use std::collections::HashMap;

use crate::{
    nir::{
        global_interner::{
            ClassId, DefId, ExprId, ImplBlockId, ItemId, ScopeId, TraitId, TypeExprId, UnresolvedId,
        },
        interner::ConstructibleId,
        nir::{
            FieldAccessKind, NirArgument, NirClassDef, NirExpr, NirExprKind, NirFunctionDef,
            NirGenericArg, NirImplBlock, NirItem, NirMethod, NirModuleDef, NirProgram,
            NirTraitConstraint, NirTraitDef, NirTypeBound,
        },
    },
    ty::{
        TcError, TcFunProto, TcParam,
        pass::Pass,
        scope::{
            Class, ClassMember, Definition, ImplBlock, ImplKind, Method, MethodKind, Module,
            ScopeKind, TemplateArgument, Trait, TypeExpr, Unresolved, UnresolvedKind,
        },
    },
};

use super::TyCtx;

pub struct SurfaceResolution {}
pub type SurfaceResolutionPassOutput<'ctx> = Vec<(ScopeId, ItemId)>;

impl<'ctx> SurfaceResolution {
    pub fn new() -> Self {
        Self {}
    }

    fn visit_method_for_trait(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        method: &NirMethod,
    ) -> Result<TcFunProto, TcError> {
        let name = method.name;
        let return_ty = ctx.visit_type(method.return_ty.as_ref().unwrap())?;
        let params = method
            .args
            .iter()
            .map(
                |NirArgument {
                     name: arg_name, ty, ..
                 }| {
                    ctx.visit_type(ty).map(|ty| TcParam {
                        name: *arg_name,
                        ty,
                    })
                },
            )
            .collect::<Result<_, _>>()?;
        Ok(TcFunProto {
            name,
            params,
            return_ty,
            variadic: false,
        })
    }

    fn check_scope(&self, ctx: &TyCtx<'ctx>, id: ScopeId) -> bool {
        let scope = ctx.ctx.interner.get_scope(id);

        scope
            .definitions
            .iter()
            .all(|(_, def)| !matches!(ctx.ctx.interner.get_def(*def), Definition::Unresolved(_)))
            && scope
                .children
                .iter()
                .all(|child| self.check_scope(ctx, *child))
    }

    fn check_scopes(&self, ctx: &TyCtx<'ctx>) -> bool {
        // Make sure we are at the topmost scope,
        // meaning we handled entering / exiting
        // scopes correctly
        assert!(ctx.current_scope.0 == 0);
        let mut scope_id = ctx.current_scope;
        let mut scope = ctx.get_last_scope();
        while let Some(parent) = scope.parent {
            scope = ctx.ctx.interner.get_scope(parent);
            scope_id = parent;
        }
        self.check_scope(ctx, scope_id)
    }

    fn visit_program(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &'ctx NirProgram,
    ) -> Result<SurfaceResolutionPassOutput<'ctx>, TcError> {
        let res = input
            .0
            .iter()
            .map(|item| self.visit_item(ctx, *item).map(|y| (y, *item)))
            .collect();

        loop {
            let to_backpatch: Vec<_> = ctx.backpatching.iter().cloned().collect();

            ctx.backpatching.clear();
            let mut worked_once = false;

            for (def, id) in to_backpatch {
                if !matches!(ctx.ctx.interner.get_def(def), Definition::Unresolved(_)) {
                    continue;
                }

                let new_def = {
                    let resolved = self.resolve_unresolved(ctx, id)?;
                    ctx.ctx.interner.get_def(resolved).clone()
                };
                if !matches!(ctx.ctx.interner.get_def(def), Definition::Unresolved(_)) {
                    worked_once = true;
                }
                *ctx.ctx.interner.get_def_mut(def) = new_def;
            }
            if !worked_once {
                break;
            }
        }

        if ctx.backpatching.len() > 0 {
            println!("\n\n");
            let mut errors = vec![];
            for (_, id) in ctx.backpatching.clone() {
                let symb = self.print_unresolved(ctx, id);
                println!("[Error]: Unresolved symbol {}", symb);
                let s = ctx.ctx.interner.insert_symbol(&symb);
                errors.push(TcError::NameNotFound(s))
            }
            return Err(TcError::Aggregate(errors));
        }

        ctx.backpatching.clear();
        ctx.ctx.interner.clear_unresolved();

        if !(self.check_scopes(ctx)) {
            panic!("Bad scopes !!!!\n");
        }

        res
    }

    fn print_unresolved(&mut self, ctx: &mut TyCtx<'ctx>, input: UnresolvedId) -> String {
        let un = ctx.ctx.interner.get_unresolved(input);
        match un.kind {
            UnresolvedKind::Symb(symbol, _) => format!("{}", ctx.ctx.interner.get_symbol(symbol)),
            UnresolvedKind::From(id, symbol) => {
                format!(
                    "{}::{}",
                    self.print_unresolved(ctx, id),
                    ctx.ctx.interner.get_symbol(symbol)
                )
            }
        }
    }

    fn resolve_unresolved(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: UnresolvedId,
    ) -> Result<DefId, TcError> {
        let Unresolved { scope, kind } = ctx.ctx.interner.get_unresolved(input).clone();
        ctx.with_scope_id(scope, |ctx| match kind {
            UnresolvedKind::Symb(symbol, span) => {
                let expr = NirExpr {
                    kind: NirExprKind::Named(symbol),
                    span: span.clone(),
                };
                let nir_id = ctx.ctx.interner.insert_expr(expr);
                self.resolve_expr(ctx, nir_id)
            }
            UnresolvedKind::From(id, symbol) => {
                let def = self.resolve_unresolved(ctx, id)?;
                match ctx.ctx.interner.get_def(def) {
                    Definition::Class(_) => todo!(),
                    Definition::Function(_) => todo!(),
                    Definition::Module(module_id) => {
                        let module = ctx.ctx.interner.get_module(*module_id);
                        Ok(ctx.get_symbol_def_in_scope(module.scope, symbol).unwrap())
                    }
                    Definition::Variable(_) => unreachable!(),
                    Definition::Trait(_) => todo!(),
                    Definition::Type(_) => todo!(),
                    Definition::Unresolved(_) => {
                        Ok(ctx.ctx.interner.insert_def(Definition::Unresolved(input)))
                    }
                }
            }
        })
    }

    fn visit_item(&mut self, ctx: &mut TyCtx<'ctx>, input: ItemId) -> Result<ScopeId, TcError> {
        let nir = ctx.ctx.interner.get_item(input).clone();
        match nir {
            NirItem::Function(x) => self.visit_function(ctx, &x, input),
            NirItem::Module(x) => self.visit_module(ctx, &x, input),
            NirItem::Class(x) => self.visit_class(ctx, &x, input),
            NirItem::Trait(x) => self.visit_trait(ctx, &x, input),
            NirItem::Impl(x) => self.visit_impl(ctx, &x, input),
            NirItem::Alias(name, ty) => {
                let def = ctx.visit_type_as_def(&ty)?;
                ctx.push_def(name, def);
                Ok(ctx.current_scope)
            }
            _ => unreachable!(),
        }
    }

    fn visit_function(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirFunctionDef,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let name = input.name;
        let return_ty = ctx.visit_type(&input.return_ty)?;
        let params = input
            .args
            .iter()
            .map(|x| ctx.visit_type(&x.ty).map(|ty| TcParam { name: x.name, ty }))
            .collect::<Result<Vec<_>, _>>()?;

        let fun_id = ctx.ctx.interner.insert_fun(TcFunProto {
            name,
            params,
            return_ty,
            variadic: input.is_variadic,
        });

        ctx.with_scope(ScopeKind::Function(fun_id, item_id), |ctx| {
            let insert_def = ctx.ctx.interner.insert_def(Definition::Function(fun_id));
            ctx.push_def(input.name, insert_def);
            Ok(ctx.current_scope)
        })
    }

    fn resolve_expr(&mut self, ctx: &mut TyCtx<'ctx>, input: ExprId) -> Result<DefId, TcError> {
        let expr = ctx.ctx.interner.get_expr(input).clone();
        match expr.kind {
            NirExprKind::Access { from, field } => {
                let from_def = self.resolve_expr(ctx, from)?;
                ctx.resolve_access(
                    from_def,
                    match field.kind {
                        FieldAccessKind::Symbol(symbol) => symbol,
                        FieldAccessKind::Index(_) => unreachable!(),
                    },
                    field.span,
                )
            }
            NirExprKind::Named(symb) => Ok(ctx.get_symbol_def(symb).unwrap_or_else(|| {
                let id = ctx.ctx.interner.insert_unresolved(Unresolved {
                    scope: ctx.current_scope,
                    kind: UnresolvedKind::Symb(symb, expr.span),
                });
                let def = ctx.ctx.interner.insert_def(Definition::Unresolved(id));
                ctx.backpatching.insert(0, (def, id));
                def
            })),
            _ => unreachable!(),
        }
    }

    fn visit_module(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirModuleDef,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let name = input.name;

        let module_id = ctx.ctx.interner.insert_module(Module {
            name,
            scope: ctx.current_scope,
        });
        let def = ctx.ctx.interner.insert_def(Definition::Module(module_id));
        ctx.push_def(name, def);
        ctx.with_scope(ScopeKind::Module(module_id, item_id), |ctx| {
            // Fixing the scope of the module
            ctx.ctx.interner.get_module_mut(module_id).scope = ctx.current_scope;
            for item in &input.items {
                self.visit_item(ctx, *item)?;
            }
            Ok(ctx.current_scope)
        })
    }

    fn get_templates(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        args: &Vec<NirGenericArg>,
    ) -> Result<Vec<TemplateArgument>, TcError> {
        let mut templates = Vec::with_capacity(args.len());
        for arg in args {
            let mut constraints = Vec::with_capacity(arg.constraints.len());
            for constraint in &arg.constraints {
                let def = ctx.resolve_path(&constraint.name);
                constraints.push(def);
            }
            templates.push(TemplateArgument {
                name: arg.name,
                constraints,
            });
        }
        Ok(templates)
    }

    fn visit_class(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirClassDef,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let c = Class {
            name: input.name,
            templates: Vec::new(),
            members: Vec::new(),
            methods: Vec::new(),
        };

        let id = ctx.ctx.interner.insert_class(c);

        let def = ctx.ctx.interner.insert_def(Definition::Class(id));
        ctx.push_def(input.name, def);

        ctx.with_scope(ScopeKind::Class(id, item_id), |ctx| {
            let templates = self.get_templates(ctx, &input.generic_args)?;
            Self::add_templates_to_scope(ctx, &templates);
            self.add_templates_to_class(ctx, id, templates)?;
            self.add_members_to_class(ctx, id, input)?;
            self.add_methods_to_class(ctx, id, input)?;
            Ok(ctx.current_scope)
        })
    }

    fn add_templates_to_class(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        id: ClassId,
        templates: Vec<TemplateArgument>,
    ) -> Result<(), TcError> {
        let cmut = ctx.ctx.interner.get_class_mut(id);
        cmut.templates = templates;
        Ok(())
    }

    fn add_templates_to_scope(ctx: &mut TyCtx<'ctx>, templates: &Vec<TemplateArgument>) {
        for (i, TemplateArgument { name, .. }) in templates.iter().enumerate() {
            let te = ctx.ctx.interner.insert_type_expr(TypeExpr::Template(i));
            let def = ctx.ctx.interner.insert_def(Definition::Type(te));
            ctx.push_def(*name, def);
        }
    }

    fn add_methods_to_class(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        id: ClassId,
        input: &NirClassDef,
    ) -> Result<(), TcError> {
        let mut methods = Vec::with_capacity(input.methods.len());
        for method in &input.methods {
            let meth = match ctx.ctx.interner.get_item(*method) {
                NirItem::Method(nir_method) => nir_method,
                _ => unreachable!(),
            }
            .clone();
            methods.push(self.visit_method(ctx, &meth)?);
        }
        let cmut = ctx.ctx.interner.get_class_mut(id);
        cmut.methods = methods;
        Ok(())
    }

    fn add_members_to_class(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        id: ClassId,
        input: &NirClassDef,
    ) -> Result<(), TcError> {
        let mut members = Vec::with_capacity(input.members.len());
        for member in &input.members {
            members.push(ClassMember {
                name: member.name,
                ty: ctx.visit_type(&member.ty)?,
            });
        }
        let cmut = ctx.ctx.interner.get_class_mut(id);
        cmut.members = members;
        Ok(())
    }

    fn get_template_type_expr(ctx: &mut TyCtx<'ctx>, index: usize) -> TypeExprId {
        ctx.ctx.interner.insert_type_expr(TypeExpr::Template(index))
    }

    fn visit_trait(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirTraitDef,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let for_ty = TemplateArgument {
            name: input.ty.name,
            constraints: self.get_constraints(ctx, &input.ty.constraints)?,
        };
        let tr = Trait {
            name: input.name,
            for_ty,
            methods: Vec::new(),
            types: Vec::new(),
        };
        let id = ctx.ctx.interner.insert_tr(tr);
        let def = ctx.ctx.interner.insert_def(Definition::Trait(id));
        ctx.push_def(input.name, def);

        ctx.with_scope(ScopeKind::Trait(id, item_id), |ctx| {
            let type_id = Self::get_template_type_expr(ctx, 0);
            let def = ctx.ctx.interner.insert_def(Definition::Type(type_id));
            ctx.push_def(input.ty.name, def);
            self.add_methods_to_trait(ctx, id, input)?;
            Self::add_types_to_trait(ctx, input);
            Ok(ctx.current_scope)
        })
    }

    fn get_constraints(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &Vec<NirTraitConstraint>,
    ) -> Result<Vec<DefId>, TcError> {
        let constraints = {
            let mut constraints = Vec::with_capacity(input.len());
            for constraint in input {
                let def = ctx.resolve_path(&constraint.name);
                constraints.push(def);
            }
            constraints
        };
        Ok(constraints)
    }

    fn add_types_to_trait(ctx: &mut TyCtx<'ctx>, input: &NirTraitDef) {
        for (i, ty) in input.types.iter().enumerate() {
            let type_id = ctx.ctx.interner.insert_type_expr(TypeExpr::Associated(i));
            let def = ctx.ctx.interner.insert_def(Definition::Type(type_id));
            ctx.push_def(ty.name, def);
        }
    }

    fn add_methods_to_trait(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        id: TraitId,
        input: &NirTraitDef,
    ) -> Result<(), TcError> {
        Ok(for method_id in &input.methods {
            let method = match ctx.ctx.interner.get_item(*method_id) {
                NirItem::Method(nir_method) => nir_method,
                _ => unreachable!(),
            }
            .clone();
            let proto = self.visit_method_for_trait(ctx, &method)?;
            ctx.ctx.interner.get_tr_mut(id).methods.push(proto);
        })
    }

    fn visit_impl(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirImplBlock,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let templates = self.get_templates(ctx, &input.generic_args)?;

        let dummy_id = ImplBlockId::new(0);

        ctx.with_scope(ScopeKind::Impl(dummy_id, item_id), |ctx| {
            for (i, t) in templates.iter().enumerate() {
                let type_id = ctx.ctx.interner.insert_type_expr(TypeExpr::Template(i));
                let def = ctx.ctx.interner.insert_def(Definition::Type(type_id));
                ctx.push_def(t.name, def);
            }

            let for_ty = ctx.visit_type(&input.ty)?;

            let impl_block = ImplBlock {
                for_ty,
                templates,
                methods: vec![],
                kind: match &input.implements {
                    Some(constraint) => ImplKind::WithTrait {
                        impl_trait: ctx.resolve_path(&constraint.name),
                        types: HashMap::new(),
                    },
                    None => ImplKind::NoTrait,
                },
            };
            let actual_id = ctx.ctx.interner.insert_imp(impl_block);
            ctx.get_last_scope_mut().kind = ScopeKind::Impl(actual_id, item_id);

            self.add_types_to_impl(ctx, actual_id, &input.types)?;
            self.add_methods_to_impl(ctx, actual_id, &input.methods)?;

            Ok(ctx.current_scope)
        })
    }

    fn add_methods_to_impl(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        id: ImplBlockId,
        input: &Vec<ItemId>,
    ) -> Result<(), TcError> {
        for method_id in input {
            let method = match ctx.ctx.interner.get_item(*method_id) {
                NirItem::Method(nir_method) => nir_method,
                _ => unreachable!(),
            }
            .clone();
            let method = self.visit_method(ctx, &method)?;
            ctx.ctx.interner.get_imp_mut(id).methods.push(method);
        }
        Ok(())
    }

    fn add_types_to_impl(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        id: ImplBlockId,
        input: &Vec<NirTypeBound>,
    ) -> Result<(), TcError> {
        Ok(for ty in input {
            let name = ty.name;
            let rhs = ctx.visit_type(&ty.ty)?;
            match &mut ctx.ctx.interner.get_imp_mut(id).kind {
                ImplKind::WithTrait { types, .. } => {
                    types.insert(name, rhs);
                }
                _ => unreachable!(),
            }
            let def = ctx.ctx.interner.insert_def(Definition::Type(rhs));
            ctx.push_def(name, def);
        })
    }

    fn visit_method(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirMethod,
    ) -> Result<Method, TcError> {
        let name = input.name;

        let current_class_res = match ctx.get_last_scope().kind {
            ScopeKind::Class(id, _) => Ok(ctx.ctx.interner.get_class(id)),
            ScopeKind::Impl(id, _) => Err(id),
            ref kind => unreachable!("{:?}", kind),
        };

        let kind = if let Ok(current_class) = current_class_res
            && current_class.name == input.name
        {
            if input.return_ty.is_some() {
                todo!("Report error: No return type for constructor.");
            }
            MethodKind::Constructor
        } else {
            if input.return_ty.is_none() {
                todo!("Report error: Return type needed for non-constructor methods.");
            }
            MethodKind::Method {
                return_type: ctx.visit_type(input.return_ty.as_ref().unwrap())?,
            }
        };

        assert!(input.generic_args.len() == 0);

        let args = input
            .args
            .iter()
            .map(
                |NirArgument {
                     name: arg_name, ty, ..
                 }| {
                    ctx.visit_type(ty).map(|ty| TcParam {
                        name: *arg_name,
                        ty,
                    })
                },
            )
            .collect::<Result<_, _>>()?;
        Ok(Method { name, kind, args })
    }
}

impl<'ctx> Pass<'ctx, &'ctx NirProgram> for SurfaceResolution {
    type Output = SurfaceResolutionPassOutput<'ctx>;

    fn run(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &'ctx NirProgram,
    ) -> Result<Self::Output, TcError> {
        self.visit_program(ctx, input)
    }
}
