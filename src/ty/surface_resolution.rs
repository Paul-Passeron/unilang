use std::collections::HashMap;

use crate::{
    common::source_location::Span,
    nir::{
        interner::{
            ClassId, ConstructibleId, DefId, ExprId, ImplBlockId, Interner, ItemId, ScopeId,
            Symbol, TraitId, TyId, TypeExprId, UnresolvedId, UnresolvedInterner,
        },
        nir::{
            FieldAccessKind, NirArgument, NirClassDef, NirExpr, NirExprKind, NirFunctionDef,
            NirGenericArg, NirImplBlock, NirItem, NirMethod, NirModuleDef, NirPath, NirProgram,
            NirTraitConstraint, NirTraitDef, NirType, NirTypeBound, NirTypeKind,
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

pub struct SurfaceResolution {
    backpatching: Vec<(DefId, UnresolvedId)>,
    unresolved_interner: UnresolvedInterner,
}
pub type SurfaceResolutionPassOutput<'ctx> = Vec<(ScopeId, ItemId)>;

impl<'ctx> SurfaceResolution {
    pub fn new() -> Self {
        Self {
            backpatching: Vec::new(),
            unresolved_interner: UnresolvedInterner::new(),
        }
    }

    fn visit_method_for_trait(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        method: &NirMethod,
    ) -> Result<TcFunProto, TcError> {
        let name = method.name;
        let return_ty = self.visit_type(ctx, method.return_ty.as_ref().unwrap())?;
        let params = method
            .args
            .iter()
            .map(
                |NirArgument {
                     name: arg_name, ty, ..
                 }| {
                    self.visit_type(ctx, ty).map(|ty| TcParam {
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
        for (_, def) in &scope.definitions {
            match ctx.ctx.interner.get_def(*def) {
                Definition::Unresolved(_) => return false,
                _ => (),
            }
        }

        for child in &scope.children {
            if !self.check_scope(ctx, *child) {
                return false;
            }
        }

        true
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
            let to_backpatch: Vec<_> = self.backpatching.iter().cloned().collect();

            self.backpatching.clear();
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

        if self.backpatching.len() > 0 {
            println!("\n\n");
            let mut errors = vec![];
            for (_, id) in self.backpatching.clone() {
                let symb = self.print_unresolved(ctx, id);
                println!("[Error]: Unresolved symbol {}", symb);
                let s = ctx.ctx.interner.insert_symbol(&symb);
                errors.push(TcError::NameNotFound(s))
            }
            return Err(TcError::Aggregate(errors));
        }

        if !(self.check_scopes(ctx)) {
            panic!("Bad scopes !!!!\n");
        }

        res
    }

    fn print_unresolved(&mut self, ctx: &mut TyCtx<'ctx>, input: UnresolvedId) -> String {
        let un = self.unresolved_interner.get(input);
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
        let Unresolved { scope, kind } = self.unresolved_interner.get(input).clone();
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
                    Definition::Unresolved(_) => panic!(),
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
                let ty = self.visit_type(ctx, &ty)?;
                let def = ctx.ctx.interner.insert_def(Definition::Type(ty));
                ctx.push_def(name, def);
                Ok(ctx.current_scope)
            }
            _ => unreachable!(),
        }
    }

    fn ty_id_to_string(&self, _ctx: &TyCtx<'ctx>, ty: TyId) -> String {
        format!("{:?}", ty)
    }

    fn def_to_string(&self, ctx: &TyCtx<'ctx>, def: DefId) -> String {
        match ctx.ctx.interner.get_def(def) {
            Definition::Class(id) => {
                let cdef = ctx.ctx.interner.get_class(*id);
                format!(
                    "{}{}",
                    ctx.ctx.interner.get_symbol(cdef.name),
                    if cdef.templates.len() > 0 {
                        "<".to_string()
                            + (cdef
                                .templates
                                .iter()
                                .map(|x| ctx.ctx.interner.get_symbol(x.name).clone())
                                .collect::<Vec<_>>()
                                .join(", "))
                            .as_str()
                            + ">"
                    } else {
                        String::new()
                    }
                )
            }
            Definition::Function(_) => todo!(),
            Definition::Module(id) => format!("(Module {})", {
                let mdef = ctx.ctx.interner.get_module(*id);
                ctx.ctx.interner.get_symbol(mdef.name)
            }),
            Definition::Variable(_) => todo!(),
            Definition::Trait(id) => format!("(Trait {})", {
                let tdef = ctx.ctx.interner.get_tr(*id);
                ctx.ctx.interner.get_symbol(tdef.name)
            }),

            Definition::Type(id) => self.tyexpr_to_string(ctx, *id),
            Definition::Unresolved(id) => format!("Unresolved({})", id.0),
        }
    }

    fn tyexpr_to_string(&self, ctx: &TyCtx<'ctx>, ty: TypeExprId) -> String {
        let ty_expr = ctx.ctx.interner.get_type_expr(ty);
        match ty_expr {
            TypeExpr::Template(x) => format!("Template({})", x),
            TypeExpr::Associated(x) => format!("Associated({})", x),
            TypeExpr::Instantiation { template, args } => {
                format!(
                    "{}<{}>",
                    self.def_to_string(ctx, *template),
                    args.iter()
                        .map(|x| self.tyexpr_to_string(ctx, *x))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            TypeExpr::Ptr(_) => todo!(),
            TypeExpr::Tuple(_) => todo!(),
            TypeExpr::Primitive(primitive_ty) => primitive_ty.get_name().to_string(),
        }
    }

    fn visit_function(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirFunctionDef,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let name = input.name;
        let return_ty = self.visit_type(ctx, &input.return_ty)?;
        let params = input
            .args
            .iter()
            .map(|x| {
                self.visit_type(ctx, &x.ty)
                    .map(|ty| TcParam { name: x.name, ty })
            })
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

    fn resolve_access(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        from_def: DefId,
        index: Symbol,
        span: Span,
    ) -> Result<DefId, TcError> {
        match ctx.ctx.interner.get_def(from_def) {
            Definition::Class(_) => todo!(),
            Definition::Function(_) => todo!(),
            Definition::Module(module_id) => {
                let module = ctx.ctx.interner.get_module(*module_id);
                let def_opt = ctx.get_symbol_def_in_scope(module.scope, index);
                if def_opt.is_some() {
                    return Ok(def_opt.unwrap());
                }

                let id = self.unresolved_interner.insert(Unresolved {
                    scope: module.scope,
                    kind: UnresolvedKind::Symb(index, span),
                });

                let def = ctx.ctx.interner.insert_def(Definition::Unresolved(id));
                self.backpatching.insert(0, (def, id));
                Ok(def)
            }
            Definition::Variable(_) => todo!(),
            Definition::Trait(_) => todo!(),
            Definition::Type(_) => todo!(),
            Definition::Unresolved(u_id) => {
                println!("Here !\n");

                let un = Unresolved {
                    scope: ctx.current_scope,
                    kind: UnresolvedKind::From(*u_id, index),
                };
                let id = self.unresolved_interner.insert(un);
                let def = ctx.ctx.interner.insert_def(Definition::Unresolved(id));
                self.backpatching.insert(0, (def, id));
                Ok(def)
            }
        }
    }

    fn resolve_expr(&mut self, ctx: &mut TyCtx<'ctx>, input: ExprId) -> Result<DefId, TcError> {
        let expr = ctx.ctx.interner.get_expr(input).clone();
        match expr.kind {
            NirExprKind::Access { from, field } => {
                let from_def = self.resolve_expr(ctx, from)?;
                self.resolve_access(
                    ctx,
                    from_def,
                    match field.kind {
                        FieldAccessKind::Symbol(symbol) => symbol,
                        FieldAccessKind::Index(_) => unreachable!(),
                    },
                    field.span,
                )
            }
            NirExprKind::Named(symb) => Ok(ctx.get_symbol_def(symb).unwrap_or_else(|| {
                let id = self.unresolved_interner.insert(Unresolved {
                    scope: ctx.current_scope,
                    kind: UnresolvedKind::Symb(symb, expr.span),
                });
                let def = ctx.ctx.interner.insert_def(Definition::Unresolved(id));
                self.backpatching.insert(0, (def, id));
                def
            })),
            _ => unreachable!(),
        }
    }

    fn visit_type(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirType,
    ) -> Result<TypeExprId, TcError> {
        match &input.kind {
            NirTypeKind::Ptr(nir_type) => self
                .visit_type(ctx, nir_type)
                .map(|x| ctx.ctx.interner.insert_type_expr(TypeExpr::Ptr(x))),
            NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
                let def = self.resolve_path(ctx, name);
                match ctx.ctx.interner.get_def(def) {
                    Definition::Class(_) => {
                        Ok(ctx.ctx.interner.insert_type_expr(TypeExpr::Instantiation {
                            template: def,
                            args: vec![],
                        }))
                    }
                    Definition::Type(x) => Ok(*x),
                    Definition::Unresolved(_) => {
                        let ty = TypeExpr::Instantiation {
                            template: def,
                            args: vec![],
                        };
                        Ok(ctx.ctx.interner.insert_type_expr(ty))
                    }
                    _ => todo!("{def:?}"),
                }
            }
            NirTypeKind::Named { name, generic_args } => {
                let args = generic_args
                    .iter()
                    .map(|x| self.visit_type(ctx, x))
                    .collect::<Result<_, _>>()?;
                let def = self.resolve_path(ctx, name);

                Ok(ctx.ctx.interner.insert_type_expr(TypeExpr::Instantiation {
                    template: def,
                    args,
                }))
            }
            NirTypeKind::Tuple(nir_types) => {
                let tys = nir_types
                    .iter()
                    .map(|x| self.visit_type(ctx, x))
                    .collect::<Result<_, _>>()?;
                Ok(ctx.ctx.interner.insert_type_expr(TypeExpr::Tuple(tys)))
            }
        }
    }

    fn resolve_path(&mut self, ctx: &mut TyCtx<'ctx>, name: &NirPath) -> DefId {
        let def = {
            name.path.iter().fold(None, |acc, (x, span)| match acc {
                Some(def) => Some(self.resolve_access(ctx, def, *x, *span).unwrap()),
                None => ctx.get_symbol_def(*x).or_else(|| {
                    let insert = self.unresolved_interner.insert(Unresolved {
                        scope: ctx.current_scope,
                        kind: UnresolvedKind::Symb(*x, *span),
                    });
                    let def = ctx.ctx.interner.insert_def(Definition::Unresolved(insert));
                    self.backpatching.insert(0, (def, insert));
                    Some(def)
                }),
            })
        }
        .unwrap();
        def
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
                let def = self.resolve_path(ctx, &constraint.name);
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
                ty: self.visit_type(ctx, &member.ty)?,
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
                let def = self.resolve_path(ctx, &constraint.name);
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

            let for_ty = self.visit_type(ctx, &input.ty)?;

            let impl_block = ImplBlock {
                for_ty,
                templates,
                methods: vec![],
                kind: match &input.implements {
                    Some(constraint) => ImplKind::WithTrait {
                        impl_trait: self.resolve_path(ctx, &constraint.name),
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
            let rhs = self.visit_type(ctx, &ty.ty)?;
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
                return_type: self.visit_type(ctx, input.return_ty.as_ref().unwrap())?,
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
                    self.visit_type(ctx, ty).map(|ty| TcParam {
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
