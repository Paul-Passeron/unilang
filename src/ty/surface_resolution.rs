use std::{collections::HashMap, rc::Rc};

use crate::{
    common::source_location::Span,
    nir::{
        interner::{
            ConstructibleId, ExprId, ImplBlockId, Interner, ItemId, ScopeId, Symbol, TypeExprId,
            UnresolvedId,
        },
        nir::{
            FieldAccessKind, NirArgument, NirClassDef, NirExpr, NirExprKind, NirFunctionDef,
            NirImplBlock, NirItem, NirMethod, NirModuleDef, NirProgram, NirTraitDef, NirType,
            NirTypeKind,
        },
    },
    ty::{
        TcError, TcFunProto, TcParam,
        pass::Pass,
        scope::{
            Class, ClassMember, Definition, ImplBlock, ImplKind, Method, MethodKind, Module, Scope,
            ScopeKind, TemplateArgument, Trait, TypeExpr, Unresolved, UnresolvedKind,
        },
    },
};

use super::TyCtx;

pub struct SurfaceResolution {
    backpatching: Vec<(Rc<Definition>, UnresolvedId)>,
}
pub type SurfaceResolutionPassOutput<'ctx> = Vec<(ScopeId, ItemId)>;

impl<'ctx> SurfaceResolution {
    pub fn new() -> Self {
        Self {
            backpatching: Vec::new(),
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
        let scope = ctx.ctx.interner.scope_interner.get(id);
        for (_, def) in &scope.definitions {
            match def.as_ref() {
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
        let mut scope_id = ctx.current_scope;
        let mut scope = ctx.get_last_scope();
        while let Some(parent) = scope.parent {
            scope = ctx.ctx.interner.scope_interner.get(parent);
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
            let to_backpatch: Vec<_> = self
                .backpatching
                .iter()
                .filter(|(d, _)| matches!(d.as_ref(), Definition::Unresolved(_)))
                .cloned()
                .collect();
            self.backpatching.clear();
            let mut worked_once = false;

            for (mut def, id) in to_backpatch {
                if !matches!(def.as_ref(), Definition::Unresolved(_)) {
                    continue;
                }

                let new_def = self.resolve_unresolved(ctx, id)?.as_ref().clone();
                if !matches!(def.as_ref(), Definition::Unresolved(_)) {
                    worked_once = true;
                }

                // Because The Rc<Definition> is not unique
                unsafe {
                    *Rc::get_mut_unchecked(&mut def) = new_def;
                }
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
        }

        if !(self.check_scopes(ctx)) {
            panic!("Bad scopes !!!!\n");
        }

        res
    }

    fn print_unresolved(&mut self, ctx: &mut TyCtx<'ctx>, input: UnresolvedId) -> String {
        let un = ctx.ctx.interner.unresolved_interner.get(input);
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
    ) -> Result<Rc<Definition>, TcError> {
        let old_scope = ctx.current_scope;
        let Unresolved { scope, kind } = ctx.ctx.interner.unresolved_interner.get(input).clone();
        ctx.current_scope = scope;
        let res = match kind {
            UnresolvedKind::Symb(symbol, span) => {
                let expr = NirExpr {
                    kind: NirExprKind::Named(symbol),
                    span: span.clone(),
                };
                let nir_id = ctx.ctx.interner.expr_interner.insert(expr);
                self.resolve_expr(ctx, nir_id)
            }
            UnresolvedKind::From(id, symbol) => {
                let def = self.resolve_unresolved(ctx, id)?;
                match def.as_ref() {
                    Definition::Class(_) => todo!(),
                    Definition::Function(_) => todo!(),
                    Definition::Module(module_id) => {
                        let module = ctx.ctx.interner.module_interner.get(*module_id);
                        Ok(ctx
                            .ctx
                            .interner
                            .scope_interner
                            .get(module.scope)
                            .get_definition_for_symbol(symbol, &ctx.ctx.interner.scope_interner)
                            .unwrap())
                    }
                    Definition::Variable(_) => unreachable!(),
                    Definition::Trait(_) => todo!(),
                    Definition::Type(_) => todo!(),
                    Definition::Unresolved(_) => panic!(),
                }
            }
        };

        ctx.current_scope = old_scope;
        res
    }

    fn visit_item(&mut self, ctx: &mut TyCtx<'ctx>, input: ItemId) -> Result<ScopeId, TcError> {
        let nir = ctx.ctx.interner.item_interner.get(input).clone();
        match nir {
            NirItem::Function(x) => self.visit_function(ctx, &x, input),
            NirItem::Module(x) => self.visit_module(ctx, &x, input),
            NirItem::Class(x) => self.visit_class(ctx, &x, input),
            NirItem::Trait(x) => self.visit_trait(ctx, &x, input),
            NirItem::Impl(x) => self.visit_impl(ctx, &x, input),
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
        let return_ty = self.visit_type(ctx, &input.return_ty)?;
        let params = input
            .args
            .iter()
            .map(|x| {
                self.visit_type(ctx, &x.ty)
                    .map(|ty| TcParam { name: x.name, ty })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let proto = TcFunProto {
            name,
            params,
            return_ty,
            variadic: input.is_variadic,
        };

        let fun_id = ctx.ctx.interner.fun_interner.insert(proto);

        let def = Rc::new(Definition::Function(fun_id));

        let scope = Scope {
            kind: ScopeKind::Function(fun_id, item_id),
            parent: Some(ctx.current_scope),
            children: vec![],
            definitions: vec![(input.name, def)],
        };

        let scope_id = ctx.ctx.interner.scope_interner.insert(scope);

        ctx.get_last_scope_mut().children.push(scope_id);

        Ok(scope_id)
    }

    fn resolve_access(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        from_def: Rc<Definition>,
        index: Symbol,
        span: Span,
    ) -> Result<Rc<Definition>, TcError> {
        match from_def.as_ref() {
            Definition::Class(_) => todo!(),
            Definition::Function(_) => todo!(),
            Definition::Module(module_id) => {
                let module = ctx.ctx.interner.module_interner.get(*module_id);
                println!(
                    "Looking for {} in module {}",
                    ctx.ctx.interner.get_symbol(index),
                    ctx.ctx.interner.get_symbol(module.name)
                );
                Ok(ctx
                    .ctx
                    .interner
                    .scope_interner
                    .get(module.scope)
                    .get_definition_for_symbol(index, &ctx.ctx.interner.scope_interner)
                    .unwrap_or_else(|| {
                        Rc::new(Definition::Unresolved(
                            ctx.ctx.interner.unresolved_interner.insert(Unresolved {
                                scope: module.scope,
                                kind: UnresolvedKind::Symb(index, span),
                            }),
                        ))
                    }))
            }
            Definition::Variable(_) => todo!(),
            Definition::Trait(_) => todo!(),
            Definition::Type(_) => todo!(),
            Definition::Unresolved(u_id) => {
                let un = Unresolved {
                    scope: ctx.current_scope,
                    kind: UnresolvedKind::From(*u_id, index),
                };
                let id = ctx.ctx.interner.unresolved_interner.insert(un);
                let def = Rc::new(Definition::Unresolved(id));
                self.backpatching.insert(0, (def.clone(), id));
                Ok(def)
            }
        }
    }

    fn resolve_expr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: ExprId,
    ) -> Result<Rc<Definition>, TcError> {
        let expr = ctx.ctx.interner.expr_interner.get(input).clone();
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
            NirExprKind::Named(symb) => Ok(ctx
                .get_last_scope()
                .get_definition_for_symbol(symb, &ctx.ctx.interner.scope_interner)
                .unwrap_or_else(|| {
                    println!("Unresolved {}", ctx.ctx.interner.get_symbol(symb));
                    let id = ctx.ctx.interner.unresolved_interner.insert(Unresolved {
                        scope: ctx.current_scope,
                        kind: UnresolvedKind::Symb(symb, expr.span),
                    });
                    let def = Rc::new(Definition::Unresolved(id));
                    self.backpatching.insert(0, (def.clone(), id));
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
                .map(|x| ctx.ctx.interner.type_expr_interner.insert(TypeExpr::Ptr(x))),
            NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
                let def = self.resolve_expr(ctx, *name)?;

                match def.as_ref() {
                    Definition::Class(_) => {
                        Ok(ctx
                            .ctx
                            .interner
                            .type_expr_interner
                            .insert(TypeExpr::Instantiation {
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
                        Ok(ctx.ctx.interner.type_expr_interner.insert(ty))
                    }
                    _ => todo!("{def:?}"),
                }
            }
            NirTypeKind::Named { name, generic_args } => {
                let args = generic_args
                    .iter()
                    .map(|x| self.visit_type(ctx, x))
                    .collect::<Result<_, _>>()?;
                let def = self.resolve_expr(ctx, *name)?;

                Ok(ctx
                    .ctx
                    .interner
                    .type_expr_interner
                    .insert(TypeExpr::Instantiation {
                        template: def,
                        args,
                    }))
            }
            NirTypeKind::Tuple(nir_types) => {
                let tys = nir_types
                    .iter()
                    .map(|x| self.visit_type(ctx, x))
                    .collect::<Result<_, _>>()?;
                Ok(ctx
                    .ctx
                    .interner
                    .type_expr_interner
                    .insert(TypeExpr::Tuple(tys)))
            }
        }
    }

    fn visit_module(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirModuleDef,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let name = input.name;
        println!("Visiting Module {}", ctx.ctx.interner.get_symbol(name));
        let module_id = ctx.ctx.interner.module_interner.insert(Module {
            name,
            scope: ctx.current_scope,
        });

        let scope = Scope {
            kind: ScopeKind::Module(module_id, item_id),
            parent: Some(ctx.current_scope),
            children: vec![],
            definitions: vec![],
        };

        let parent_id = ctx.current_scope;

        let scope_id = ctx.ctx.interner.scope_interner.insert(scope);

        ctx.ctx.interner.module_interner.get_mut(module_id).scope = scope_id;

        let parent_scope = ctx.get_last_scope_mut();
        parent_scope.children.push(scope_id);
        parent_scope
            .definitions
            .push((name, Rc::new(Definition::Module(module_id))));
        ctx.current_scope = scope_id;
        println!("ctx.current_scope = {:?}", ctx.current_scope);

        for item in &input.items {
            self.visit_item(ctx, *item)?;
        }

        ctx.current_scope = parent_id;
        println!("ctx.current_scope = {:?}", ctx.current_scope);

        Ok(scope_id)
    }

    fn visit_class(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirClassDef,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        println!("Visiting Class {}", ctx.ctx.interner.get_symbol(input.name));

        let templates = {
            let mut templates = Vec::with_capacity(input.generic_args.len());
            for arg in &input.generic_args {
                let mut constraints = Vec::with_capacity(arg.constraints.len());
                for constraint in &arg.constraints {
                    let def = self.resolve_expr(ctx, constraint.name)?;
                    constraints.push(def);
                }
                templates.push(TemplateArgument {
                    name: arg.name,
                    constraints,
                });
            }
            templates
        };
        let c = Class {
            name: input.name,
            templates: templates.clone(),
            members: Vec::new(),
            methods: Vec::new(),
        };

        let id = ctx.ctx.interner.class_interner.insert(c);
        let parent_scope = ctx.current_scope;

        let new_scope = Scope {
            kind: ScopeKind::Class(id, item_id),
            parent: Some(ctx.current_scope),
            children: Vec::new(),
            definitions: Vec::new(),
        };
        let new_scope_id = ctx.ctx.interner.scope_interner.insert(new_scope);

        let last_scope = ctx.get_last_scope_mut();
        last_scope.children.push(new_scope_id);
        last_scope
            .definitions
            .push((input.name, Rc::new(Definition::Class(id))));
        ctx.current_scope = new_scope_id;
        println!("ctx.current_scope = {:?}", ctx.current_scope);

        for (i, TemplateArgument { name, .. }) in templates.iter().enumerate() {
            let res = (
                *name,
                Rc::new(Definition::Type(
                    ctx.ctx
                        .interner
                        .type_expr_interner
                        .insert(TypeExpr::Template(i)),
                )),
            );
            let current_scope = ctx.get_last_scope_mut();
            current_scope.definitions.push(res);
        }

        let mut members = Vec::with_capacity(input.members.len());

        for member in &input.members {
            members.push(ClassMember {
                name: member.name,
                ty: self.visit_type(ctx, &member.ty)?,
            });
        }

        let cmut = ctx.ctx.interner.class_interner.get_mut(id);
        cmut.members = members;

        let mut methods = Vec::with_capacity(input.methods.len());
        for method in &input.methods {
            let meth = match ctx.ctx.interner.item_interner.get(*method) {
                NirItem::Method(nir_method) => nir_method,
                _ => unreachable!(),
            }
            .clone();
            methods.push(self.visit_method(ctx, &meth)?);
        }

        ctx.current_scope = parent_scope;
        println!("ctx.current_scope = {:?}", ctx.current_scope);

        Ok(new_scope_id)
    }

    fn visit_trait(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirTraitDef,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let mut constraints = Vec::with_capacity(input.ty.constraints.len());
        for constraint in &input.ty.constraints {
            let def = self.resolve_expr(ctx, constraint.name)?;
            constraints.push(def);
        }
        let for_ty = TemplateArgument {
            name: input.ty.name,
            constraints,
        };
        let type_id = ctx
            .ctx
            .interner
            .type_expr_interner
            .insert(TypeExpr::Template(0));
        let ty_name = input.ty.name;
        let tr = Trait {
            name: input.name,
            for_ty,
            methods: vec![],
            types: vec![],
        };
        let id = ctx.ctx.interner.trait_interner.insert(tr);
        let def = Rc::new(Definition::Trait(id));
        ctx.get_last_scope_mut().definitions.push((input.name, def));

        let scope = Scope {
            kind: ScopeKind::Trait(id, item_id),
            parent: Some(ctx.current_scope),
            children: vec![],
            definitions: vec![(ty_name, Rc::new(Definition::Type(type_id)))],
        };

        let scope_id = ctx.ctx.interner.scope_interner.insert(scope);
        ctx.get_last_scope_mut().children.push(scope_id);

        let parent_id = ctx.current_scope;
        ctx.current_scope = scope_id;

        for method_id in &input.methods {
            let method = match ctx.ctx.interner.item_interner.get(*method_id) {
                NirItem::Method(nir_method) => nir_method,
                _ => unreachable!(),
            }
            .clone();
            let proto = self.visit_method_for_trait(ctx, &method)?;
            ctx.ctx
                .interner
                .trait_interner
                .get_mut(id)
                .methods
                .push(proto);
        }

        for (i, ty) in input.types.iter().enumerate() {
            let type_id = ctx
                .ctx
                .interner
                .type_expr_interner
                .insert(TypeExpr::Associated(i));
            ctx.get_last_scope_mut()
                .definitions
                .push((ty.name, Rc::new(Definition::Type(type_id))))
        }

        ctx.current_scope = parent_id;
        Ok(scope_id)
    }

    fn visit_impl(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirImplBlock,
        item_id: ItemId,
    ) -> Result<ScopeId, TcError> {
        let templates = {
            let mut templates = Vec::with_capacity(input.generic_args.len());
            for arg in &input.generic_args {
                let mut constraints = Vec::with_capacity(arg.constraints.len());
                for constraint in &arg.constraints {
                    let def = self.resolve_expr(ctx, constraint.name)?;
                    constraints.push(def);
                }
                templates.push(TemplateArgument {
                    name: arg.name,
                    constraints,
                });
            }
            templates
        };

        let dummy_id = ImplBlockId::new(0);
        // let id = ctx.ctx.interner.impl_interner.insert(impl_block);

        let scope = Scope {
            kind: ScopeKind::Impl(dummy_id, item_id),
            parent: Some(ctx.current_scope),
            children: vec![],
            definitions: vec![],
        };

        let scope_id = ctx.ctx.interner.scope_interner.insert(scope);
        ctx.get_last_scope_mut().children.push(scope_id);

        let parent_id = ctx.current_scope;
        ctx.current_scope = scope_id;

        for (i, t) in templates.iter().enumerate() {
            let type_id = ctx
                .ctx
                .interner
                .type_expr_interner
                .insert(TypeExpr::Template(i));

            ctx.get_last_scope_mut()
                .definitions
                .push((t.name, Rc::new(Definition::Type(type_id))));
        }

        let for_ty = self.visit_type(ctx, &input.ty)?;

        let impl_block = ImplBlock {
            for_ty,
            templates,
            methods: vec![],
            kind: match &input.implements {
                Some(constraint) => ImplKind::WithTrait {
                    impl_trait: self.resolve_expr(ctx, constraint.name)?,
                    types: HashMap::new(),
                },
                None => ImplKind::NoTrait,
            },
        };

        let actual_id = ctx.ctx.interner.impl_interner.insert(impl_block);
        ctx.get_last_scope_mut().kind = ScopeKind::Impl(actual_id, item_id);

        for ty in &input.types {
            let name = ty.name;
            let rhs = self.visit_type(ctx, &ty.ty)?;
            match &mut ctx.ctx.interner.impl_interner.get_mut(actual_id).kind {
                ImplKind::WithTrait { types, .. } => {
                    types.insert(name, rhs);
                }
                _ => unreachable!(),
            }

            ctx.get_last_scope_mut()
                .definitions
                .push((name, Rc::new(Definition::Type(rhs))));
        }

        for method_id in &input.methods {
            let method = match ctx.ctx.interner.item_interner.get(*method_id) {
                NirItem::Method(nir_method) => nir_method,
                _ => unreachable!(),
            }
            .clone();
            let method = self.visit_method(ctx, &method)?;
            ctx.ctx
                .interner
                .impl_interner
                .get_mut(actual_id)
                .methods
                .push(method);
        }

        ctx.current_scope = parent_id;
        Ok(scope_id)
    }

    fn visit_method(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirMethod,
    ) -> Result<Method, TcError> {
        let name = input.name;

        let current_class_res = match ctx.get_last_scope().kind {
            ScopeKind::Class(id, _) => Ok(ctx.ctx.interner.class_interner.get(id)),
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
