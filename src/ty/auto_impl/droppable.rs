use crate::{
    common::global_interner::{FunId, ScopeId, TraitId, TyId},
    nir::{
        interner::ConstructibleId,
        nir::{FieldAccessKind, NirItem},
    },
    ty::{
        TcError, TcFunProto, TcParam, TyCtx,
        auto_impl::no_drop::NoDropImpler,
        displays::Displayable,
        scope::{Definition, ScopeKind, TypeExpr},
        tir::{ConcreteType, SCField, Signature, TirCtx, TirExpr},
        type_checker::TypeChecker,
    },
};

#[derive(Clone)]
pub struct DroppableImpler {
    droppable: TraitId,
    ty: TyId,
    fun_id: Option<FunId>,
}

impl DroppableImpler {
    pub fn droppable_trait(ctx: &mut TyCtx) -> Option<TraitId> {
        let trait_symbol = ctx.ctx.interner.insert_symbol(&"Droppable".to_string());
        let def = ctx.get_symbol_def_in_scope(ScopeId::new(0), trait_symbol)?;
        match def.get_def(ctx) {
            Definition::Trait(id) => Some(*id),
            _ => None,
        }
    }

    pub fn new(ctx: &mut TyCtx, ty: TyId) -> Option<Self> {
        Self::droppable_trait(ctx).map(|x| Self {
            droppable: x,
            ty,
            fun_id: None,
        })
    }

    pub fn is_droppable(&self, tir: &mut TirCtx, ctx: &mut TyCtx) -> bool {
        if tir.ty_implements[&self.ty].contains(&self.droppable) {
            return true;
        }
        if let Some(no_drop) = NoDropImpler::no_drop_trait(ctx) {
            if tir.ty_implements[&self.ty].contains(&no_drop) {
                return false;
            }
        }

        match self.ty.as_concrete(ctx).clone() {
            ConcreteType::SpecializedClass(sc_id) => sc_id
                .as_spec_class(ctx)
                .clone()
                .fields
                .iter()
                .any(|SCField { ty, .. }| {
                    TypeChecker::type_impl_trait(tir, ctx, self.droppable, *ty).is_ok()
                }),
            ConcreteType::Primitive(_) => false,
            ConcreteType::Ptr(_) => false,
            ConcreteType::Tuple(ids) => ids
                .iter()
                .any(|ty| TypeChecker::type_impl_trait(tir, ctx, self.droppable, *ty).is_ok()),
        }
    }

    pub fn concretize_droppable(
        &mut self,
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
    ) -> Result<(), TcError> {
        if self.fun_id.is_some() {
            return Ok(());
        }

        let drop_symb = ctx.ctx.interner.insert_symbol(&"drop".to_string());

        let self_symb = ctx.ctx.interner.insert_symbol(&"self".to_string());

        if tir.ty_implements[&self.ty].contains(&self.droppable) {
            return Ok(());
        }

        if !self.is_droppable(tir, ctx) {
            return Err(TcError::Text(format!(
                "Cannot derive Droppable trait for non-trivially droppable type `{}`",
                self.ty.to_string(ctx)
            )));
        }

        let void_ty_c = tir.void_ty(ctx);
        let void_ty = ctx
            .ctx
            .interner
            .insert_type_expr(TypeExpr::Concrete(void_ty_c));

        let self_ptr_ty_c = tir.get_ptr_to(ctx, self.ty);

        let self_ptr_ty = ctx
            .ctx
            .interner
            .insert_type_expr(TypeExpr::Concrete(self_ptr_ty_c));

        let fun_proto = TcFunProto {
            name: drop_symb,
            params: vec![TcParam {
                name: self_symb,
                ty: self_ptr_ty,
            }],
            return_ty: void_ty,
            variadic: false,
        };

        let actual_sig = Signature {
            name: drop_symb,
            params: vec![SCField {
                name: self_symb,
                ty: self_ptr_ty_c,
            }],
            return_ty: void_ty_c,
            variadic: false,
        };

        let fun_id = ctx.ctx.interner.insert_fun(fun_proto);

        tir.methods
            .get_mut(&self.ty)
            .unwrap()
            .insert(drop_symb, fun_id);

        tir.protos.insert(fun_id, actual_sig);

        tir.ty_implements
            .get_mut(&self.ty)
            .unwrap()
            .insert(self.droppable);

        self.fun_id = Some(fun_id);

        Ok(())
    }

    pub fn implement_droppable(&self, tir: &mut TirCtx, ctx: &mut TyCtx) -> Result<(), TcError> {
        if self.fun_id.is_none() {
            return Ok(());
        }

        let old_scope = ctx.current_scope;
        let old_defer_stack = ctx.defer_stack.clone();
        let scope_id = if let Some(sc_id) = self.ty.as_sc(ctx) {
            ctx.with_scope(ScopeKind::Spec(sc_id), |ctx| ctx.current_scope)
        } else {
            ScopeId::new(0)
        };

        ctx.current_scope = scope_id;
        ctx.defer_stack.clear();

        let drop_symbol = ctx.ctx.interner.insert_symbol(&"drop".to_string());
        let fun_id = self.fun_id.unwrap();
        let dummy_item = ctx.ctx.interner.insert_item(NirItem::Dummy);

        ctx.with_scope(ScopeKind::Function(fun_id, dummy_item, vec![]), |ctx| {
            let self_ptr = tir.create_expr(ctx, TirExpr::Arg(0), false);
            match self.ty.as_concrete(ctx).clone() {
                ConcreteType::SpecializedClass(sc_id) => {
                    let sc = sc_id.as_spec_class(ctx).clone();
                    for f in sc.fields {
                        if TypeChecker::type_impl_trait(tir, ctx, self.droppable, f.ty).is_ok() {
                            let drop_fun_id = tir.methods[&f.ty][&drop_symbol];
                            let ptr_access = tir.create_expr(
                                ctx,
                                TirExpr::PtrAccess(self_ptr, FieldAccessKind::Symbol(f.name)),
                                false,
                            );
                            let _drop_call = tir.create_expr(
                                ctx,
                                TirExpr::Funcall(drop_fun_id, vec![ptr_access]),
                                false,
                            );
                        }
                    }
                    Ok(())
                }
                ConcreteType::Primitive(_) => Err(TcError::Text(format!("Internal compiler error: should not generate automatically drop method for primitive type"))),
                ConcreteType::Ptr(_) => Err(TcError::Text(format!("Internal compiler error: should not generate automatically drop method for ptr type"))),
                ConcreteType::Tuple(ids) => {
                    for (i, ty) in ids.iter().copied().enumerate() {
                        if TypeChecker::type_impl_trait(tir, ctx, self.droppable, ty).is_ok() {
                            let drop_fun_id = tir.methods[&ty][&drop_symbol];
                            let ptr_access = tir.create_expr(
                                ctx,
                                TirExpr::PtrAccess(self_ptr, FieldAccessKind::Index(i.try_into().unwrap())),
                                false,
                            );
                            let _drop_call = tir.create_expr(
                                ctx,
                                TirExpr::Funcall(drop_fun_id, vec![ptr_access]),
                                false,
                            );
                        }
                    }
                Ok(())
                }
            }
        })?;

        ctx.current_scope = old_scope;
        ctx.defer_stack = old_defer_stack;

        Ok(())
    }
}
