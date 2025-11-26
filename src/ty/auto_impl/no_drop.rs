use crate::{
    common::global_interner::{ScopeId, TraitId, TyId},
    nir::interner::ConstructibleId,
    ty::{
        TcError, TyCtx,
        displays::Displayable,
        scope::Definition,
        tir::{ConcreteType, TirCtx},
    },
};

pub struct NoDropImpler {
    no_drop_trait: TraitId,
}

impl NoDropImpler {
    pub fn new(ctx: &mut TyCtx) -> Option<Self> {
        Self::no_drop_trait(ctx).map(|x| Self { no_drop_trait: x })
    }

    pub fn no_drop_trait(ctx: &mut TyCtx) -> Option<TraitId> {
        let trait_symbol = ctx.ctx.interner.insert_symbol(&"NoDrop".to_string());
        let def = ctx.get_symbol_def_in_scope(ScopeId::new(0), trait_symbol)?;
        match def.get_def(ctx) {
            Definition::Trait(id) => Some(*id),
            _ => None,
        }
    }

    pub fn is_no_drop(&self, tir: &mut TirCtx, ctx: &mut TyCtx, ty: TyId) -> bool {
        let no_drop_trait = self.no_drop_trait;
        if tir.ty_implements[&ty].contains(&no_drop_trait) {
            return true;
        }
        match ty.as_concrete(ctx).clone() {
            ConcreteType::SpecializedClass(sc_id) => sc_id
                .as_spec_class(ctx)
                .fields
                .clone()
                .iter()
                .all(|x| self.is_no_drop(tir, ctx, x.ty)),
            ConcreteType::Primitive(_) => true,
            ConcreteType::Ptr(_) => false,
            ConcreteType::Tuple(ids) => ids.into_iter().all(|x| self.is_no_drop(tir, ctx, x)),
        }
    }

    pub fn implement_no_drop(
        &self,
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        ty: TyId,
    ) -> Result<(), TcError> {
        let trait_id = Self::no_drop_trait(ctx).ok_or(TcError::Text(format!(
            "Compiler internal error: the trait `NoDrop` was not found"
        )))?;

        if !self.is_no_drop(tir, ctx, ty) {
            return Err(TcError::Text(format!(
                "Cannot derive NoDrop trait for non-trivially droppable type `{}`",
                ty.to_string(ctx)
            )));
        }

        tir.ty_implements.get_mut(&ty).unwrap().insert(trait_id);
        Ok(())
    }
}
