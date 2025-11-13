use crate::{
    common::global_interner::{SCId, TyId},
    ty::{PrimitiveTy, TyCtx, tir::ConcreteType},
};

impl TyId {
    pub fn as_concrete<'ctx>(&self, ctx: &'ctx TyCtx) -> &'ctx ConcreteType {
        ctx.ctx.interner.get_conc_type(*self)
    }

    pub fn as_mut_concrete<'ctx>(&self, ctx: &'ctx mut TyCtx) -> &'ctx mut ConcreteType {
        ctx.ctx.interner.get_conc_type_mut(*self)
    }

    pub fn as_ptr(&self, ctx: &TyCtx) -> Option<TyId> {
        match self.as_concrete(ctx) {
            ConcreteType::Ptr(inner) => Some(*inner),
            _ => None,
        }
    }

    pub fn as_sc(&self, ctx: &TyCtx) -> Option<SCId> {
        match self.as_concrete(ctx) {
            ConcreteType::SpecializedClass(id) => Some(*id),
            _ => None,
        }
    }

    pub fn is_integer(&self, ctx: &TyCtx) -> bool {
        match self.as_concrete(ctx) {
            ConcreteType::Primitive(PrimitiveTy::Void) => false,
            ConcreteType::Primitive(_) => true,
            _ => true,
        }
    }

    pub fn unfold(&self, ctx: &TyCtx) -> Vec<TyId> {
        match self.as_concrete(ctx) {
            ConcreteType::Tuple(ids) => ids.clone(),
            _ => vec![*self],
        }
    }

    pub fn is_coercible(&self, ctx: &TyCtx, target: TyId) -> bool {
        if *self == target {
            return true;
        }
        if self.is_integer(ctx) && target.is_integer(ctx) {
            return true;
        }

        if let Some(_) = self.as_ptr(ctx)
            && let Some(_) = target.as_ptr(ctx)
        {
            return true;
        }

        if let Some(sc_id) = target.as_sc(ctx) {
            let args = &self.unfold(ctx)[..];
        }

        todo!()
    }
}
