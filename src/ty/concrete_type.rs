use crate::{
    common::global_interner::{SCId, Symbol, TyId},
    ty::{
        PrimitiveTy, TyCtx,
        tir::{ConcreteType, TirCtx},
    },
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

    pub fn as_primitive(&self, ctx: &TyCtx) -> Option<PrimitiveTy> {
        match self.as_concrete(ctx) {
            ConcreteType::Primitive(p) => Some(*p),
            _ => None,
        }
    }

    pub fn as_tuple(&self, ctx: &TyCtx) -> Option<Vec<TyId>> {
        match self.as_concrete(ctx) {
            ConcreteType::Tuple(ids) => Some(ids.clone()),
            _ => None,
        }
    }

    pub fn get_named_field(&self, ctx: &TyCtx, name: Symbol) -> Option<TyId> {
        self.as_sc(ctx)?
            .as_spec_class(ctx)
            .fields
            .iter()
            .find(|x| x.name == name)
            .map(|x| x.ty)
    }

    pub fn get_nth_tuple_field(&self, ctx: &TyCtx, n: usize) -> Option<TyId> {
        self.as_tuple(ctx)?.get(n).copied()
    }

    pub fn is_integer(&self, ctx: &TyCtx) -> bool {
        match self.as_concrete(ctx) {
            ConcreteType::Primitive(PrimitiveTy::Void) => false,
            ConcreteType::Primitive(_) => true,
            _ => false,
        }
    }

    pub fn unfold(&self, ctx: &TyCtx) -> Vec<TyId> {
        match self.as_concrete(ctx) {
            ConcreteType::Tuple(ids) => ids.clone(),
            _ => vec![*self],
        }
    }

    pub fn get_size(&self, ctx: &TyCtx) -> usize {
        let t = self.as_concrete(ctx);
        let alignement = 4;

        match t {
            ConcreteType::SpecializedClass(sc_id) => {
                let sc = sc_id.as_spec_class(ctx);
                sc.fields.iter().fold(0, |acc, ty| {
                    let res = acc + ty.ty.get_size(ctx);
                    let x = res % alignement;
                    res + if x != 0 { alignement - x } else { 0 }
                })
            }
            ConcreteType::Primitive(p) => p.size(),
            ConcreteType::Ptr(_) => 4,
            ConcreteType::Tuple(ids) => ids.iter().fold(0, |acc, ty| {
                let res = acc + ty.get_size(ctx);
                let x = res % alignement;
                res + if x != 0 { alignement - x } else { 0 }
            }),
        }
    }

    pub fn is_coercible(&self, tir_ctx: &TirCtx, ctx: &TyCtx, target: TyId) -> bool {
        if *self == target {
            return true;
        }
        if self.is_integer(ctx) && target.is_integer(ctx) {
            return true;
        }

        if self.as_ptr(ctx).is_some() && target.as_ptr(ctx).is_some() {
            return true;
        }

        if let Some(sc_id) = target.as_sc(ctx) {
            let args = &self.unfold(ctx)[..];
            return sc_id.get_matching_constructor(tir_ctx, ctx, args).is_some();
        }

        todo!()
    }
}
