use crate::{
    common::global_interner::{FunId, SCId, TyId},
    ty::{
        TyCtx,
        tir::{ArgsMatch, SpecializedClass, TirCtx},
    },
};

impl SCId {
    pub fn as_spec_class<'ctx>(&self, ctx: &'ctx TyCtx) -> &'ctx SpecializedClass {
        ctx.ctx.interner.get_sc(*self)
    }

    pub fn as_mut_spec_class<'ctx>(&self, ctx: &'ctx mut TyCtx) -> &'ctx mut SpecializedClass {
        ctx.ctx.interner.get_sc_mut(*self)
    }

    pub fn get_matching_constructor(
        &self,
        tir_ctx: &TirCtx,
        ty_ctx: &TyCtx,
        args: &[TyId],
    ) -> Option<FunId> {
        let sc = self.as_spec_class(ty_ctx);
        let constructors = sc.constructors.iter().map(|cons| {
            let sig = tir_ctx.protos.get(cons);
            (
                *cons,
                sig.map_or(ArgsMatch::No, |sig| {
                    sig.get_match(tir_ctx, ty_ctx, args, true)
                }),
            )
        });

        // Todo: find best match from the casts instead of
        // the first one.

        constructors
            .clone()
            .find(|(_, m)| {
                if matches!(m, ArgsMatch::Perfect) {
                    println!("Perfect match found");
                    true
                } else {
                    false
                }
            })
            .map_or_else(
                || {
                    constructors
                        .clone()
                        .find(|(_, m)| matches!(m, ArgsMatch::Casts(_)))
                },
                Some,
            )
            .map(|(cons, _)| cons)
    }
}
