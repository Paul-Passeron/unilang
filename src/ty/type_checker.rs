use crate::{
    common::global_interner::{FunId, SCId, TyId},
    ty::{
        TcError, TyCtx,
        tir::{ArgsMatch, TirCtx},
    },
};

pub struct TypeChecker;

impl TypeChecker {
    pub fn get_matching_constructor(
        tir_ctx: &TirCtx,
        ty_ctx: &TyCtx,
        args: &[TyId],
        target: SCId,
    ) -> Result<FunId, TcError> {
        let sc = target.as_spec_class(ty_ctx);
        let constructors = sc.constructors.iter().map(|cons| {
            let sig = tir_ctx.protos.get(cons);
            (
                *cons,
                sig.map_or(ArgsMatch::No, |sig| sig.get_match(ty_ctx, args)),
            )
        });

        constructors
            .clone()
            .find(|(_, m)| matches!(m, ArgsMatch::Perfect))
            .map_or_else(
                || {
                    constructors
                        .clone()
                        .find(|(_, m)| matches!(m, ArgsMatch::Casts(_)))
                },
                Some,
            )
            .map(|(cons, _)| cons)
            .ok_or(TcError::Text(format!("No matching constructor found")))
    }
}
