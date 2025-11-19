use crate::{
    common::global_interner::{ExprId, Symbol, TirExprId, TyId},
    nir::nir::{
        FieldAccess, NirBinOp, NirCall, NirExprKind, NirLiteral, NirType, NirUnOpKind, StrLit,
    },
    ty::{TcError, TyCtx, displays::Displayable, tir::TirCtx, type_checker::TypeChecker},
};

use super::tir::TirExpr;

pub struct ExprTranslator;

impl ExprTranslator {
    pub fn expr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        // This ensure the expression type checks
        let _expr_ty = TypeChecker::get_type_of_expr(tir, ctx, expr)?;

        let nir_expr = expr.to_nir(ctx).clone();
        match nir_expr.kind {
            NirExprKind::Literal(lit) => Ok(Self::literal(tir, ctx, &lit, defer)),
            NirExprKind::BinOp(binop) => Self::binop(tir, ctx, &binop, defer),
            NirExprKind::UnOp { op, operand } => Self::unop(tir, ctx, op, operand, defer),
            NirExprKind::Call(call) => Self::call(tir, ctx, &call, defer),
            NirExprKind::Subscript { value, index } => {
                Self::subscript(tir, ctx, value, index, defer)
            }
            NirExprKind::Access { from, field } => Self::access(tir, ctx, from, field, defer),
            NirExprKind::Named(name) => Self::named(tir, ctx, name, defer),
            NirExprKind::AddrOf(to_ref) => Self::expr_as_ptr(tir, ctx, to_ref, defer),
            NirExprKind::Deref(one_shot_id) => Self::deref(tir, ctx, one_shot_id, defer),
            NirExprKind::SizeOf(nir_type) => Self::size_of(tir, ctx, &nir_type, defer),
            NirExprKind::StringOf(nir_type) => Self::string_of(tir, ctx, &nir_type, defer),
            NirExprKind::New { ty, expr } => {
                let target_te = ctx.visit_type(&ty)?;
                let ty_id = tir.visit_type(ctx, target_te)?;
                Self::new_dir(tir, ctx, ty_id, expr, defer)
            }
            NirExprKind::As { ty, expr } => {
                let target_te = ctx.visit_type(&ty)?;
                let ty_id = tir.visit_type(ctx, target_te)?;
                Self::as_dir(tir, ctx, ty_id, expr, defer)
            }
            NirExprKind::Tuple(exprs) => Self::tuple(tir, ctx, &exprs[..], defer),
            NirExprKind::Range { .. } => Err(TcError::Text(format!(
                "The range expression is not typeable"
            ))),
            NirExprKind::PostIncr(_) => Err(TcError::Text(format!(
                "The post-increment operation is not supported yet"
            ))),
            NirExprKind::PreIncr(_) => Err(TcError::Text(format!(
                "The pre-increment operation is not supported yet"
            ))),
            NirExprKind::PostDecr(_) => Err(TcError::Text(format!(
                "The post-decrement operation is not supported yet"
            ))),
            NirExprKind::PreDecr(_) => Err(TcError::Text(format!(
                "The pre-decrement operation is not supported yet"
            ))),
            NirExprKind::TodoDir => Err(TcError::Text(format!(
                "The TODO directive is not supported yet"
            ))),
        }
    }

    pub fn expr_as_ptr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    pub fn coerce_expr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: TirExprId,
        ty: TyId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    pub fn expr_with_type(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: ExprId,
        ty: TyId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let src_ty = TypeChecker::get_type_of_expr(tir, ctx, expr)?;

        if ty.as_tuple(ctx).is_some() {
            if let Some(res) = Self::try_as_typed_tuple(tir, ctx, expr, ty, defer) {
                return Ok(res);
            }
        }

        let e = Self::expr(tir, ctx, expr, defer)?;
        if src_ty == ty {
            Ok(e)
        } else {
            Self::coerce_expr(tir, ctx, e, ty, defer)
        }
    }

    pub fn try_as_typed_tuple(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: ExprId,
        ty: TyId,
        defer: bool,
    ) -> Option<TirExprId> {
        let nir_expr = expr.to_nir(ctx).clone();

        match (nir_expr.kind, ty.as_tuple(ctx)) {
            (NirExprKind::Tuple(exprs), Some(targets)) if exprs.len() == targets.len() => {
                let typeds = exprs
                    .iter()
                    .zip(targets)
                    .map(|(e, ty)| Self::expr_with_type(tir, ctx, *e, ty, defer))
                    .collect::<Result<Vec<_>, _>>();
                typeds
                    .ok()
                    .map(|typeds| tir.create_expr(ctx, TirExpr::Tuple(typeds), defer))
            }
            _ => None,
        }
    }

    fn literal(tir: &mut TirCtx, ctx: &mut TyCtx, lit: &NirLiteral, defer: bool) -> TirExprId {
        todo!()
    }

    fn binop(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        binop: &NirBinOp,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn unop(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        op: NirUnOpKind,
        operand: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn call(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        call: &NirCall,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn subscript(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        value: ExprId,
        index: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn access(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        from: ExprId,
        field: FieldAccess,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn named(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        name: Symbol,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn deref(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        one_shot_id: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn size_of(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        nir_type: &NirType,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn string_of(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        nir_type: &NirType,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let te = ctx.visit_type(nir_type)?;
        let ty = tir.visit_type(ctx, te)?;
        let as_str = ty.to_string(ctx);
        let symbol = ctx.ctx.interner.insert_string(&StrLit(as_str));
        Ok(tir.create_expr(ctx, TirExpr::StringLiteral(symbol), defer))
    }

    fn new_dir(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        ty: TyId,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn as_dir(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        ty: TyId,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }

    fn tuple(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        exprs: &[ExprId],
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        todo!()
    }
}
