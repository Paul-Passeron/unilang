use crate::{
    common::global_interner::{ExprId, TyId},
    nir::nir::{NirBinOp, NirBinOpKind, NirExprKind, NirLiteral},
    ty::{TcError, TyCtx, tir::TirCtx},
};

pub struct TypeChecker;

impl TypeChecker {
    pub fn get_type_of_lit(tir: &TirCtx, ctx: &TyCtx, lit: &NirLiteral) -> TyId {
        match lit {
            // Defaults to biggest int size, can then be downcasted
            // with no overhead.
            // Same thing for signedness
            NirLiteral::IntLiteral(_) => tir.i64_ty(ctx),
            NirLiteral::FloatLiteral(_) => unreachable!("floats are not supported yet"),
            NirLiteral::StringLiteral(_) => tir.u8_ptr_ty(ctx),
            NirLiteral::CharLiteral(_) => tir.u8_ty(ctx),
        }
    }

    pub fn get_type_of_binop<'ctx>(
        op: NirBinOpKind,
        left: TyId,
        right: TyId,
        ctx: &TyCtx,
    ) -> Result<TyId, TcError> {
        match op {
            NirBinOpKind::Add | NirBinOpKind::Sub => {
                // TODO: issue warnings
                if left.is_integer(ctx) && right.is_integer(ctx) {
                    if right.get_size(ctx) > left.get_size(ctx) {
                        return Ok(right);
                    } else {
                        return Ok(left);
                    }
                }
                todo!()
            }
            NirBinOpKind::Mul => todo!(),
            NirBinOpKind::Div => todo!(),
            NirBinOpKind::Mod => todo!(),
            NirBinOpKind::Equ => todo!(),
            NirBinOpKind::Dif => todo!(),
            NirBinOpKind::LOr => todo!(),
            NirBinOpKind::LAnd => todo!(),
            NirBinOpKind::BOr => todo!(),
            NirBinOpKind::BAnd => todo!(),
            NirBinOpKind::BXor => todo!(),
            NirBinOpKind::Geq => todo!(),
            NirBinOpKind::Leq => todo!(),
            NirBinOpKind::Gt => todo!(),
            NirBinOpKind::Lt => todo!(),
        }
    }

    pub fn get_type_of_expr<'ctx>(
        tir: &mut TirCtx,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
    ) -> Result<TyId, TcError> {
        let nir = expr.to_nir(ctx).clone();
        match nir.kind {
            NirExprKind::Literal(lit) => Ok(Self::get_type_of_lit(tir, ctx, &lit)),
            NirExprKind::BinOp(NirBinOp { op, left, right }) => {
                let left_ty = Self::get_type_of_expr(tir, ctx, left)?;
                let right_ty = Self::get_type_of_expr(tir, ctx, right)?;
                Self::get_type_of_binop(op, left_ty, right_ty, ctx)
            }
            NirExprKind::UnOp { op, operand } => todo!(),
            NirExprKind::Call(nir_call) => todo!(),
            NirExprKind::Subscript { value, index } => todo!(),
            NirExprKind::Access { from, field } => todo!(),
            NirExprKind::Named(one_shot_id) => todo!(),
            NirExprKind::PostIncr(one_shot_id) => todo!(),
            NirExprKind::PreIncr(one_shot_id) => todo!(),
            NirExprKind::PostDecr(one_shot_id) => todo!(),
            NirExprKind::PreDecr(one_shot_id) => todo!(),
            NirExprKind::AddrOf(one_shot_id) => todo!(),
            NirExprKind::Deref(one_shot_id) => todo!(),
            NirExprKind::SizeOf(nir_type) => todo!(),
            NirExprKind::StringOf(nir_type) => todo!(),
            NirExprKind::Minus(one_shot_id) => todo!(),
            NirExprKind::Not(one_shot_id) => todo!(),
            NirExprKind::New { ty, expr } => todo!(),
            NirExprKind::As { ty, expr } => todo!(),
            NirExprKind::Tuple(one_shot_ids) => todo!(),
            NirExprKind::Range { start, end } => todo!(),
            NirExprKind::TodoDir => todo!(),
        }
    }
}
