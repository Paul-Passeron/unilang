use crate::{
    common::global_interner::{DefId, ExprId, FunId, ModuleId, Symbol, TyId},
    nir::nir::{
        FieldAccess, FieldAccessKind, NirBinOp, NirBinOpKind, NirCall, NirCalled, NirExprKind,
        NirLiteral, NirUnOpKind,
    },
    parser::ast::Ty,
    ty::{
        TcError, TyCtx,
        displays::Displayable,
        tir::TirCtx,
        tir_pass::{Receiver, TypeReceiver},
    },
};

use super::{scope::Definition, tir::ConcreteType};

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
        tir: &TirCtx,
        ctx: &TyCtx,
    ) -> Result<TyId, TcError> {
        match op {
            NirBinOpKind::Add | NirBinOpKind::Sub => {
                // TODO: issue warnings !
                if left.is_integer(ctx) && right.is_integer(ctx) {
                    if right.get_size(ctx) > left.get_size(ctx) {
                        Ok(right)
                    } else {
                        Ok(left)
                    }
                } else if left.is_integer(ctx) && right.as_ptr(ctx).is_some() {
                    Ok(right)
                } else if right.is_integer(ctx) && left.as_ptr(ctx).is_some() {
                    Ok(left)
                } else if right.as_ptr(ctx).is_some() && left.as_ptr(ctx).is_some() {
                    Ok(left)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `{}` is not supported yet between types `{}` and `{}`.",
                        if op == NirBinOpKind::Add { "+" } else { "-" },
                        left.to_string(ctx),
                        right.to_string(ctx),
                    )))
                }
            }
            NirBinOpKind::Mul => {
                if left.is_integer(ctx) && right.is_integer(ctx) {
                    if right.get_size(ctx) > left.get_size(ctx) {
                        Ok(right)
                    } else {
                        Ok(left)
                    }
                } else {
                    Err(TcError::Text(format!(
                        "Operation `*` is not supported yet between types `{}` and `{}`.",
                        left.to_string(ctx),
                        right.to_string(ctx),
                    )))
                }
            }
            NirBinOpKind::Div | NirBinOpKind::Mod => {
                if left.as_ptr(ctx).is_some() && right.as_ptr(ctx).is_some() {
                    Ok(tir.u64_ty(ctx))
                } else if !right.is_integer(ctx) {
                    Err(TcError::Text(format!(
                        "Operation `{}` needs its right hand side to be of integer type instead of {}.",
                        if op == NirBinOpKind::Div { "/" } else { "%" },
                        right.to_string(ctx)
                    )))
                } else if right.is_integer(ctx) {
                    if right.get_size(ctx) > left.get_size(ctx) {
                        Ok(right)
                    } else {
                        Ok(left)
                    }
                } else {
                    Err(TcError::Text(format!(
                        "Operation `{}` is not supported yet between types `{}` and `{}`.",
                        if op == NirBinOpKind::Div { "/" } else { "%" },
                        left.to_string(ctx),
                        right.to_string(ctx),
                    )))
                }
            }
            NirBinOpKind::Geq
            | NirBinOpKind::Leq
            | NirBinOpKind::Gt
            | NirBinOpKind::Lt
            | NirBinOpKind::Equ
            | NirBinOpKind::Dif => {
                if left.is_integer(ctx) && right.is_integer(ctx) {
                    Ok(tir.bool_ty(ctx))
                } else if left.as_ptr(ctx).is_some() && right.as_ptr(ctx).is_some() {
                    Ok(tir.bool_ty(ctx))
                } else if right.is_coercible(tir, ctx, left)
                    && (left.as_ptr(ctx).is_some() || left.is_integer(ctx))
                {
                    Ok(tir.bool_ty(ctx))
                } else {
                    Err(TcError::Text(format!(
                        "Operation `{}` is not supported yet between types `{}` and `{}`.",
                        if op == NirBinOpKind::Equ { "=" } else { "!=" },
                        left.to_string(ctx),
                        right.to_string(ctx),
                    )))
                }
            }
            NirBinOpKind::LOr | NirBinOpKind::LAnd => {
                let b = tir.bool_ty(ctx);
                if left == b && right == b {
                    Ok(b)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `{}` is not supported yet between types `{}` and `{}`.",
                        if op == NirBinOpKind::LOr { "||" } else { "&&" },
                        left.to_string(ctx),
                        right.to_string(ctx),
                    )))
                }
            }
            NirBinOpKind::BOr | NirBinOpKind::BAnd | NirBinOpKind::BXor => {
                if (left.is_integer(ctx) || left.as_ptr(ctx).is_some())
                    && (right.is_integer(ctx) || right.as_ptr(ctx).is_some())
                {
                    if right.get_size(ctx) > left.get_size(ctx) {
                        Ok(right)
                    } else {
                        Ok(left)
                    }
                } else {
                    Err(TcError::Text(format!(
                        "Operation `{}` is not supported yet between types `{}` and `{}`.",
                        if op == NirBinOpKind::BOr {
                            "|"
                        } else if op == NirBinOpKind::BAnd {
                            "&"
                        } else {
                            "^"
                        },
                        left.to_string(ctx),
                        right.to_string(ctx),
                    )))
                }
            }
        }
    }

    pub fn get_type_of_unop(
        op: NirUnOpKind,
        ty: TyId,
        tir: &TirCtx,
        ctx: &mut TyCtx,
    ) -> Result<TyId, TcError> {
        match op {
            NirUnOpKind::Minus => {
                if ty.is_integer(ctx) {
                    Ok(ty)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `-` is not supported on type {}",
                        ty.to_string(ctx)
                    )))
                }
            }
            NirUnOpKind::LNot => {
                if ty == tir.bool_ty(ctx) {
                    Ok(ty)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `!` is not supported on type {}",
                        ty.to_string(ctx)
                    )))
                }
            }
            NirUnOpKind::BNot => {
                if ty.is_integer(ctx) || ty.is_integer(ctx) {
                    Ok(ty)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `~` is not supported on type {}",
                        ty.to_string(ctx)
                    )))
                }
            }
            NirUnOpKind::Deref => {
                if let Some(inner_ty) = ty.as_ptr(ctx) {
                    Ok(inner_ty)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `*` is not supported on type {}",
                        ty.to_string(ctx)
                    )))
                }
            }
            NirUnOpKind::AddrOf => Ok(ctx.ctx.interner.insert_conc_type(ConcreteType::Ptr(ty))),
        }
    }

    pub fn get_type_receiver(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: ExprId,
    ) -> Result<TypeReceiver, TcError> {
        if let Some(id) = Self::expr_as_module(ctx, expr) {
            Ok(TypeReceiver::Module(id))
        } else {
            Self::get_type_of_expr(tir, ctx, expr).map(TypeReceiver::Object)
        }
    }

    pub fn expr_as_module(ctx: &TyCtx, expr: ExprId) -> Option<ModuleId> {
        let nir = expr.to_nir(ctx).clone();
        let def: Option<DefId> = match nir.kind {
            NirExprKind::Access {
                from,
                field:
                    FieldAccess {
                        kind: FieldAccessKind::Symbol(field),
                        ..
                    },
            } => {
                let outer_module = Self::expr_as_module(ctx, from)?;
                let as_m = ctx.ctx.interner.get_module(outer_module);
                let scope = as_m.scope;
                ctx.get_symbol_def_in_scope(scope, field)
            }

            NirExprKind::Named(name) => ctx.get_symbol_def(name),
            _ => None,
        };

        def.map_or(None, |x| {
            let d = ctx.ctx.interner.get_def(x);
            match d {
                Definition::Module(id) => Some(*id),
                _ => None,
            }
        })
    }

    pub fn get_fun_id_self_ty(
        tir: &TirCtx,
        ctx: &TyCtx,
        receiver: TypeReceiver,
        called: Symbol,
    ) -> Result<(FunId, Option<TyId>), TcError> {
        match receiver {
            TypeReceiver::Object(id) => {
                let ty = id.as_ptr(ctx).unwrap_or(id);
                if !tir.methods[&ty].contains_key(&called) {
                    Err(TcError::Text(format!(
                        "No method named {} for type {}",
                        called.to_string(ctx),
                        ty.to_string(ctx)
                    )))
                } else {
                    Ok((tir.methods[&ty][&called].clone(), Some(ty)))
                }
            }
            TypeReceiver::Module(id) => {
                let m = ctx.ctx.interner.get_module(id);
                let s = m.scope;
                let def_id = ctx.get_symbol_def_in_scope(s, called);
                let fun_id = def_id.map_or(None, |x| match x.get_def(ctx) {
                    Definition::Function(id) => Some(*id),
                    _ => None,
                });
                fun_id
                    .ok_or(TcError::Text(format!(
                        "No such function {} in module {}",
                        called.to_string(ctx),
                        id.get_name(ctx)
                    )))
                    .map(|id| (id, None))
            }
        }
    }

    pub fn get_called_fun(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        called: NirCalled,
    ) -> Result<FunId, TcError> {
        if let Some(receiver) = called.receiver {
            let receiver = Self::get_type_receiver(tir, ctx, receiver)?;
            let (fun_id, _) = Self::get_fun_id_self_ty(tir, ctx, receiver, called.called)?;
            Ok(fun_id)
        } else {
            // Context is global
            tir.get_fun_id_from_symbol(ctx, called.called)
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
                Self::get_type_of_binop(op, left_ty, right_ty, tir, ctx)
            }
            NirExprKind::UnOp { op, operand } => {
                let operand_ty = Self::get_type_of_expr(tir, ctx, operand)?;
                Self::get_type_of_unop(op, operand_ty, tir, ctx)
            }
            NirExprKind::Call(NirCall {
                called,
                generic_args,
                args,
                span,
            }) => {
                // todo: Do something else
                assert!(generic_args.len() == 0);
                let fun_id = Self::get_called_fun(tir, ctx, called)?;
                Ok(fun_id.return_type(tir))
            }
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
