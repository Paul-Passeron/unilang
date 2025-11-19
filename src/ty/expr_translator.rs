use crate::{
    common::global_interner::{ExprId, FunId, Symbol, TirExprId, TyId, VariableId},
    nir::nir::{
        FieldAccess, NirBinOp, NirCall, NirExprKind, NirLiteral, NirType, NirUnOpKind, StrLit,
    },
    ty::{
        TcError, TyCtx,
        displays::Displayable,
        scope::Definition,
        tir::{TirCtx, TypedIntLit},
        type_checker::TypeChecker,
    },
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
        match lit {
            NirLiteral::IntLiteral(i) => tir.create_expr(
                ctx,
                TirExpr::TypedIntLit(TypedIntLit::I64(i64::try_from(*i).unwrap())),
                defer,
            ),
            NirLiteral::FloatLiteral(_) => unreachable!("floats are not supported yet"),
            NirLiteral::StringLiteral(strlit) => {
                tir.create_expr(ctx, TirExpr::StringLiteral(*strlit), defer)
            }
            NirLiteral::CharLiteral(c) => tir.create_expr(
                ctx,
                TirExpr::TypedIntLit(TypedIntLit::U8(u8::try_from(*c).unwrap())),
                defer,
            ),
            NirLiteral::BoolLiteral(b) => {
                tir.create_expr(ctx, if *b { TirExpr::True } else { TirExpr::False }, defer)
            }
        }
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
        let (fun_id, self_ty) = TypeChecker::get_called_fun(tir, ctx, &call.called)?;
        let self_expr = if let Some(_) = self_ty {
            let receiver = call.called.receiver.as_ref().unwrap().clone();
            let self_expr = if TypeChecker::get_type_of_expr(tir, ctx, receiver)?
                .as_ptr(ctx)
                .is_some()
            {
                Self::expr(tir, ctx, receiver, defer)
            } else {
                Self::expr_as_ptr(tir, ctx, receiver, defer)
            }?;

            Some(self_expr)
        } else {
            None
        };
        let args = Self::create_call_args(tir, ctx, call, fun_id, self_expr, defer)?;
        Ok(tir.create_expr(ctx, TirExpr::Funcall(fun_id, args), defer))
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

    fn named_ptr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        name: Symbol,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let var_id = Self::get_var_id(ctx, name)?;
        Ok(tir.create_expr(ctx, TirExpr::VarPtr(var_id), defer))
    }

    fn get_var_id(ctx: &mut TyCtx, name: Symbol) -> Result<VariableId, TcError> {
        let err = TcError::Text(format!(
            "Name {} was not declared in the current context",
            name.to_string(ctx)
        ));
        let def_id = ctx.get_symbol_def(name);
        let def = def_id.ok_or(err.clone())?;
        match def.get_def(ctx) {
            Definition::Var(var_id) => Ok(*var_id),
            _ => Err(err),
        }
    }

    fn named(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        name: Symbol,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let named = Self::named_ptr(tir, ctx, name, defer)?;
        Ok(tir.create_expr(ctx, TirExpr::Deref(named), defer))
    }

    fn deref_tir(tir: &mut TirCtx, ctx: &mut TyCtx, expr: TirExprId, defer: bool) -> TirExprId {
        // unsafe to call if the expr is not of ptr type
        tir.create_expr(ctx, TirExpr::Deref(expr), defer)
    }

    fn deref(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let e_ty = TypeChecker::get_type_of_expr(tir, ctx, expr)?;
        let e = Self::expr(tir, ctx, expr, defer)?;
        e_ty.as_ptr(ctx)
            .ok_or(TcError::Text(format!(
                "Only pointer types can be dereferenced for the moment. Got: `{}`",
                e_ty.to_string(ctx)
            )))
            .map(|_| Self::deref_tir(tir, ctx, e, defer))
    }

    fn size_of(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        nir_type: &NirType,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let te = ctx.visit_type(nir_type)?;
        let ty = tir.visit_type(ctx, te)?;
        let size = ty.get_size(ctx);
        Ok(tir.create_expr(
            ctx,
            TirExpr::TypedIntLit(TypedIntLit::U64(size as u64)),
            defer,
        ))
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
        let tirs = exprs
            .iter()
            .map(|x| Self::expr(tir, ctx, *x, defer))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(tir.create_expr(ctx, TirExpr::Tuple(tirs), defer))
    }

    fn create_call_args(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        call: &NirCall,
        fun_id: FunId,
        self_expr: Option<TirExprId>,
        defer: bool,
    ) -> Result<Vec<TirExprId>, TcError> {
        let exprs = {
            let padding = if self_expr.is_some() { 1 } else { 0 };
            let sig = fun_id.sig(tir).clone();
            let call_args_len = call.args.len();
            if !sig.variadic && call_args_len + padding != sig.params.len() {
                return Err(TcError::Text(format!(
                    "Function {} expects {} arguments but got {}",
                    sig.name.to_string(ctx),
                    sig.params.len(),
                    call_args_len
                )));
            }
            let tys = sig
                .params
                .iter()
                .skip(1)
                .enumerate()
                .map(|(i, x)| (i < call_args_len).then_some(x.ty));

            self_expr
                .into_iter()
                .chain(
                    tys.zip(call.args.iter())
                        .map(|(ty_opt, expr)| {
                            if let Some(ty) = ty_opt {
                                Self::expr_with_type(tir, ctx, *expr, ty, defer)
                            } else {
                                Self::expr(tir, ctx, *expr, defer)
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter(),
                )
                .collect::<Vec<_>>()
        };
        Ok(exprs)
    }
}
