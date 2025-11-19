use crate::{
    common::global_interner::{ExprId, FunId, SCId, Symbol, TirExprId, TyId, VariableId},
    nir::nir::{
        FieldAccess, FieldAccessKind, NirBinOp, NirBinOpKind, NirCall, NirExprKind, NirLiteral,
        NirType, NirUnOpKind, StrLit,
    },
    ty::{
        TcError, TyCtx,
        displays::Displayable,
        scope::Definition,
        tir::{ConcreteType, TirCtx, TirInstr, TypedIntLit},
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
                let ptr = Self::subscript(tir, ctx, value, index, defer)?;
                Ok(Self::deref_tir(tir, ctx, ptr, defer))
            }
            NirExprKind::Access { from, field } => Self::access(tir, ctx, from, field, defer),
            NirExprKind::Named(name) => Self::named(tir, ctx, name, defer),
            NirExprKind::AddrOf(to_ref) => Self::lvalue_ptr(tir, ctx, to_ref, defer),
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

    pub fn lvalue_ptr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        // Make sure that the expression type checks
        TypeChecker::get_type_of_expr(tir, ctx, expr)?;

        let nir_expr = expr.to_nir(ctx).clone();

        match nir_expr.kind {
            NirExprKind::Named(name) => Self::named_ptr(tir, ctx, name, defer),
            NirExprKind::Access { from, field } => {
                let from_expr = Self::lvalue_ptr(tir, ctx, from, defer)?;
                let lval = tir.create_expr(ctx, TirExpr::PtrAccess(from_expr, field.kind), defer);
                Ok(lval)
            }
            NirExprKind::Deref(e) => Ok(Self::expr(tir, ctx, e, defer)?),
            NirExprKind::Subscript { value, index } => {
                Self::subscript(tir, ctx, value, index, defer)
            }
            _ => Err(TcError::Text(format!(
                "The expression {:?} cannot be used as a lvalue",
                nir_expr
            ))),
        }
    }

    pub fn coerce_expr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: TirExprId,
        ty: TyId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let src_ty = TypeChecker::get_type_of_tir_expr(tir, ctx, expr)?;
        if src_ty == ty {
            return Ok(expr);
        }

        if src_ty.is_integer(ctx) && ty.is_integer(ctx) {
            return Ok(tir.create_expr(ctx, TirExpr::IntCast(ty, expr), defer));
        }

        if src_ty.as_ptr(ctx).is_some() && ty.as_ptr(ctx).is_some() {
            return Ok(tir.create_expr(ctx, TirExpr::PtrCast(ty, expr), defer));
        }

        if src_ty.is_integer(ctx) && ty.as_ptr(ctx).is_some() {
            return Ok(tir.create_expr(ctx, TirExpr::PtrCast(ty, expr), defer));
        }

        if src_ty.as_ptr(ctx).is_some() && ty.is_integer(ctx) {
            return Ok(tir.create_expr(ctx, TirExpr::IntCast(ty, expr), defer));
        }

        if let Some(sc_id) = ty.as_sc(ctx) {
            Self::coerce_to_sc(tir, ctx, sc_id, expr, defer)
        } else {
            Err(TcError::Text(format!(
                "Cannot coerce `{}` to `{}`",
                src_ty.to_string(ctx),
                ty.to_string(ctx)
            )))
        }
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
        let left_ty = TypeChecker::get_type_of_expr(tir, ctx, binop.left)?;
        let right_ty = TypeChecker::get_type_of_expr(tir, ctx, binop.right)?;

        match binop.op {
            NirBinOpKind::Add | NirBinOpKind::Sub => {
                // Determine the target type for both operands
                let (target_left_ty, target_right_ty) =
                    if left_ty.is_integer(ctx) && right_ty.is_integer(ctx) {
                        // Both integers: use the larger type for both
                        let target = if right_ty.get_size(ctx) > left_ty.get_size(ctx) {
                            right_ty
                        } else {
                            left_ty
                        };
                        (target, target)
                    } else if left_ty.as_ptr(ctx).is_some() && right_ty.is_integer(ctx) {
                        // Pointer + integer: keep pointer as-is, coerce integer to i64
                        (left_ty, tir.i64_ty(ctx))
                    } else if left_ty.is_integer(ctx) && right_ty.as_ptr(ctx).is_some() {
                        // Integer + pointer: coerce integer to i64, keep pointer as-is
                        (tir.i64_ty(ctx), right_ty)
                    } else if left_ty.as_ptr(ctx).is_some() && right_ty.as_ptr(ctx).is_some() {
                        // Pointer + pointer: keep both as-is
                        (left_ty, right_ty)
                    } else {
                        return Err(TcError::Text(format!(
                            "Addition not supported between types `{}` and `{}`",
                            left_ty.to_string(ctx),
                            right_ty.to_string(ctx)
                        )));
                    };

                let lhs = Self::expr_with_type(tir, ctx, binop.left, target_left_ty, defer)?;
                let rhs = Self::expr_with_type(tir, ctx, binop.right, target_right_ty, defer)?;

                Ok(tir.create_expr(
                    ctx,
                    TirExpr::BinOp {
                        lhs,
                        rhs,
                        op: binop.op,
                    },
                    defer,
                ))
            }
            NirBinOpKind::Mul => {
                // Both operands must be integers
                if !left_ty.is_integer(ctx) || !right_ty.is_integer(ctx) {
                    return Err(TcError::Text(format!(
                        "Multiplication requires both operands to be integers, got `{}` and `{}`",
                        left_ty.to_string(ctx),
                        right_ty.to_string(ctx)
                    )));
                }

                // Use the larger type for both operands
                let target = if right_ty.get_size(ctx) > left_ty.get_size(ctx) {
                    right_ty
                } else {
                    left_ty
                };

                let lhs = Self::expr_with_type(tir, ctx, binop.left, target, defer)?;
                let rhs = Self::expr_with_type(tir, ctx, binop.right, target, defer)?;

                Ok(tir.create_expr(
                    ctx,
                    TirExpr::BinOp {
                        lhs,
                        rhs,
                        op: binop.op,
                    },
                    defer,
                ))
            }

            NirBinOpKind::Div | NirBinOpKind::Mod => {
                // Both operands must be integers
                if !(left_ty.is_integer(ctx) || left_ty.as_ptr(ctx).is_some())
                    || !right_ty.is_integer(ctx)
                {
                    return Err(TcError::Text(format!(
                        "Multiplication requires both operands to be integers, got `{}` and `{}`",
                        left_ty.to_string(ctx),
                        right_ty.to_string(ctx)
                    )));
                }

                // Use the larger type for both operands or u64 if ptr / int
                let target = if left_ty.as_ptr(ctx).is_some() {
                    tir.u64_ty(ctx)
                } else {
                    if right_ty.get_size(ctx) > left_ty.get_size(ctx) {
                        right_ty
                    } else {
                        left_ty
                    }
                };

                let lhs = Self::expr_with_type(tir, ctx, binop.left, target, defer)?;
                let rhs = Self::expr_with_type(tir, ctx, binop.right, target, defer)?;

                Ok(tir.create_expr(
                    ctx,
                    TirExpr::BinOp {
                        lhs,
                        rhs,
                        op: binop.op,
                    },
                    defer,
                ))
            }

            NirBinOpKind::Equ
            | NirBinOpKind::Dif
            | NirBinOpKind::Geq
            | NirBinOpKind::Leq
            | NirBinOpKind::Gt
            | NirBinOpKind::Lt => {
                let (target_left_ty, target_right_ty) =
                    if left_ty.as_ptr(ctx).is_some() || right_ty.as_ptr(ctx).is_some() {
                        // If either is a pointer, coerce both to pointer type
                        let ptr_ty = left_ty
                            .as_ptr(ctx)
                            .map(|_| left_ty)
                            .or_else(|| right_ty.as_ptr(ctx).map(|_| right_ty))
                            .unwrap();
                        (ptr_ty, ptr_ty)
                    } else if left_ty.is_integer(ctx) && right_ty.is_integer(ctx) {
                        // Both integers: use the larger type for both
                        let target = if right_ty.get_size(ctx) > left_ty.get_size(ctx) {
                            right_ty
                        } else {
                            left_ty
                        };
                        (target, target)
                    } else {
                        return Err(TcError::Text(format!(
                            "Comparison not supported between types `{}` and `{}`",
                            left_ty.to_string(ctx),
                            right_ty.to_string(ctx)
                        )));
                    };

                let lhs = Self::expr_with_type(tir, ctx, binop.left, target_left_ty, defer)?;
                let rhs = Self::expr_with_type(tir, ctx, binop.right, target_right_ty, defer)?;

                Ok(tir.create_expr(
                    ctx,
                    TirExpr::BinOp {
                        lhs,
                        rhs,
                        op: binop.op,
                    },
                    defer,
                ))
            }

            _ => todo!("Other binary operations not yet implemented"),
        }
    }

    fn unop(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        op: NirUnOpKind,
        operand: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        // Get the operand type for validation and to create appropriate literals
        let operand_ty = TypeChecker::get_type_of_expr(tir, ctx, operand)?;

        match op {
            NirUnOpKind::Minus => {
                let operand_expr = Self::expr(tir, ctx, operand, defer)?;
                let zero = tir.create_expr(ctx, TirExpr::TypedIntLit(TypedIntLit::I64(0)), defer);
                let zero = Self::coerce_expr(tir, ctx, zero, operand_ty, defer)?;
                Ok(tir.create_expr(
                    ctx,
                    TirExpr::BinOp {
                        lhs: zero,
                        rhs: operand_expr,
                        op: NirBinOpKind::Sub,
                    },
                    defer,
                ))
            }
            NirUnOpKind::LNot => {
                let operand_expr = Self::expr(tir, ctx, operand, defer)?;
                let operand_expr =
                    Self::coerce_expr(tir, ctx, operand_expr, tir.bool_ty(ctx), defer)?;
                let false_val = tir.create_expr(ctx, TirExpr::False, defer);
                Ok(tir.create_expr(
                    ctx,
                    TirExpr::BinOp {
                        lhs: operand_expr,
                        rhs: false_val,
                        op: NirBinOpKind::Equ,
                    },
                    defer,
                ))
            }
            NirUnOpKind::BNot => Err(TcError::Text(
                "Bitwise not operation not supported in the compiler yet".to_string(),
            )),
            NirUnOpKind::Deref => {
                // Deref is handled in the main expr function, but also here for consistency
                Self::deref(tir, ctx, operand, defer)
            }
            NirUnOpKind::AddrOf => {
                // AddrOf is also handled in the main expr function, but also here for consistency
                Self::lvalue_ptr(tir, ctx, operand, defer)
            }
        }
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
                Self::lvalue_ptr(tir, ctx, receiver, defer)
            }?;

            Some(self_expr)
        } else {
            None
        };
        let args = Self::create_call_args(tir, ctx, call, fun_id, self_expr, defer)?;
        println!(
            "{}:{}:{} Calling {} with {} args.",
            file!(),
            line!(),
            column!(),
            fun_id.sig(tir).name.to_string(ctx),
            args.len()
        );
        Ok(tir.create_expr(ctx, TirExpr::Funcall(fun_id, args), defer))
    }

    fn subscript(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        value: ExprId,
        index: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let value_ty = TypeChecker::get_type_of_expr(tir, ctx, value)?;

        if value_ty.as_ptr(ctx).is_none() {
            return Err(TcError::Text(format!(
                "Cannot subscript non-pointer type `{}`",
                value_ty.to_string(ctx)
            )));
        }

        let index_ty = TypeChecker::get_type_of_expr(tir, ctx, index)?;
        if index_ty.is_integer(ctx) {
            return Err(TcError::Text(format!(
                "Cannot subscript with non-integer index type `{}`",
                index_ty.to_string(ctx)
            )));
        }

        let ptr = Self::expr(tir, ctx, value, defer)?;
        let index = Self::expr(tir, ctx, index, defer)?;

        Ok(tir.create_expr(ctx, TirExpr::Subscript { ptr, index }, defer))
    }

    fn access(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        from: ExprId,
        field: FieldAccess,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let from_ty = TypeChecker::get_type_of_expr(tir, ctx, from)?;
        let from_expr = Self::expr(tir, ctx, from, defer)?;

        match field.kind {
            FieldAccessKind::Symbol(field_name) => {
                let mut dereferenced = false;
                let ty = from_ty.as_ptr(ctx).unwrap_or_else(|| {
                    dereferenced = true;
                    from_ty
                });
                if let Some(scid) = ty.as_sc(ctx) {
                    scid.as_spec_class(ctx)
                        .fields
                        .iter()
                        .find(|field| field.name == field_name)
                        .ok_or(TcError::Text(format!(
                            "Cannot access named field `{}` of type `{}`.",
                            field_name.to_string(ctx),
                            from_ty.to_string(ctx)
                        )))
                        .map(|_| ())?;

                    let accessed = if dereferenced {
                        TirExpr::Deref(tir.create_expr(
                            ctx,
                            TirExpr::PtrAccess(from_expr, field.kind),
                            defer,
                        ))
                    } else {
                        TirExpr::Access(from_expr, field.kind)
                    };

                    Ok(tir.create_expr(ctx, accessed, defer))
                } else {
                    Err(TcError::Text(format!(
                        "Cannot access named field `{}` of non-struct-like type `{}`.",
                        field_name.to_string(ctx),
                        from_ty.to_string(ctx)
                    )))
                }
            }
            FieldAccessKind::Index(i) => {
                if let Some(fields) = from_ty.as_tuple(ctx) {
                    fields.get(i as usize).ok_or(TcError::Text(format!(
                        "Cannot access indexed field {} of type `{}`.",
                        i,
                        from_ty.to_string(ctx)
                    )))?;
                    Ok(tir.create_expr(ctx, TirExpr::Access(from_expr, field.kind), defer))
                } else {
                    Err(TcError::Text(format!(
                        "Cannot access indexed field {} of non-tuple type `{}`.",
                        i,
                        from_ty.to_string(ctx)
                    )))
                }
            }
        }
    }

    fn get_var_id(ctx: &mut TyCtx, name: Symbol) -> Result<VariableId, TcError> {
        let err = TcError::Text(format!(
            "Name `{}` was not declared in the current context",
            name.to_string(ctx)
        ));
        let def_id = ctx.get_symbol_def(name);
        let def = def_id.ok_or(err.clone())?;
        match def.get_def(ctx) {
            Definition::Var(var_id) => Ok(*var_id),
            _ => Err(err),
        }
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

    fn named(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        name: Symbol,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let named = Self::named_ptr(tir, ctx, name, defer)?;
        Ok(Self::deref_tir(tir, ctx, named, defer))
    }

    // Warning: unsafe to call if the expr is not of ptr type
    fn deref_tir(tir: &mut TirCtx, ctx: &mut TyCtx, expr: TirExprId, defer: bool) -> TirExprId {
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

    fn construct_object_at_ptr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        sc: SCId,
        args: Vec<TirExprId>,
        ptr: TirExprId,
        defer: bool,
    ) -> Result<(), TcError> {
        let tys = args
            .iter()
            .map(|x| TypeChecker::get_type_of_tir_expr(tir, ctx, *x))
            .collect::<Result<Vec<_>, _>>()?;

        let constructor = sc
            .get_matching_constructor(tir, ctx, &tys[..])
            .ok_or(TcError::Text(format!(
                "No matching constructor found for class `{}` matching signature ({}).",
                sc.to_string(ctx),
                tys.iter().to_string(ctx)
            )))?;

        let sig = constructor.sig(tir).clone();

        assert!(!sig.variadic);

        let args = Some(ptr)
            .into_iter()
            .chain(
                sig.params
                    .iter()
                    .skip(1)
                    .zip(args)
                    .map(|(param, arg)| Self::coerce_expr(tir, ctx, arg, param.ty, defer))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter(),
            )
            .collect::<Vec<_>>();

        tir.create_expr(ctx, TirExpr::Funcall(constructor, args), defer);

        Ok(())
    }

    fn unwrap_expr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: ExprId,
        defer: bool,
    ) -> Result<Vec<TirExprId>, TcError> {
        TypeChecker::get_type_of_expr(tir, ctx, expr)?;

        match expr.to_nir(ctx).kind.clone() {
            NirExprKind::Tuple(exprs) => exprs
                .into_iter()
                .map(|x| Self::expr(tir, ctx, x, defer))
                .collect::<Result<Vec<_>, _>>(),
            _ => Ok(vec![Self::expr(tir, ctx, expr, defer)?]),
        }
    }

    fn new_dir(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        ty: TyId,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        // Create a malloced ptr
        // construct the object with it
        let ptr = tir.create_expr(ctx, TirExpr::Malloc(ty), defer);
        if let Some(sc_id) = ty.as_sc(ctx) {
            let unwrapped = Self::unwrap_expr(tir, ctx, expr, defer)?;
            Self::construct_object_at_ptr(tir, ctx, sc_id, unwrapped, ptr, defer)?;
        } else {
            let tir_expr = Self::expr(tir, ctx, expr, defer)?;
            let value = Self::coerce_expr(tir, ctx, tir_expr, ty, defer)?;
            ctx.push_instr(TirInstr::Assign(ptr, value), defer);
        }
        Ok(ptr)
    }

    fn coerce_to_sc(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        sc_id: SCId,
        expr: TirExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let ty = tir.create_type(ctx, ConcreteType::SpecializedClass(sc_id));
        let ptr = tir.create_expr(ctx, TirExpr::Alloca(ty), defer);
        Self::construct_object_at_ptr(tir, ctx, sc_id, vec![expr], ptr, defer)?;
        Ok(tir.create_expr(ctx, TirExpr::Deref(ptr), defer))
    }

    fn as_dir(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        ty: TyId,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        // Construct the object directly, no malloc
        if let Some(sc_id) = ty.as_sc(ctx) {
            let ptr = tir.create_expr(ctx, TirExpr::Alloca(ty), defer);
            let unwrapped = Self::unwrap_expr(tir, ctx, expr, defer)?;
            Self::construct_object_at_ptr(tir, ctx, sc_id, unwrapped, ptr, defer)?;
            Ok(tir.create_expr(ctx, TirExpr::Deref(ptr), defer))
        } else {
            let tir_expr = Self::expr(tir, ctx, expr, defer)?;
            Ok(Self::coerce_expr(tir, ctx, tir_expr, ty, defer)?)
        }
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
            let mut tys = vec![];

            for i in 0..call_args_len {
                tys.push(sig.params.get(i).map(|x| x.ty))
            }

            self_expr
                .into_iter()
                .chain(
                    tys.into_iter()
                        .zip(call.args.iter())
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
