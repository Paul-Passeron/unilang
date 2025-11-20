use crate::{
    common::global_interner::{DefId, ExprId, FunId, ModuleId, Symbol, TirExprId, TyId},
    nir::nir::{
        FieldAccess, FieldAccessKind, NirBinOp, NirBinOpKind, NirCall, NirCalled, NirExprKind,
        NirLiteral, NirUnOpKind,
    },
    ty::{
        PrimitiveTy, TcError, TyCtx,
        displays::Displayable,
        tir::{ArgsMatch, TirCtx, TypedIntLit},
        tir_pass::TypeReceiver,
    },
};

use super::{
    scope::Definition,
    tir::{ConcreteType, TirExpr},
};

pub struct TypeChecker;

impl TypeChecker {
    pub fn get_type_of_lit(tir: &TirCtx, ctx: &TyCtx, lit: &NirLiteral) -> TyId {
        match lit {
            NirLiteral::IntLiteral(_) => tir.i64_ty(ctx),
            NirLiteral::FloatLiteral(_) => unreachable!("floats are not supported yet"),
            NirLiteral::StringLiteral(_) => tir.u8_ptr_ty(ctx),
            NirLiteral::CharLiteral(_) => tir.u8_ty(ctx),
            NirLiteral::BoolLiteral(_) => tir.bool_ty(ctx),
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
                        "Operation `{}` needs its right hand side to be of integer type instead of `{}`.",
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
        op: &NirUnOpKind,
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
                        "Operation `-` is not supported on type `{}`",
                        ty.to_string(ctx)
                    )))
                }
            }
            NirUnOpKind::LNot => {
                if ty == tir.bool_ty(ctx) {
                    Ok(ty)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `!` is not supported on type `{}`",
                        ty.to_string(ctx)
                    )))
                }
            }
            NirUnOpKind::BNot => {
                if ty.is_integer(ctx) || ty.is_integer(ctx) {
                    Ok(ty)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `~` is not supported on type `{}`",
                        ty.to_string(ctx)
                    )))
                }
            }
            NirUnOpKind::Deref => {
                if let Some(inner_ty) = ty.as_ptr(ctx) {
                    Ok(inner_ty)
                } else {
                    Err(TcError::Text(format!(
                        "Operation `*` is not supported on type `{}`",
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
                        "No method named `{}` for type `{}`",
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
                        "No such function `{}` in module `{}`",
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
        called: &NirCalled,
    ) -> Result<(FunId, Option<TyId>), TcError> {
        if let Some(receiver) = called.receiver {
            let receiver = Self::get_type_receiver(tir, ctx, receiver)?;
            Self::get_fun_id_self_ty(tir, ctx, receiver, called.called)
        } else {
            // Context is global
            Ok((tir.get_fun_id_from_symbol(ctx, called.called)?, None))
        }
    }

    fn get_type_of_named<'ctx>(ctx: &mut TyCtx<'ctx>, name: Symbol) -> Result<TyId, TcError> {
        if let Some(def) = ctx.get_symbol_def(name) {
            match def.get_def(ctx) {
                Definition::Var(id) => {
                    let var = id.get_var(ctx);
                    return Ok(var.ty);
                }
                _ => (),
            }
        }
        Err(TcError::Text(format!(
            "Name `{}` was not declared in the current scope.",
            name.to_string(ctx),
        )))
    }

    pub fn get_type_of_expr<'ctx>(
        tir: &mut TirCtx,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
    ) -> Result<TyId, TcError> {
        let nir = expr.to_nir(ctx).clone();
        match &nir.kind {
            NirExprKind::Literal(lit) => Ok(Self::get_type_of_lit(tir, ctx, &lit)),
            NirExprKind::BinOp(NirBinOp { op, left, right }) => {
                let left_ty = Self::get_type_of_expr(tir, ctx, *left)?;
                let right_ty = Self::get_type_of_expr(tir, ctx, *right)?;
                Self::get_type_of_binop(*op, left_ty, right_ty, tir, ctx)
            }
            NirExprKind::UnOp { op, operand } => {
                let operand_ty = Self::get_type_of_expr(tir, ctx, *operand)?;
                Self::get_type_of_unop(op, operand_ty, tir, ctx)
            }
            NirExprKind::Call(NirCall {
                called,
                generic_args,
                args,
                ..
            }) => {
                // todo: Do something else
                assert!(generic_args.len() == 0);
                let (fun_id, self_ty) = Self::get_called_fun(tir, ctx, called)?;
                let sig = fun_id.sig(tir).clone();
                let args = args
                    .iter()
                    .map(|x| Self::get_type_of_expr(tir, ctx, *x))
                    .collect::<Result<Vec<_>, _>>()?;
                match sig.get_match(tir, ctx, &args, self_ty.is_some()) {
                    ArgsMatch::No => {
                        return Err(TcError::Text(format!(
                            "Mismatched arguments in call: Expected ({}) but got ({})",
                            sig.params
                                .iter()
                                .skip(if self_ty.is_some() { 1 } else { 0 })
                                .map(|x| &x.ty)
                                .to_string(ctx),
                            args.iter().to_string(ctx),
                        )));
                    }
                    _ => (),
                }
                // TODO: check the args
                Ok(fun_id.return_type(tir))
            }
            NirExprKind::Subscript { value, index } => {
                let value_ty = Self::get_type_of_expr(tir, ctx, *value)?;
                let index_ty = Self::get_type_of_expr(tir, ctx, *index)?;
                if let Some(inner) = value_ty.as_ptr(ctx) {
                    if index_ty.is_integer(ctx) {
                        Ok(inner)
                    } else {
                        Err(TcError::Text(format!(
                            "Type `{}` can only be indexed by integer types. Got: `{}`",
                            value_ty.to_string(ctx),
                            index_ty.to_string(ctx)
                        )))
                    }
                } else {
                    Err(TcError::Text(format!(
                        "Only pointer types can be subscripted for the moment. Got: `{}`",
                        value_ty.to_string(ctx),
                    )))
                }
            }
            NirExprKind::Deref(e) => {
                let e_ty = Self::get_type_of_expr(tir, ctx, *e)?;
                e_ty.as_ptr(ctx).ok_or(TcError::Text(format!(
                    "Only pointer types can be dereferenced for the moment. Got: `{}`",
                    e_ty.to_string(ctx)
                )))
            }
            NirExprKind::AddrOf(e) => {
                let e_ty = Self::get_type_of_expr(tir, ctx, *e)?;
                tir.create_type(ctx, ConcreteType::Ptr(e_ty))
            }
            NirExprKind::Access { from, field } => {
                let from_ty = Self::get_type_of_expr(tir, ctx, *from)?;
                Self::get_type_of_access(ctx, from_ty, field)
            }
            NirExprKind::Named(name) => Self::get_type_of_named(ctx, *name),

            NirExprKind::SizeOf(ty) => {
                let t_e = ctx.visit_type(&ty)?;
                tir.visit_type(ctx, t_e)?;
                Ok(tir.u64_ty(ctx))
            }
            NirExprKind::StringOf(ty) => {
                let t_e = ctx.visit_type(&ty)?;
                tir.visit_type(ctx, t_e)?;
                Ok(tir.u8_ptr_ty(ctx))
            }
            NirExprKind::New { ty, expr } | NirExprKind::As { ty, expr } => {
                let target_te = ctx.visit_type(&ty)?;
                let target = tir.visit_type(ctx, target_te)?;
                let expr_ty = Self::get_type_of_expr(tir, ctx, *expr)?;
                let is_new = matches!(nir.kind, NirExprKind::New { .. });

                if expr_ty.is_coercible(tir, ctx, target) {
                    if is_new {
                        tir.create_type(ctx, ConcreteType::Ptr(target))
                    } else {
                        Ok(target)
                    }
                } else {
                    Err(TcError::Text(format!(
                        "Type `{}` is not coercible to type `{}` in @{} directive",
                        expr_ty.to_string(ctx),
                        target.to_string(ctx),
                        if is_new { "new" } else { "as" }
                    )))
                }
            }
            NirExprKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|x| Self::get_type_of_expr(tir, ctx, *x))
                    .collect::<Result<Vec<_>, _>>()?;

                tir.create_type(ctx, ConcreteType::Tuple(tys))
            }
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

    fn get_type_of_access<'ctx>(
        ctx: &mut TyCtx<'ctx>,
        from_ty: TyId,
        field: &FieldAccess,
    ) -> Result<crate::nir::interner::OneShotId<ConcreteType>, TcError> {
        let mut from_ty = from_ty;
        if let Some(inner) = from_ty.as_ptr(ctx)
            && inner.as_sc(ctx).is_some()
        {
            from_ty = inner;
        }
        match field.kind {
            FieldAccessKind::Symbol(field) => {
                if from_ty.as_sc(ctx).is_some() {
                    from_ty
                        .get_named_field(ctx, field)
                        .ok_or(TcError::Text(format!(
                            "Cannot access named field `{}` of type `{}`.",
                            field.to_string(ctx),
                            from_ty.to_string(ctx)
                        )))
                } else {
                    Err(TcError::Text(format!(
                        "Cannot access named field `{}` of non-struct-like type `{}`.",
                        field.to_string(ctx),
                        from_ty.to_string(ctx)
                    )))
                }
            }
            FieldAccessKind::Index(i) => {
                if from_ty.as_tuple(ctx).is_some() {
                    from_ty
                        .get_nth_tuple_field(ctx, i as usize)
                        .ok_or(TcError::Text(format!(
                            "Cannot access indexed field {} of type `{}`.",
                            i,
                            from_ty.to_string(ctx)
                        )))
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

    pub fn get_type_of_tir_expr(
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: TirExprId,
    ) -> Result<TyId, TcError> {
        match expr.get_tir(ctx).clone() {
            TirExpr::TypedIntLit(x) => match x {
                TypedIntLit::Ptr(id, _) => {
                    let ty = ConcreteType::Ptr(id);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::I8(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I8);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::I16(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I16);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::I32(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I32);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::I64(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I64);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::U8(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U8);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::U16(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U16);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::U32(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U32);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::U64(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U64);
                    tir.create_type(ctx, ty)
                }
                TypedIntLit::Bool(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::Bool);
                    tir.create_type(ctx, ty)
                }
            },
            TirExpr::Access(var, field_access_kind) => {
                let ty = Self::get_type_of_tir_expr(tir, ctx, var)?;
                tir.get_access_ty(ctx, ty, &field_access_kind)
            }
            TirExpr::IntCast(id, _) => Ok(id),
            TirExpr::Tuple(ids) => {
                let ty = ConcreteType::Tuple(
                    ids.iter()
                        .map(|x| Self::get_type_of_tir_expr(tir, ctx, *x))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                tir.create_type(ctx, ty)
            }
            TirExpr::BinOp { lhs, op, rhs } => match op {
                NirBinOpKind::Equ
                | NirBinOpKind::Dif
                | NirBinOpKind::Geq
                | NirBinOpKind::Leq
                | NirBinOpKind::Gt
                | NirBinOpKind::Lt
                | NirBinOpKind::LOr
                | NirBinOpKind::LAnd => Ok(tir.get_primitive_type(ctx, PrimitiveTy::Bool)),

                _ => {
                    let lt = Self::get_type_of_tir_expr(tir, ctx, lhs)?;
                    let rt = Self::get_type_of_tir_expr(tir, ctx, rhs)?;
                    if lt.as_ptr(ctx).is_some() {
                        Ok(lt)
                    } else if rt.as_ptr(ctx).is_some() {
                        Ok(rt)
                    } else {
                        Ok(Self::get_type_of_tir_expr(tir, ctx, lhs)?)
                    }
                }
            },
            TirExpr::Arg(i) => {
                let fun_id = ctx.get_current_fun().unwrap();
                let proto = &tir.protos[&fun_id];
                Ok(proto.params[i].ty)
            }
            TirExpr::Funcall(fun_id, _) => Ok(tir.protos[&fun_id].return_ty),
            TirExpr::PtrCast(id, _) => Ok(tir.get_ptr_to(ctx, id)),
            TirExpr::StringLiteral(_) => {
                let ty = tir.get_primitive_type(ctx, PrimitiveTy::U8);
                Ok(tir.get_ptr_to(ctx, ty))
            }
            TirExpr::True | TirExpr::False => Ok(tir.get_primitive_type(ctx, PrimitiveTy::Bool)),
            TirExpr::PtrAccess(expr, FieldAccessKind::Symbol(field_name)) => {
                let t = Self::get_type_of_tir_expr(tir, ctx, expr).unwrap();
                let mut ty = t.as_concrete(ctx);
                if let ConcreteType::Ptr(x) = ty {
                    ty = x.as_concrete(ctx);
                }
                if let ConcreteType::SpecializedClass(sc_id) = ty {
                    let sc = ctx.ctx.interner.get_sc(*sc_id);
                    let field = sc
                        .fields
                        .iter()
                        .find(|elem| elem.name == field_name)
                        .ok_or(TcError::Text(format!(
                            "Field named ??? not found in class ???"
                        )))?;
                    tir.create_type(ctx, ConcreteType::Ptr(field.ty))
                } else {
                    return Err(TcError::Text(format!(
                        "No named field in non-class type (get_type_of_tir_expr)",
                    )));
                }
            }
            TirExpr::PtrAccess(expr, FieldAccessKind::Index(i)) => {
                let t = Self::get_type_of_tir_expr(tir, ctx, expr).unwrap();
                let mut ty = t.as_concrete(ctx);
                if let ConcreteType::Ptr(x) = ty {
                    ty = x.as_concrete(ctx);
                }
                if let ConcreteType::Tuple(ids) = ty {
                    if ids.len() <= i as usize {
                        return Err(TcError::Text(format!("Tuple access out of range")));
                    }
                    tir.create_type(ctx, ConcreteType::Ptr(ids[i as usize]))
                } else {
                    return Err(TcError::Text(format!("No index field in non-tuple type")));
                }
            }
            TirExpr::VarPtr(id) => {
                let inner = ctx.ctx.interner.get_variable(id).ty;
                tir.create_type(ctx, ConcreteType::Ptr(inner))
            }
            TirExpr::Deref(e) => Ok(Self::get_type_of_tir_expr(tir, ctx, e)?
                .as_ptr(ctx)
                .unwrap()),
            TirExpr::Malloc(ty) | TirExpr::Alloca(ty) => {
                tir.create_type(ctx, ConcreteType::Ptr(ty))
            }
            TirExpr::Subscript { ptr, .. } => Self::get_type_of_tir_expr(tir, ctx, ptr),
        }
    }
}
