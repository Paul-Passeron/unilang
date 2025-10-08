use std::collections::HashMap;

use crate::{
    nir::{
        global_interner::{ExprId, Symbol, TirExprId, TyId, TypeExprId},
        nir::{
            FieldAccessKind, NirBinOp, NirBinOpKind, NirCall, NirExprKind, NirFunctionDef, NirItem,
            NirLiteral, NirPattern, NirPatternKind, NirStmt, NirStmtKind, NirVarDecl,
        },
    },
    ty::{
        PrimitiveTy, TcError,
        pass::Pass,
        scope::{Definition, Pattern, ScopeKind, VarDecl},
        surface_resolution::SurfaceResolutionPassOutput,
        tir::{ConcreteType, SCField, Signature, TirCtx, TirExpr, TirInstr, TirItem, TypedIntLit},
    },
};

use super::{TyCtx, scope::TypeExpr};

impl TirCtx {
    pub fn new() -> Self {
        Self {
            methods: HashMap::new(),
        }
    }
}

impl<'ctx> TirCtx {
    fn visit_type(&mut self, ctx: &mut TyCtx<'ctx>, ty: TypeExprId) -> Result<TyId, TcError> {
        let te = ctx.ctx.interner.get_type_expr(ty);
        match te {
            TypeExpr::Template(_) => todo!(),
            TypeExpr::Associated(_) => todo!(),
            TypeExpr::Instantiation { .. } => todo!(),
            TypeExpr::Ptr(id) => {
                let ty = ConcreteType::Ptr(self.visit_type(ctx, *id)?);
                Ok(ctx.ctx.interner.insert_conc_type(ty))
            }
            TypeExpr::Tuple(ids) => {
                let tys = ids
                    .clone()
                    .iter()
                    .map(|id| self.visit_type(ctx, *id))
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = ConcreteType::Tuple(tys);
                Ok(ctx.ctx.interner.insert_conc_type(ty))
            }
            TypeExpr::Primitive(primitive_ty) => {
                let ty = ConcreteType::Primitive(*primitive_ty);
                Ok(ctx.ctx.interner.insert_conc_type(ty))
            }
        }
    }

    fn type_is_coercible(&mut self, ctx: &mut TyCtx<'ctx>, src: TyId, target: TyId) -> bool {
        if src == target {
            return true;
        }
        let s = ctx.ctx.interner.get_conc_type(src);
        let t = ctx.ctx.interner.get_conc_type(target);
        if let ConcreteType::Primitive(prim_src) = s
            && let ConcreteType::Primitive(prim_target) = t
        {
            return match (prim_src, prim_target) {
                (PrimitiveTy::Void, PrimitiveTy::Void) => true,
                (PrimitiveTy::Void, _) => false,
                (_, PrimitiveTy::Void) => false,
                _ => true,
            };
        }
        if let ConcreteType::Primitive(_) = t {
            return false;
        }
        todo!()
    }

    fn extract_var_from_pattern(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        pattern: &Pattern,
        name: Symbol,
        expr: TirExprId,
    ) -> Result<TirExprId, TcError> {
        match pattern {
            Pattern::Wildcard => Err(TcError::NameNotFound(name)),
            Pattern::Symbol(x) => {
                if *x == name {
                    Ok(expr)
                } else {
                    Err(TcError::NameNotFound(name))
                }
            }
            Pattern::Tuple(ps) => {
                for (i, p) in ps.iter().enumerate() {
                    let e = TirExpr::Access(expr, FieldAccessKind::Index(i as u32));
                    let e_id = ctx.ctx.interner.insert_te(e);
                    match self.extract_var_from_pattern(ctx, p, name, e_id) {
                        Ok(expr) => {
                            return Ok(expr);
                        }
                        _ => (),
                    }
                }
                Err(TcError::NameNotFound(name))
            }
        }
    }

    fn get_primitive_type(&mut self, ctx: &mut TyCtx<'ctx>, prim: PrimitiveTy) -> TyId {
        ctx.ctx
            .interner
            .insert_conc_type(ConcreteType::Primitive(prim))
    }

    fn get_type_of_tir_expr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr_id: TirExprId,
    ) -> Result<TyId, TcError> {
        let expr = ctx.ctx.interner.get_te(expr_id).clone();
        match expr {
            TirExpr::TypedIntLit(x) => match x {
                TypedIntLit::Ptr(id, _) => {
                    let ty = ConcreteType::Ptr(id);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::I8(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I8);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::I16(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I16);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::I32(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I32);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::I64(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I64);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::U8(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U8);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::U16(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U16);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::U32(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U32);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::U64(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U64);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
                TypedIntLit::Bool(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::Bool);
                    Ok(ctx.ctx.interner.insert_conc_type(ty))
                }
            },
            TirExpr::Access(var, field_access_kind) => {
                let ty = self.get_type_of_tir_expr(ctx, var)?;
                self.get_access_ty(ctx, ty, &field_access_kind)
            }
            TirExpr::VarExpr(id) => {
                let var = ctx.ctx.interner.get_variable(id);
                Ok(var.ty)
            }
            TirExpr::IntCast(id, _) => Ok(id),
            TirExpr::Tuple(ids) => {
                let ty = ConcreteType::Tuple(
                    ids.iter()
                        .map(|x| self.get_type_of_tir_expr(ctx, *x))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                Ok(ctx.ctx.interner.insert_conc_type(ty))
            }
            TirExpr::BinOp { lhs, op, .. } => match op {
                NirBinOpKind::Equ
                | NirBinOpKind::Dif
                | NirBinOpKind::Geq
                | NirBinOpKind::Leq
                | NirBinOpKind::Gt
                | NirBinOpKind::Lt
                | NirBinOpKind::LOr
                | NirBinOpKind::LAnd => Ok(self.get_primitive_type(ctx, PrimitiveTy::Bool)),
                _ => Ok(self.get_type_of_tir_expr(ctx, lhs)?),
            },
        }
    }

    fn get_access_ty(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        ty: TyId,
        access: &FieldAccessKind,
    ) -> Result<TyId, TcError> {
        let t = ctx.ctx.interner.get_conc_type(ty);

        match access {
            FieldAccessKind::Symbol(_) => todo!(),
            FieldAccessKind::Index(i) => {
                if let ConcreteType::Tuple(tys) = t {
                    if tys.len() < *i as usize {
                        return Err(TcError::Text("Tuple access out of range"));
                    }
                    Ok(tys[*i as usize])
                } else {
                    return Err(TcError::Text("No integer field in non-tuple type"));
                }
            }
        }
    }

    fn get_type_of_expr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr_id: ExprId,
    ) -> Result<TyId, TcError> {
        let expr = ctx.ctx.interner.get_expr(expr_id).clone();
        match &expr.kind {
            NirExprKind::Literal(nir_literal) => match nir_literal {
                NirLiteral::IntLiteral(_) => Ok(self.get_primitive_type(ctx, PrimitiveTy::I64)),
                _ => todo!(),
            },
            NirExprKind::Named(name) => {
                let name = name.clone();
                let def = ctx.get_symbol_def(name);
                if def.is_none() {
                    return Err(TcError::NameNotFound(name));
                }
                let def = ctx.ctx.interner.get_def(def.unwrap());
                match def {
                    Definition::Var(id) => {
                        let var = ctx.ctx.interner.get_variable(*id);
                        Ok(var.ty)
                    }
                    _ => todo!(),
                }
            }
            NirExprKind::Tuple(exprs) => {
                let ty = ConcreteType::Tuple(
                    exprs
                        .clone()
                        .iter()
                        .map(|x| self.get_type_of_expr(ctx, *x))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                Ok(ctx.ctx.interner.insert_conc_type(ty))
            }
            NirExprKind::Access { from, field } => {
                let t = self.get_type_of_expr(ctx, from.clone())?;
                let ty = ctx.ctx.interner.get_conc_type(t);
                match field.kind {
                    FieldAccessKind::Symbol(_) => todo!(),
                    FieldAccessKind::Index(i) => {
                        if let ConcreteType::Tuple(tys) = ty {
                            if tys.len() < i as usize {
                                return Err(TcError::Text("Tuple access out of range"));
                            }
                            Ok(tys[i as usize])
                        } else {
                            return Err(TcError::Text("No integer field in non-tuple type"));
                        }
                    }
                }
            }
            NirExprKind::BinOp(NirBinOp { op, left, right }) => {
                let lt = self.get_type_of_expr(ctx, *left)?;
                let rt = self.get_type_of_expr(ctx, *right)?;
                if !self.is_type_integer(ctx, lt) || !self.is_type_integer(ctx, rt) {
                    return Err(TcError::Text("Cannot use binop with non-integer types"));
                }
                let lt_size = self.get_type_size(ctx, lt);
                let rt_size = self.get_type_size(ctx, rt);
                let operands_ty = if lt_size > rt_size { lt } else { rt };
                match op {
                    NirBinOpKind::Equ
                    | NirBinOpKind::Dif
                    | NirBinOpKind::Geq
                    | NirBinOpKind::Leq
                    | NirBinOpKind::Gt
                    | NirBinOpKind::Lt
                    | NirBinOpKind::LOr
                    | NirBinOpKind::LAnd => Ok(self.get_primitive_type(ctx, PrimitiveTy::Bool)),
                    _ => Ok(operands_ty),
                }
            }
            NirExprKind::Call(NirCall {
                called,
                generic_args,
                args: _,
                span: _,
            }) => {
                assert!(generic_args.len() == 0);
                assert!(called.receiver.is_none());
                let function = ctx.get_symbol_def(called.called);
                if function.is_none() {
                    return Err(TcError::NameNotFound(called.called));
                }
                todo!()
            }
            _ => todo!(),
        }
    }

    fn get_type_size(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> usize {
        let t = ctx.ctx.interner.get_conc_type(ty);
        let alignement = 4;
        match t {
            ConcreteType::SpecializedClass(_) => todo!(),
            ConcreteType::Primitive(primitive_ty) => primitive_ty.size(),
            ConcreteType::Ptr(_) => 4,
            ConcreteType::Tuple(ids) => {
                let mut size = 0;
                for id in ids.clone() {
                    size += self.get_type_size(ctx, id);
                    size += alignement - size % alignement;
                }
                size
            }
        }
    }

    fn is_type_integer(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> bool {
        let t = ctx.ctx.interner.get_conc_type(ty);
        match t {
            ConcreteType::Ptr(_) => true,
            ConcreteType::Primitive(PrimitiveTy::Void) => false,
            ConcreteType::Primitive(_) => true,
            _ => false,
        }
    }

    fn get_expr_with_type(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
        ty: TyId,
    ) -> Result<TirExprId, TcError> {
        let expr_ty = self.get_type_of_expr(ctx, expr)?;
        if !self.type_is_coercible(ctx, expr_ty, ty) {
            return Err(TcError::Text("Types are not coercible !"));
        }
        let expr = ctx.ctx.interner.get_expr(expr).clone();
        let t = ctx.ctx.interner.get_conc_type(ty);

        match &expr.kind {
            NirExprKind::Literal(nir_literal) => match nir_literal {
                NirLiteral::IntLiteral(x) => {
                    let e = TirExpr::TypedIntLit(match t {
                        ConcreteType::Primitive(primitive_ty) => match primitive_ty {
                            PrimitiveTy::Void => unreachable!(),
                            PrimitiveTy::I8 => TypedIntLit::I8(*x as i8),
                            PrimitiveTy::I16 => TypedIntLit::I16(*x as i16),
                            PrimitiveTy::I32 => TypedIntLit::I32(*x as i32),
                            PrimitiveTy::I64 => TypedIntLit::I64(*x as i64),
                            PrimitiveTy::U8 => TypedIntLit::U8(*x as u8),
                            PrimitiveTy::U16 => TypedIntLit::U16(*x as u16),
                            PrimitiveTy::U32 => TypedIntLit::U32(*x as u32),
                            PrimitiveTy::U64 => TypedIntLit::U64(*x as u64),
                            PrimitiveTy::Bool => TypedIntLit::Bool(*x != 0),
                        },
                        ConcreteType::Ptr(ptr) => TypedIntLit::Ptr(*ptr, *x as usize),
                        _ => todo!(),
                    });
                    Ok(ctx.ctx.interner.insert_te(e))
                }
                NirLiteral::FloatLiteral(_) => todo!(),
                NirLiteral::StringLiteral(_) => todo!(),
                NirLiteral::CharLiteral(_) => todo!(),
            },
            NirExprKind::Named(name) => {
                let def_id = ctx.get_symbol_def(*name);
                if def_id.is_none() {
                    return Err(TcError::NameNotFound(*name));
                }

                let def_id = def_id.unwrap();
                let def = ctx.ctx.interner.get_def(def_id);

                let var_id = match def {
                    Definition::Var(var_id) => *var_id,
                    _ => unreachable!(),
                };
                let var = ctx.ctx.interner.get_variable(var_id).clone();
                if var.ty == ty {
                    return Ok(ctx.ctx.interner.insert_te(TirExpr::VarExpr(var_id)));
                }
                if !self.type_is_coercible(ctx, var.ty, ty) {
                    return Err(TcError::Text("Types are not coercible !"));
                }
                if self.is_type_integer(ctx, var.ty) && self.is_type_integer(ctx, ty) {
                    let var_expr = ctx.ctx.interner.insert_te(TirExpr::VarExpr(var_id));
                    return Ok(ctx.ctx.interner.insert_te(TirExpr::IntCast(ty, var_expr)));
                }
                return Err(TcError::Text("Coerce non integer types !"));
            }
            NirExprKind::Tuple(exprs) => {
                if let ConcreteType::Tuple(types) = t {
                    if exprs.len() != types.len() {
                        return Err(TcError::Text("Coerce tuple to tuple of != size"));
                    }

                    let tuple = TirExpr::Tuple(
                        exprs
                            .clone()
                            .iter()
                            .zip(types.clone().iter())
                            .map(|(e, t)| self.get_expr_with_type(ctx, *e, *t))
                            .collect::<Result<Vec<_>, _>>()?,
                    );
                    Ok(ctx.ctx.interner.insert_te(tuple))
                } else {
                    return Err(TcError::Text("Coerce tuple into non tuple"));
                }
            }
            NirExprKind::Access { from, field } => {
                let left = self.get_expr(ctx, *from)?;
                self.get_access(ctx, left, field.kind)
            }
            NirExprKind::BinOp(NirBinOp { op, left, right }) => {
                let lt = self.get_type_of_expr(ctx, *left)?;
                let rt = self.get_type_of_expr(ctx, *right)?;
                if !self.is_type_integer(ctx, lt) || !self.is_type_integer(ctx, rt) {
                    return Err(TcError::Text("Cannot use binop with non-integer types"));
                }
                let lt_size = self.get_type_size(ctx, lt);
                let rt_size = self.get_type_size(ctx, rt);
                let operands_ty = if lt_size > rt_size { lt } else { rt };

                if matches!(op, NirBinOpKind::LOr | NirBinOpKind::LAnd) {
                    self.get_primitive_type(ctx, PrimitiveTy::Bool)
                } else if lt_size > rt_size {
                    lt
                } else {
                    rt
                };

                let lhs = self.get_expr_with_type(ctx, *left, operands_ty)?;
                let rhs = self.get_expr_with_type(ctx, *right, operands_ty)?;

                Ok(ctx
                    .ctx
                    .interner
                    .insert_te(TirExpr::BinOp { lhs, rhs, op: *op }))
            }
            x => todo!("{x:?}"),
        }
    }

    fn get_access(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: TirExprId,
        access: FieldAccessKind,
    ) -> Result<TirExprId, TcError> {
        match access {
            FieldAccessKind::Symbol(_) => todo!(),
            FieldAccessKind::Index(i) => {
                let ty = self.get_type_of_tir_expr(ctx, expr)?;
                let t = ctx.ctx.interner.get_conc_type(ty);
                if let ConcreteType::Tuple(tys) = t {
                    if tys.len() <= i as usize {
                        return Err(TcError::Text("Tuple access out of range"));
                    }
                    Ok(ctx.ctx.interner.insert_te(TirExpr::Access(expr, access)))
                } else {
                    return Err(TcError::Text("No integer field in non-tuple type"));
                }
            }
        }
    }

    fn get_expr(&mut self, ctx: &mut TyCtx<'ctx>, expr: ExprId) -> Result<TirExprId, TcError> {
        let ty = self.get_type_of_expr(ctx, expr)?;
        self.get_expr_with_type(ctx, expr, ty)
    }

    fn visit_pattern(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirPattern,
    ) -> Result<Pattern, TcError> {
        match &input.kind {
            NirPatternKind::Wildcard => Ok(Pattern::Wildcard),
            NirPatternKind::Symbol(id) => Ok(Pattern::Symbol(*id)),
            NirPatternKind::Tuple(nirs) => Ok(Pattern::Tuple(
                nirs.iter()
                    .map(|x| self.visit_pattern(ctx, x))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
        }
    }

    fn declare_pattern(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirPattern,
        ty: TyId,
        expr: Option<TirExprId>,
    ) -> Result<Vec<TirInstr>, TcError> {
        match &input.kind {
            NirPatternKind::Wildcard => Ok(vec![]),
            NirPatternKind::Symbol(symb) => {
                let id = ctx
                    .ctx
                    .interner
                    .insert_variable(VarDecl { name: *symb, ty });
                let d = ctx.ctx.interner.insert_def(Definition::Var(id));
                ctx.push_def(*symb, d);
                Ok(expr.iter().map(|x| TirInstr::Assign(id, *x)).collect())
            }
            NirPatternKind::Tuple(nirs) => {
                let t = ctx.ctx.interner.get_conc_type(ty);
                if !matches!(t, ConcreteType::Tuple(_)) {
                    return Err(TcError::Text(
                        "Tried to declare tuple variable with non tuple type",
                    ));
                }

                let tys = match t {
                    ConcreteType::Tuple(tys) => tys.clone(),
                    _ => unreachable!(),
                };

                if tys.len() != nirs.len() {
                    return Err(TcError::Text("Coerce tuple to tuple of != size"));
                }

                Ok(nirs
                    .iter()
                    .zip(tys.iter())
                    .enumerate()
                    .map(|(i, (x, ty))| {
                        let expr = expr.map(|e| {
                            ctx.ctx
                                .interner
                                .insert_te(TirExpr::Access(e, FieldAccessKind::Index(i as u32)))
                        });
                        self.declare_pattern(ctx, x, *ty, expr)
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect())
            }
        }
    }

    fn visit_let(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirVarDecl,
    ) -> Result<Vec<TirInstr>, TcError> {
        if input.ty.is_none() && input.value.is_none() {
            return Err(TcError::Text(
                "Type inference for variable is not availaible yet",
            ));
        }

        let ty = match input.ty.as_ref() {
            Some(ty) => {
                let ty_id = ctx.visit_type(ty)?;
                self.visit_type(ctx, ty_id)?
            }
            None => self.get_type_of_expr(ctx, input.value.unwrap())?,
        };

        let expr = match input.value.as_ref() {
            Some(e) => Some(self.get_expr_with_type(ctx, *e, ty)?),
            None => None,
        };
        self.declare_pattern(ctx, &input.pattern, ty, expr)
    }

    fn visit_stmt(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirStmt,
    ) -> Result<Vec<TirInstr>, TcError> {
        match &input.kind {
            NirStmtKind::Return { value } => {
                let void_ty = self.get_primitive_type(ctx, PrimitiveTy::Void);
                let return_ty = ctx.get_return_ty();
                let ret_id = return_ty.map_or(Ok(void_ty), |ty| self.visit_type(ctx, ty))?;

                if value.is_none() {
                    if ret_id != void_ty {
                        return Err(TcError::BadReturnType(void_ty, ret_id));
                    }
                    return Ok(vec![TirInstr::Return(None)]);
                }
                let value = value.unwrap();
                let expr_ty = self.get_type_of_expr(ctx, value)?;

                if !self.type_is_coercible(ctx, expr_ty, ret_id) {
                    return Err(TcError::BadReturnType(expr_ty, ret_id));
                }
                let expr = self.get_expr_with_type(ctx, value, ret_id)?;
                Ok(vec![TirInstr::Return(Some(expr))])
            }
            NirStmtKind::Let(decl) => self.visit_let(ctx, decl),
            NirStmtKind::Expr(expr) => {
                let e = self.get_expr(ctx, *expr)?;
                Ok(vec![TirInstr::Expr(e)])
            }
            _ => todo!(),
        }
    }

    fn visit_fundef(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirFunctionDef,
    ) -> Result<Vec<TirItem>, TcError> {
        assert!(input.generic_args.len() == 0);

        let scope = ctx.get_last_scope();
        let id = match scope.kind {
            ScopeKind::Function(fun_id, _) => fun_id,
            _ => unreachable!(),
        };

        let fun = ctx.ctx.interner.get_fun(id).clone();

        let params = fun
            .params
            .iter()
            .map(|param| {
                self.visit_type(ctx, param.ty).map(|ty| SCField {
                    name: param.name,
                    ty,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let return_ty = self.visit_type(ctx, fun.return_ty)?;

        let sig = Signature {
            name: input.name,
            params,
            return_ty,
            variadic: fun.variadic,
        };

        let body = match input.body.as_ref().map(|body| {
            body.iter()
                .map(|stmt| self.visit_stmt(ctx, stmt))
                .collect::<Result<Vec<_>, _>>()
        }) {
            Some(Ok(x)) => Ok(Some(x.into_iter().flatten().collect())),
            Some(Err(y)) => Err(y),
            None => Ok(None),
        }?;

        Ok(vec![TirItem::Fundef { sig, body }])
    }
}

impl<'ctx> Pass<'ctx, SurfaceResolutionPassOutput<'ctx>> for TirCtx {
    type Output = Vec<TirItem>;

    fn run(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: SurfaceResolutionPassOutput<'ctx>,
    ) -> Result<Self::Output, TcError> {
        let mut items = vec![];
        for (scope, item) in input {
            let mut tir_items = ctx.with_scope_id(scope, |ctx| {
                let nir = ctx.ctx.interner.get_item(item).clone();
                match nir {
                    NirItem::Function(fdef) => self.visit_fundef(ctx, &fdef),
                    NirItem::Alias(_, _) => Ok(vec![]),
                    _ => todo!(),
                }
            })?;
            items.append(&mut tir_items);
        }
        println!(
            "Items: [\n{}\n]",
            items
                .iter()
                .map(|x| format!("\n=> {:?}\n", x))
                .collect::<Vec<_>>()
                .join("\n")
        );
        Ok(items)
    }
}
