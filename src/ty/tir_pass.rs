use std::collections::HashMap;

use crate::{
    nir::{
        global_interner::{ExprId, TyId, TypeExprId},
        nir::{NirExprKind, NirFunctionDef, NirItem, NirLiteral, NirStmt, NirStmtKind},
    },
    ty::{
        PrimitiveTy, TcError,
        pass::Pass,
        scope::ScopeKind,
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
        todo!()
    }

    fn get_primitive_type(&mut self, ctx: &mut TyCtx<'ctx>, prim: PrimitiveTy) -> TyId {
        ctx.ctx
            .interner
            .insert_conc_type(ConcreteType::Primitive(prim))
    }

    fn get_type_of_expr(&mut self, ctx: &mut TyCtx<'ctx>, expr: ExprId) -> Result<TyId, TcError> {
        let expr = ctx.ctx.interner.get_expr(expr);
        match &expr.kind {
            NirExprKind::Literal(nir_literal) => match nir_literal {
                NirLiteral::IntLiteral(_) => Ok(self.get_primitive_type(ctx, PrimitiveTy::I64)),
                _ => todo!(),
            },
            _ => todo!(),
        }
    }

    fn get_expr_with_type(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
        ty: TyId,
    ) -> Result<TirExpr, TcError> {
        let expr_ty = self.get_type_of_expr(ctx, expr)?;
        if !self.type_is_coercible(ctx, expr_ty, ty) {
            return Err(TcError::Todo);
        }
        let expr = ctx.ctx.interner.get_expr(expr);
        let t = ctx.ctx.interner.get_conc_type(ty);

        match &expr.kind {
            NirExprKind::Literal(nir_literal) => match nir_literal {
                NirLiteral::IntLiteral(x) => Ok(TirExpr::TypedIntLit(match t {
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
                })),
                NirLiteral::FloatLiteral(_) => todo!(),
                NirLiteral::StringLiteral(_) => todo!(),
                NirLiteral::CharLiteral(_) => todo!(),
            },
            _ => todo!(),
        }
    }

    fn visit_stmt(&mut self, ctx: &mut TyCtx<'ctx>, input: &NirStmt) -> Result<TirInstr, TcError> {
        match &input.kind {
            NirStmtKind::Return { value } => {
                let void_ty = self.get_primitive_type(ctx, PrimitiveTy::Void);
                let return_ty = ctx.get_return_ty();
                let ret_id = return_ty.map_or(Ok(void_ty), |ty| self.visit_type(ctx, ty))?;

                if value.is_none() {
                    if ret_id != void_ty {
                        return Err(TcError::BadReturnType(void_ty, ret_id));
                    }
                    return Ok(TirInstr::Return(None));
                }
                let value = value.unwrap();
                let expr_ty = self.get_type_of_expr(ctx, value)?;

                if !self.type_is_coercible(ctx, expr_ty, ret_id) {
                    return Err(TcError::BadReturnType(expr_ty, ret_id));
                }
                let expr = self.get_expr_with_type(ctx, value, ret_id)?;
                Ok(TirInstr::Return(Some(expr)))
            }
            _ => todo!(),
        }
    }

    fn visit_fundef(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirFunctionDef,
    ) -> Result<TirItem, TcError> {
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
            Some(Ok(x)) => Ok(Some(x)),
            Some(Err(y)) => Err(y),
            None => Ok(None),
        }?;

        Ok(TirItem::Fundef { sig, body })
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
            let tir_item = ctx.with_scope_id(scope, |ctx| {
                let nir = ctx.ctx.interner.get_item(item).clone();
                match nir {
                    NirItem::Function(fdef) => self.visit_fundef(ctx, &fdef),
                    _ => todo!(),
                }
            })?;
            items.push(tir_item);
        }
        Ok(items)
    }
}
