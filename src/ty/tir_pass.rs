use std::collections::HashMap;

use strum::IntoEnumIterator;

use crate::{
    common::{
        global_interner::{
            DefId, ExprId, FunId, ImplBlockId, ItemId, ModuleId, SCId, ScopeId, Symbol, TirExprId,
            TyId, TypeExprId,
        },
        pass::Pass,
    },
    nir::{
        interner::ConstructibleId,
        nir::{
            FieldAccess, FieldAccessKind, NirBinOp, NirBinOpKind, NirCall, NirCalled, NirExprKind,
            NirFunctionDef, NirItem, NirLiteral, NirMethod, NirModuleDef, NirPattern,
            NirPatternKind, NirStmt, NirStmtKind, NirVarDecl,
        },
    },
    ty::{
        PrimitiveTy, TcError, TcFunProto, TcParam, TyCtx,
        displays::Displayable,
        scope::{Class, ClassMember, Definition, Method, ScopeKind, TypeExpr, VarDecl},
        surface_resolution::SurfaceResolutionPassOutput,
        tir::{
            ConcreteType, SCField, Signature, SpecializedClass, TirCtx, TirExpr, TirInstr,
            TypedIntLit,
        },
        type_checker::TypeChecker,
    },
};

#[derive(Debug)]
pub enum Receiver {
    Module(ModuleId),
    Object(TirExprId),
}

#[derive(Debug)]
pub enum TypeReceiver {
    Module(ModuleId),
    Object(TyId),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SpecInfo {
    pub def: DefId,
    pub args: Vec<TyId>,
}

impl TirCtx {
    pub fn new<'ctx>(ctx: &mut TyCtx<'ctx>) -> Self {
        let mut res = Self {
            methods: HashMap::new(),
            protos: HashMap::new(),
            impls: Self::get_all_impls(ctx),
            class_stack: vec![],
            specs: HashMap::new(),
        };
        PrimitiveTy::iter().for_each(|ty| {
            let x = res.create_type(ctx, ConcreteType::Primitive(ty));
            res.create_type(ctx, ConcreteType::Ptr(x));
        });

        res
    }

    // Note:
    // &self even though it is not used
    // because TirCtx needs to be constructed before
    // we have these concrete types. So needing to call
    // these methods from an instance instead of statically
    // ensures that they actually exist.

    pub fn primitive(&self, ctx: &TyCtx, prim: PrimitiveTy) -> TyId {
        ctx.ctx
            .interner
            .contains_conc_type(&ConcreteType::Primitive(prim))
            .unwrap()
    }

    pub fn primitive_ptr(&self, ctx: &TyCtx, prim: PrimitiveTy) -> TyId {
        ctx.ctx
            .interner
            .contains_conc_type(&ConcreteType::Ptr(self.primitive(ctx, prim)))
            .unwrap()
    }

    pub fn void_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::Void)
    }
    pub fn i8_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::I8)
    }
    pub fn i16_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::I16)
    }
    pub fn i32_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::I32)
    }
    pub fn i64_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::I64)
    }
    pub fn u8_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::U8)
    }
    pub fn u16_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::U16)
    }
    pub fn u32_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::U32)
    }
    pub fn u64_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::U64)
    }
    pub fn bool_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive(ctx, PrimitiveTy::Bool)
    }

    pub fn void_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::Void)
    }
    pub fn i8_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::I8)
    }
    pub fn i16_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::I16)
    }
    pub fn i32_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::I32)
    }
    pub fn i64_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::I64)
    }
    pub fn u8_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::U8)
    }
    pub fn u16_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::U16)
    }
    pub fn u32_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::U32)
    }
    pub fn u64_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::U64)
    }
    pub fn bool_ptr_ty(&self, ctx: &TyCtx) -> TyId {
        self.primitive_ptr(ctx, PrimitiveTy::Bool)
    }
}

impl<'ctx> TirCtx {
    pub fn get_all_impls(ctx: &TyCtx<'ctx>) -> Vec<ImplBlockId> {
        fn aux<'ctx>(ctx: &TyCtx<'ctx>, v: &mut Vec<ImplBlockId>, id: ScopeId) {
            let s = ctx.ctx.interner.get_scope(id);
            match &s.kind {
                ScopeKind::Impl(block_id, _) => {
                    v.push(*block_id);
                }
                ScopeKind::Global | ScopeKind::Module(_, _) => {
                    for child in s.children.clone() {
                        aux(ctx, v, child);
                    }
                }
                _ => (),
            }
        }
        let mut v = vec![];
        aux(ctx, &mut v, ScopeId::new(0));
        v
    }

    pub fn instantiate(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        template: DefId,
        args: &Vec<TypeExprId>,
    ) -> Result<TyId, TcError> {
        let spec_info = SpecInfo {
            def: template,
            args: args
                .iter()
                .map(|x| self.visit_type(ctx, *x))
                .collect::<Result<Vec<_>, _>>()?,
        };

        if self.specs.contains_key(&spec_info) {
            return Ok(self.specs[&spec_info]);
        }

        let class_id = {
            let def = ctx.ctx.interner.get_def(template);
            match def {
                Definition::Class(class_id) => *class_id,
                _ => unreachable!("{:?}", def),
            }
        };

        let Class {
            name,
            templates,
            members,
            methods,
        } = ctx.ctx.interner.get_class(class_id).clone();

        assert!(templates.len() == args.len());

        let c = SpecializedClass {
            original: template,
            name,
            fields: vec![],
            templates: spec_info.args.clone(),
            constructors: vec![],
            methods: vec![],
        };

        let sc_id = ctx.ctx.interner.insert_sc(c);

        let ty = ctx.with_scope(ScopeKind::Spec(sc_id), |ctx| {
            for (i, arg) in spec_info.args.iter().enumerate() {
                let te = ctx.ctx.interner.insert_type_expr(TypeExpr::Concrete(*arg));
                let def_id = ctx.ctx.interner.insert_def(Definition::Type(te));
                ctx.push_def(templates[i].name, def_id);
            }

            let fields = members
                .into_iter()
                .map(
                    |ClassMember {
                         name: field_name,
                         ty,
                     }| {
                        self.visit_type(ctx, ty).map(|ty| SCField {
                            name: field_name,
                            ty,
                        })
                    },
                )
                .try_collect()?;
            ctx.ctx.interner.get_sc_mut(sc_id).fields = fields;

            let ty = self.create_type(ctx, ConcreteType::SpecializedClass(sc_id));

            self.specs.insert(spec_info, ty);

            assert!(self.impls.len() == 0);

            self.class_stack.push(sc_id);
            self.methods.insert(ty, HashMap::new());

            for Method { id: method_id, .. } in &methods {
                if let Some(method_ast) = match ctx.ctx.interner.get_item(*method_id) {
                    NirItem::Method(ast) => (ast.name != name).then_some(ast.clone()),
                    _ => unreachable!(),
                } {
                    let fun_id = self.concretize_method(ctx, &method_ast)?;
                    ctx.ctx.interner.get_sc_mut(sc_id).methods.push(fun_id);
                } else {
                    let ast = match ctx.ctx.interner.get_item(*method_id) {
                        NirItem::Method(ast) => ast.clone(),
                        _ => unreachable!(),
                    };
                    let fun_id = self.concretize_constructor(ctx, &ast)?;
                    ctx.ctx.interner.get_sc_mut(sc_id).constructors.push(fun_id);
                }
            }

            for (i, Method { id: method_id, .. }) in methods.iter().enumerate() {
                if let Some(method_ast) = match ctx.ctx.interner.get_item(*method_id) {
                    NirItem::Method(ast) => (ast.name != name).then_some(ast.clone()),
                    _ => unreachable!(),
                } {
                    self.visit_method(ctx, &method_ast, *method_id)?;
                } else {
                    let ast = match ctx.ctx.interner.get_item(*method_id) {
                        NirItem::Method(ast) => ast.clone(),
                        _ => unreachable!(),
                    };
                    self.visit_constructor(
                        ctx,
                        &ast,
                        ctx.ctx.interner.get_sc(sc_id).constructors[i],
                        *method_id,
                    )?;
                }
            }
            Ok(ty)
        })?;

        self.class_stack.pop();

        Ok(ty)
    }

    pub fn visit_type(&mut self, ctx: &mut TyCtx<'ctx>, ty: TypeExprId) -> Result<TyId, TcError> {
        let te = ctx.ctx.interner.get_type_expr(ty).clone();
        match &te {
            TypeExpr::Template(name) => {
                let d = ctx.get_symbol_def(*name).ok_or_else(|| todo!())?;
                let def = ctx.ctx.interner.get_def(d);
                match &def {
                    Definition::Type(id) => self.visit_type(ctx, *id),
                    _ => todo!(),
                }
            }
            TypeExpr::Associated(_) => todo!(),
            TypeExpr::Instantiation { template, args } => self.instantiate(ctx, *template, args),
            TypeExpr::Ptr(id) => {
                let ty = ConcreteType::Ptr(self.visit_type(ctx, *id)?);
                Ok(self.create_type(ctx, ty))
            }
            TypeExpr::Tuple(ids) => {
                let tys = ids
                    .clone()
                    .iter()
                    .map(|id| self.visit_type(ctx, *id))
                    .collect::<Result<Vec<_>, _>>()?;
                let ty = ConcreteType::Tuple(tys);
                Ok(self.create_type(ctx, ty))
            }
            TypeExpr::Primitive(primitive_ty) => {
                let ty = ConcreteType::Primitive(*primitive_ty);
                Ok(self.create_type(ctx, ty))
            }
            TypeExpr::Concrete(id) => Ok(*id),
        }
    }

    pub fn type_is_coercible(&mut self, ctx: &mut TyCtx<'ctx>, src: TyId, target: TyId) -> bool {
        if src == target {
            return true;
        }
        let s = src.as_concrete(ctx);
        let t = target.as_concrete(ctx);
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

        if let ConcreteType::Tuple(srcs) = s
            && let ConcreteType::Tuple(trgts) = t
            && srcs.len() == trgts.len()
        {
            return srcs
                .clone()
                .iter()
                .zip(trgts.clone().iter())
                .all(|(src, target)| self.type_is_coercible(ctx, *src, *target));
        }

        if let ConcreteType::Ptr(_) = s
            && let ConcreteType::Ptr(_) = t
        {
            return true;
        }

        if let ConcreteType::SpecializedClass(class_id) = t {
            let args = match &s {
                ConcreteType::Tuple(ids) => ids.clone(),
                _ => vec![src],
            };

            // get constructors of specialized class
            // TODO: remove the clone and have cleaner interface with
            // not everything taking ctx as mut
            let cons = self.get_matching_constructor(ctx, args, *class_id);
            return cons.is_ok();
        }
        todo!(
            "Coerce {:?} into {:?} ?",
            src.to_string(ctx),
            target.to_string(ctx)
        )
    }

    pub fn get_matching_constructor(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        args: Vec<TyId>,
        target: SCId,
    ) -> Result<FunId, TcError> {
        target
            .get_matching_constructor(self, ctx, &args[..])
            .ok_or_else(|| {
                TcError::Text(format!(
                    "Cannot find matching constructor for {} from ({})",
                    target.to_string(ctx),
                    args.iter().to_string(ctx),
                ))
            })
    }

    pub fn create_expr(&mut self, ctx: &mut TyCtx<'ctx>, expr: TirExpr, defer: bool) -> TirExprId {
        let e = ctx.ctx.interner.insert_te(expr.clone());
        ctx.push_instr(TirInstr::Calculate(e), defer);
        e
    }

    pub fn get_primitive_type(&mut self, ctx: &mut TyCtx<'ctx>, prim: PrimitiveTy) -> TyId {
        self.create_type(ctx, ConcreteType::Primitive(prim))
    }

    pub fn get_type_of_tir_expr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr_id: TirExprId,
    ) -> Result<TyId, TcError> {
        let expr = ctx.ctx.interner.get_te(expr_id).clone();
        match expr {
            TirExpr::TypedIntLit(x) => match x {
                TypedIntLit::Ptr(id, _) => {
                    let ty = ConcreteType::Ptr(id);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::I8(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I8);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::I16(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I16);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::I32(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I32);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::I64(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::I64);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::U8(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U8);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::U16(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U16);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::U32(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U32);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::U64(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::U64);
                    Ok(self.create_type(ctx, ty))
                }
                TypedIntLit::Bool(_) => {
                    let ty = ConcreteType::Primitive(PrimitiveTy::Bool);
                    Ok(self.create_type(ctx, ty))
                }
            },
            TirExpr::Access(var, field_access_kind) => {
                let ty = self.get_type_of_tir_expr(ctx, var)?;
                self.get_access_ty(ctx, ty, &field_access_kind)
            }
            TirExpr::IntCast(id, _) => Ok(id),
            TirExpr::Tuple(ids) => {
                let ty = ConcreteType::Tuple(
                    ids.iter()
                        .map(|x| self.get_type_of_tir_expr(ctx, *x))
                        .collect::<Result<Vec<_>, _>>()?,
                );
                Ok(self.create_type(ctx, ty))
            }
            TirExpr::BinOp { lhs, op, rhs } => match op {
                NirBinOpKind::Equ
                | NirBinOpKind::Dif
                | NirBinOpKind::Geq
                | NirBinOpKind::Leq
                | NirBinOpKind::Gt
                | NirBinOpKind::Lt
                | NirBinOpKind::LOr
                | NirBinOpKind::LAnd => Ok(self.get_primitive_type(ctx, PrimitiveTy::Bool)),

                _ => {
                    let lt = self.get_type_of_tir_expr(ctx, lhs)?;
                    let rt = self.get_type_of_tir_expr(ctx, rhs)?;
                    if lt.as_ptr(ctx).is_some() {
                        Ok(lt)
                    } else if rt.as_ptr(ctx).is_some() {
                        Ok(rt)
                    } else {
                        Ok(self.get_type_of_tir_expr(ctx, lhs)?)
                    }
                }
            },
            TirExpr::Arg(i) => {
                let fun_id = ctx.get_current_fun().unwrap();
                let proto = &self.protos[&fun_id];
                Ok(proto.params[i].ty)
            }
            TirExpr::Funcall(fun_id, _) => Ok(self.protos[&fun_id].return_ty),
            TirExpr::PtrCast(id, _) => Ok(self.get_ptr_to(ctx, id)),
            TirExpr::StringLiteral(_) => {
                let ty = self.get_primitive_type(ctx, PrimitiveTy::U8);
                Ok(self.get_ptr_to(ctx, ty))
            }
            TirExpr::True | TirExpr::False => Ok(self.get_primitive_type(ctx, PrimitiveTy::Bool)),
            TirExpr::PtrAccess(expr, FieldAccessKind::Symbol(field_name)) => {
                let t = self.get_type_of_tir_expr(ctx, expr).unwrap();
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
                    Ok(self.create_type(ctx, ConcreteType::Ptr(field.ty)))
                } else {
                    return Err(TcError::Text(format!(
                        "No named field in non-class type (get_type_of_tir_expr)",
                    )));
                }
            }
            TirExpr::PtrAccess(expr, FieldAccessKind::Index(i)) => {
                let t = self.get_type_of_tir_expr(ctx, expr).unwrap();
                let mut ty = t.as_concrete(ctx);
                if let ConcreteType::Ptr(x) = ty {
                    ty = x.as_concrete(ctx);
                }
                if let ConcreteType::Tuple(ids) = ty {
                    if ids.len() <= i as usize {
                        return Err(TcError::Text(format!("Tuple access out of range")));
                    }
                    Ok(self.create_type(ctx, ConcreteType::Ptr(ids[i as usize])))
                } else {
                    return Err(TcError::Text(format!("No index field in non-tuple type")));
                }
            }
            TirExpr::VarPtr(id) => {
                let inner = ctx.ctx.interner.get_variable(id).ty;
                Ok(self.create_type(ctx, ConcreteType::Ptr(inner)))
            }
            TirExpr::Deref(e) => Ok(self.get_type_of_tir_expr(ctx, e)?.as_ptr(ctx).unwrap()),
            TirExpr::Malloc(ty) | TirExpr::Alloca(ty) => {
                Ok(self.create_type(ctx, ConcreteType::Ptr(ty)))
            }
            TirExpr::Subscript { ptr, .. } => self.get_type_of_tir_expr(ctx, ptr),
        }
    }

    pub fn get_access_ty(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        ty: TyId,
        access: &FieldAccessKind,
    ) -> Result<TyId, TcError> {
        let t = (ty).as_concrete(ctx);

        match access {
            FieldAccessKind::Symbol(name) => {
                let mut ty = (ty).as_concrete(ctx);
                if let ConcreteType::Ptr(inner) = ty {
                    ty = (*inner).as_concrete(ctx);
                };
                if let ConcreteType::SpecializedClass(sc_id) = ty {
                    let sc = ctx.ctx.interner.get_sc(*sc_id);
                    for f in &sc.fields {
                        if f.name == *name {
                            return Ok(f.ty);
                        }
                    }
                    return Err(TcError::Text(format!(
                        "Field named ??? not found in class ???"
                    )));
                } else {
                    return Err(TcError::Text(format!(
                        "No named field in non-class type (get-access)",
                    )));
                }
            }
            FieldAccessKind::Index(i) => {
                if let ConcreteType::Tuple(tys) = t {
                    if tys.len() < *i as usize {
                        return Err(TcError::Text(format!("Tuple access out of range")));
                    }
                    Ok(tys[*i as usize])
                } else {
                    return Err(TcError::Text(format!("No integer field in non-tuple type")));
                }
            }
        }
    }

    pub fn get_ptr_to(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> TyId {
        self.create_type(ctx, ConcreteType::Ptr(ty))
    }

    pub fn get_type_of_expr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr_id: ExprId,
    ) -> Result<TyId, TcError> {
        TypeChecker::get_type_of_expr(self, ctx, expr_id)
    }

    pub fn expr_as_module(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
    ) -> Result<ModuleId, TcError> {
        let nir = ctx.ctx.interner.get_expr(expr).clone();
        match &nir.kind {
            NirExprKind::Access {
                from,
                field:
                    FieldAccess {
                        kind: FieldAccessKind::Symbol(field),
                        ..
                    },
            } => {
                let from_module = self.expr_as_module(ctx, *from)?;
                let m = ctx.ctx.interner.get_module(from_module);
                let scope = m.scope.clone();
                let def_id = ctx.get_symbol_def_in_scope(scope, *field);

                if def_id.is_none() {
                    return Err(TcError::NameNotFound(*field));
                }

                let def_id = def_id.unwrap();

                let def = ctx.ctx.interner.get_def(def_id);

                match &def {
                    Definition::Module(id) => Ok(*id),
                    _ => Err(TcError::NotAModule(expr)),
                }
            }
            NirExprKind::Named(name) => {
                let def_id = ctx.get_symbol_def(*name);

                if def_id.is_none() {
                    return Err(TcError::NameNotFound(*name));
                }

                let def_id = def_id.unwrap();

                let def = ctx.ctx.interner.get_def(def_id);

                match &def {
                    Definition::Module(id) => Ok(*id),
                    _ => Err(TcError::NotAModule(expr)),
                }
            }
            _ => Err(TcError::NotAModule(expr)),
        }
    }

    pub fn expr_as_receiver(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
        defer: bool,
    ) -> Result<Receiver, TcError> {
        if let Ok(id) = self.expr_as_module(ctx, expr) {
            return Ok(Receiver::Module(id));
        }
        self.get_expr_ptr(ctx, expr, defer).map(Receiver::Object)
    }

    pub fn expr_ty_as_receiver(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
    ) -> Result<TypeReceiver, TcError> {
        if let Ok(id) = self.expr_as_module(ctx, expr) {
            return Ok(TypeReceiver::Module(id));
        }
        self.get_type_of_expr(ctx, expr).map(TypeReceiver::Object)
    }

    pub fn arg_len_mismatch(src: usize, target: usize, variadic: bool) -> bool {
        if variadic {
            src < target
        } else {
            src != target
        }
    }

    pub fn get_fun_id_from_symbol(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        s: Symbol,
    ) -> Result<FunId, TcError> {
        let function = ctx.get_symbol_def(s);
        if function.is_none() {
            return Err(TcError::NameNotFound(s));
        }
        let def = ctx.ctx.interner.get_def(function.unwrap());
        match def {
            Definition::Function(id) => Ok(*id),
            _ => Err(TcError::NameNotFound(s)),
        }
    }

    pub fn get_type_size(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> usize {
        let t = (ty).as_concrete(ctx);
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

    pub fn get_expr_with_type(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
        ty: TyId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        // let original_expr = expr;
        let expr_ty = self.get_type_of_expr(ctx, expr)?;
        if !self.type_is_coercible(ctx, expr_ty, ty) {
            return Err(TcError::Text(format!(
                "Types `{}` cannot be coerced to type `{}`",
                expr_ty.to_string(ctx),
                ty.to_string(ctx)
            )));
        }
        let expr = ctx.ctx.interner.get_expr(expr).clone();
        let t = (ty).as_concrete(ctx);

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
                    Ok(self.create_expr(ctx, e, defer))
                }
                NirLiteral::FloatLiteral(_) => todo!(),
                NirLiteral::StringLiteral(x) => {
                    if let ConcreteType::Ptr(inner) = t {
                        let inner = inner.clone();
                        if inner == self.get_primitive_type(ctx, PrimitiveTy::U8) {
                            Ok(self.create_expr(ctx, TirExpr::StringLiteral(*x), defer))
                        } else {
                            let e = self.create_expr(ctx, TirExpr::StringLiteral(*x), defer);
                            Ok(self.create_expr(ctx, TirExpr::PtrCast(inner, e), defer))
                        }
                    } else {
                        todo!()
                    }
                }
                NirLiteral::CharLiteral(c) => {
                    assert!(ty.is_integer(ctx));
                    let e = self.create_expr(
                        ctx,
                        TirExpr::TypedIntLit(TypedIntLit::U8(c.to_string().as_bytes()[0])),
                        defer,
                    );
                    if !matches!(ty.as_primitive(ctx), Some(PrimitiveTy::U8)) {
                        return Ok(self.create_expr(ctx, TirExpr::IntCast(ty.clone(), e), defer));
                    }
                    Ok(e)
                }
                NirLiteral::BoolLiteral(b) => {
                    let res = self.create_expr(
                        ctx,
                        match b {
                            true => TirExpr::True,
                            false => TirExpr::False,
                        },
                        defer,
                    );
                    if ty == self.bool_ty(ctx) {
                        Ok(res)
                    } else {
                        todo!()
                    }
                }
            },
            NirExprKind::Named(name) => {
                if *name == ctx.ctx.interner.insert_symbol(&"true".to_string())
                    || *name == ctx.ctx.interner.insert_symbol(&"false".to_string())
                {
                    let expr = if *name == ctx.ctx.interner.insert_symbol(&"true".to_string()) {
                        TirExpr::True
                    } else {
                        TirExpr::False
                    };
                    let e = self.create_expr(ctx, expr, defer);
                    let bool_ty = self.get_primitive_type(ctx, PrimitiveTy::Bool);
                    if ty == bool_ty {
                        return Ok(e);
                    } else if ty.is_integer(ctx) {
                        return Ok(self.create_expr(ctx, TirExpr::IntCast(ty, e), defer));
                    } else {
                        todo!()
                    }
                } else {
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
                        let ptr = self.create_expr(ctx, TirExpr::VarPtr(var_id), defer);
                        return Ok(self.create_expr(ctx, TirExpr::Deref(ptr), defer));
                    }
                    if !self.type_is_coercible(ctx, var.ty, ty) {
                        return Err(dbg!(TcError::Text(format!("Types are not coercible !"))));
                    }
                    if var.ty.as_ptr(ctx).is_some() && ty.as_ptr(ctx).is_some() {
                        let var_ptr = self.create_expr(ctx, TirExpr::VarPtr(var_id), defer);
                        let var_expr = self.create_expr(ctx, TirExpr::Deref(var_ptr), defer);
                        return Ok(self.create_expr(ctx, TirExpr::PtrCast(ty, var_expr), defer));
                    }

                    if var.ty.is_integer(ctx) && ty.is_integer(ctx) {
                        let var_ptr = self.create_expr(ctx, TirExpr::VarPtr(var_id), defer);
                        let var_expr = self.create_expr(ctx, TirExpr::Deref(var_ptr), defer);
                        return Ok(dbg!(self.create_expr(
                            ctx,
                            TirExpr::IntCast(ty, var_expr),
                            defer
                        )));
                    }
                }
                return Err(TcError::Text(format!("Coerce non integer types !")));
            }
            NirExprKind::Tuple(exprs) => {
                if let ConcreteType::Tuple(types) = t {
                    if exprs.len() != types.len() {
                        return Err(TcError::Text(format!("Coerce tuple to tuple of != size")));
                    }

                    let tuple = TirExpr::Tuple(
                        exprs
                            .clone()
                            .iter()
                            .zip(types.clone().iter())
                            .map(|(e, t)| self.get_expr_with_type(ctx, *e, *t, defer))
                            .collect::<Result<Vec<_>, _>>()?,
                    );
                    Ok(self.create_expr(ctx, tuple, defer))
                } else {
                    return Err(TcError::Text(format!("Coerce tuple into non tuple")));
                }
            }
            NirExprKind::Access { from, field } => {
                let left = self.get_expr(ctx, *from, defer)?;
                self.get_access(ctx, left, field.kind, defer)
            }
            NirExprKind::BinOp(NirBinOp { op, left, right }) => {
                let lt = self.get_type_of_expr(ctx, *left)?;
                let rt = self.get_type_of_expr(ctx, *right)?;
                if !lt.is_integer(ctx) || !rt.is_integer(ctx) {
                    return Err(TcError::Text(format!(
                        "Cannot use binop with non-integer types"
                    )));
                }
                let lt_size = self.get_type_size(ctx, lt);
                let rt_size = self.get_type_size(ctx, rt);

                let (lt, rt) = if lt.as_ptr(ctx).is_some() {
                    (lt, self.get_primitive_type(ctx, PrimitiveTy::I64))
                } else if rt.as_ptr(ctx).is_some() {
                    (self.get_primitive_type(ctx, PrimitiveTy::I64), rt)
                } else if lt.is_integer(ctx) && rt.is_integer(ctx) {
                    if lt_size > rt_size {
                        (lt, lt)
                    } else {
                        (rt, rt)
                    }
                } else {
                    (lt, rt)
                };

                let value_type = if matches!(op, NirBinOpKind::LOr | NirBinOpKind::LAnd) {
                    self.get_primitive_type(ctx, PrimitiveTy::Bool)
                } else if lt.as_ptr(ctx).is_some() {
                    lt
                } else if rt.as_ptr(ctx).is_some() {
                    rt
                } else if lt_size > rt_size {
                    lt
                } else {
                    rt
                };

                let lhs = self.get_expr_with_type(ctx, *left, lt, defer)?;
                let rhs = self.get_expr_with_type(ctx, *right, rt, defer)?;
                let e = self.create_expr(ctx, TirExpr::BinOp { lhs, rhs, op: *op }, defer);

                Ok({
                    if value_type != ty {
                        self.create_expr(ctx, TirExpr::IntCast(ty, e), defer)
                    } else {
                        e
                    }
                })
            }
            NirExprKind::Call(NirCall {
                called,
                generic_args,
                args,
                ..
            }) => {
                assert!(generic_args.len() == 0);

                let (f_id, self_arg): (FunId, Option<TirExprId>) =
                    self.get_fun_id_and_self_arg(ctx, called, defer)?;

                let sig = self.protos[&f_id].clone();

                if Self::arg_len_mismatch(
                    args.len()
                        + match self_arg {
                            None => 0,
                            Some(_) => 1,
                        },
                    sig.params.len(),
                    sig.variadic,
                ) {
                    return Err(TcError::Text(format!("Arg len mismatch in function call")));
                }

                let mut params = sig
                    .params
                    .iter()
                    .skip(match self_arg {
                        None => 0,
                        Some(_) => 1,
                    })
                    .map(|x| Some(x.clone()))
                    .collect::<Vec<_>>();
                for _ in params.len()..args.len() {
                    params.push(None)
                }

                let mut args = args
                    .iter()
                    .zip(params.into_iter())
                    .map(|(expr, param)| {
                        if param.is_some() {
                            self.get_expr_with_type(ctx, *expr, param.unwrap().ty, defer)
                        } else {
                            self.get_expr(ctx, *expr, defer)
                        }
                    })
                    .try_collect::<Vec<_>>()?;

                self_arg.iter().for_each(|x| args.insert(0, *x));
                // args.insert(0, self_arg);

                Ok(self.create_expr(ctx, TirExpr::Funcall(f_id, args), defer))
            }
            NirExprKind::As {
                ty: as_ty,
                expr: inner_expr,
            } => {
                let te = ctx.visit_type(as_ty)?;
                let src = self.visit_type(ctx, te)?;
                if src != ty {
                    todo!("Recast @as expr")
                }

                let nir = ctx.ctx.interner.get_expr(*inner_expr).clone();

                let args = match &nir.kind {
                    NirExprKind::Tuple(ids) => ids
                        .iter()
                        .map(|x| self.get_type_of_expr(ctx, *x))
                        .collect::<Result<Vec<_>, _>>()?,
                    _ => vec![self.get_type_of_expr(ctx, *inner_expr)?],
                };

                if !matches!((src).as_concrete(ctx), ConcreteType::SpecializedClass(_)) {
                    return self.get_expr_with_type(ctx, *inner_expr, src, defer);
                }

                let sc_id = match (src).as_concrete(ctx) {
                    ConcreteType::SpecializedClass(id) => *id,
                    _ => {
                        return self.get_expr_with_type(ctx, *inner_expr, src, defer);
                    }
                };

                let cons = self.get_matching_constructor(ctx, args, sc_id)?;
                let ptr = self.create_expr(ctx, TirExpr::Alloca(src), defer);
                let mut args = vec![ptr];

                match nir.kind {
                    NirExprKind::Tuple(ids) => ids
                        .iter()
                        .enumerate()
                        .map(|(i, x)| {
                            let fun = ctx.ctx.interner.get_fun(cons);
                            let ty = fun.params[i + 1].ty;
                            let ty = self.visit_type(ctx, ty)?;
                            self.get_expr_with_type(ctx, *x, ty, defer)
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                    _ => {
                        let fun = ctx.ctx.interner.get_fun(cons);
                        let ty = fun.params[1].ty;
                        let ty = self.visit_type(ctx, ty)?;
                        vec![self.get_expr_with_type(ctx, *inner_expr, ty, defer)?]
                    }
                }
                .into_iter()
                .for_each(|x| args.push(x));

                // call the constructor
                self.create_expr(ctx, TirExpr::Funcall(cons, args), defer);

                // return the loaded ptr
                Ok(self.create_expr(ctx, TirExpr::Deref(ptr), defer))
            }
            NirExprKind::SizeOf(ty) => {
                let te = ctx.visit_type(ty)?;
                let ty = self.visit_type(ctx, te)?;
                let size = self.get_type_size(ctx, ty);

                Ok(self.create_expr(
                    ctx,
                    TirExpr::TypedIntLit(TypedIntLit::U64(size as u64)),
                    defer,
                ))
            }
            NirExprKind::Deref(x) => {
                let ptr = self.get_expr(ctx, *x, defer)?;
                // TODO: coerce types maybe
                Ok(self.create_expr(ctx, TirExpr::Deref(ptr), defer))
            }
            NirExprKind::Subscript { value, index } => {
                assert!(
                    self.get_type_of_expr(ctx, *value)
                        .unwrap()
                        .as_ptr(ctx)
                        .unwrap()
                        == ty
                );
                let value = self.get_expr(ctx, *value, defer)?;
                let index = self.get_expr(ctx, *index, defer)?;
                let ptr = self.create_expr(ctx, TirExpr::Subscript { ptr: value, index }, defer);
                let e = self.create_expr(ctx, TirExpr::Deref(ptr), defer);
                Ok(e)
            }
            x => todo!("{x:?}"),
        }
    }

    pub fn get_fun_id_and_self_ty(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        called: &NirCalled,
    ) -> Result<(FunId, Option<TyId>), TcError> {
        if called.receiver.is_some() {
            let receiver = self.expr_ty_as_receiver(ctx, called.receiver.unwrap())?;
            match receiver {
                TypeReceiver::Module(id) => {
                    let m = ctx.ctx.interner.get_module(id);
                    let s = m.scope;
                    let def_id = ctx.get_symbol_def_in_scope(s, called.called);
                    if def_id.is_none() {
                        return Err(TcError::Text(format!("No such function in module")));
                    }
                    let def_id = def_id.unwrap();
                    let def = ctx.ctx.interner.get_def(def_id);
                    match &def {
                        Definition::Function(fun_id) => {
                            return Ok((*fun_id, None));
                        }
                        _ => {
                            return Err(TcError::Text(format!("No such function in module")));
                        }
                    }
                }
                TypeReceiver::Object(t) => {
                    let inner = t.as_ptr(ctx).unwrap_or(t);
                    let methods = &self.methods[&inner].clone();
                    if !methods.contains_key(&called.called) {
                        if let Some(inner_inner) = inner.as_ptr(ctx) {
                            let methods = &self.methods[&inner_inner].clone();
                            if methods.contains_key(&called.called) {
                                return Ok((methods[&called.called], Some(t)));
                            }
                        }
                        return Err(TcError::Text(format!(
                            "No method named {:?} in class {:?}",
                            called.called, inner
                        )));
                    }
                    return Ok((methods[&called.called], Some(t)));
                }
            }
        }
        return Ok((self.get_fun_id_from_symbol(ctx, called.called)?, None));
    }

    fn get_fun_id_and_self_arg(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        called: &NirCalled,
        defer: bool,
    ) -> Result<(FunId, Option<TirExprId>), TcError> {
        if called.receiver.is_some() {
            let receiver = self.expr_as_receiver(ctx, called.receiver.unwrap(), defer)?;
            match receiver {
                Receiver::Module(id) => {
                    let m = ctx.ctx.interner.get_module(id);
                    let s = m.scope;
                    let def_id = ctx.get_symbol_def_in_scope(s, called.called);
                    if def_id.is_none() {
                        return Err(TcError::Text(format!(
                            "No such function {:?} in module",
                            called.called
                        )));
                    }
                    let def_id = def_id.unwrap();
                    let def = ctx.ctx.interner.get_def(def_id);
                    match &def {
                        Definition::Function(fun_id) => {
                            return Ok((*fun_id, None));
                        }
                        _ => {
                            return Err(TcError::Text(format!(
                                "No such function {:?} in module {:?}",
                                called.called, m.name
                            )));
                        }
                    }
                }
                Receiver::Object(x) => {
                    let t = self.get_type_of_tir_expr(ctx, x)?;
                    let inner = t.as_ptr(ctx).unwrap();
                    let methods = &self.methods[&inner].clone();
                    if !methods.contains_key(&called.called) {
                        if let Some(inner_inner) = inner.as_ptr(ctx) {
                            let methods = &self.methods[&inner_inner].clone();
                            if methods.contains_key(&called.called) {
                                return Ok((methods[&called.called], Some(x)));
                            }
                        }
                        return Err(TcError::Text(format!(
                            "No method {:?} in class {:?} (get_expr_with_type)",
                            called.called, inner
                        )));
                    }
                    return Ok((methods[&called.called], Some(x)));
                }
            }
        }
        Ok((self.get_fun_id_from_symbol(ctx, called.called)?, None))
    }

    pub fn get_access(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: TirExprId,
        access: FieldAccessKind,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        match access {
            FieldAccessKind::Symbol(name) => {
                let t = self.get_type_of_tir_expr(ctx, expr)?;
                let mut ty = t.as_concrete(ctx);
                if let ConcreteType::Ptr(inner) = ty {
                    ty = (*inner).as_concrete(ctx);
                };
                if let ConcreteType::SpecializedClass(sc_id) = ty {
                    let sc = ctx.ctx.interner.get_sc(*sc_id);
                    for f in &sc.fields {
                        if f.name == name {
                            return Ok(self.create_expr(ctx, TirExpr::Access(expr, access), defer));
                        }
                    }
                    return Err(TcError::Text(format!(
                        "Field named {:?} not found in class {:?}",
                        name, sc.name
                    )));
                } else {
                    return Err(TcError::Text(format!(
                        "No named field in non-class type (get-access)",
                    )));
                }
            }
            FieldAccessKind::Index(i) => {
                let ty = self.get_type_of_tir_expr(ctx, expr)?;
                let t = (ty).as_concrete(ctx);
                if let ConcreteType::Tuple(tys) = t {
                    if tys.len() <= i as usize {
                        return Err(TcError::Text(format!("Tuple access out of range")));
                    }
                    Ok(self.create_expr(ctx, TirExpr::Access(expr, access), defer))
                } else {
                    return Err(TcError::Text(format!("No integer field in non-tuple type")));
                }
            }
        }
    }

    pub fn get_expr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let ty = self.get_type_of_expr(ctx, expr)?;
        self.get_expr_with_type(ctx, expr, ty, defer)
    }

    pub fn declare_pattern(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirPattern,
        ty: TyId,
        expr: Option<TirExprId>,
    ) -> Result<(), TcError> {
        match &input.kind {
            NirPatternKind::Wildcard => Ok(()),
            NirPatternKind::Symbol(symb) => {
                let id = ctx
                    .ctx
                    .interner
                    .insert_variable(VarDecl { name: *symb, ty });
                let d = ctx.ctx.interner.insert_def(Definition::Var(id));
                ctx.push_instr(TirInstr::VarDecl(id), false);
                ctx.push_def(*symb, d);
                expr.iter()
                    .for_each(|x| ctx.push_instr(TirInstr::VarAssign(id, *x), false));
                Ok(())
            }
            NirPatternKind::Tuple(nirs) => {
                let t = (ty).as_concrete(ctx);
                if !matches!(t, ConcreteType::Tuple(_)) {
                    return Err(TcError::Text(format!(
                        "Tried to declare tuple variable with non tuple type",
                    )));
                }

                let tys = match t {
                    ConcreteType::Tuple(tys) => tys.clone(),
                    _ => unreachable!(),
                };

                if tys.len() != nirs.len() {
                    return Err(TcError::Text(format!("Coerce tuple to tuple of != size")));
                }

                nirs.iter()
                    .zip(tys.iter())
                    .enumerate()
                    .try_for_each(|(i, (x, ty))| {
                        let expr = expr.map(|e| {
                            self.create_expr(
                                ctx,
                                TirExpr::Access(e, FieldAccessKind::Index(i as u32)),
                                false,
                            )
                        });
                        self.declare_pattern(ctx, x, *ty, expr)
                    })
            }
        }
    }

    pub fn visit_let(&mut self, ctx: &mut TyCtx<'ctx>, input: &NirVarDecl) -> Result<(), TcError> {
        if input.ty.is_none() && input.value.is_none() {
            return Err(TcError::Text(format!(
                "Type inference for variable is not availaible yet",
            )));
        }

        let ty = match input.ty.as_ref() {
            Some(ty) => {
                let ty_id = ctx.visit_type(ty)?;
                self.visit_type(ctx, ty_id)?
            }
            None => self.get_type_of_expr(ctx, input.value.unwrap())?,
        };

        let expr = match input.value.as_ref() {
            Some(e) => Some(self.get_expr_with_type(ctx, *e, ty, false)?),
            None => None,
        };
        self.declare_pattern(ctx, &input.pattern, ty, expr)
    }

    pub fn visit_stmt(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirStmt,
        defer: bool,
    ) -> Result<(), TcError> {
        match &input.kind {
            NirStmtKind::Return { value } => {
                ctx.push_all_deferred();

                let void_ty = self.get_primitive_type(ctx, PrimitiveTy::Void);
                let return_ty = ctx.get_return_ty();
                let ret_id = return_ty.map_or(Ok(void_ty), |ty| self.visit_type(ctx, ty))?;

                if value.is_none() {
                    if ret_id != void_ty {
                        return Err(TcError::BadReturnType(void_ty, ret_id));
                    }
                    ctx.push_instr(TirInstr::Return(None), defer);
                    return Ok(());
                }
                let value = value.unwrap();
                let expr_ty = self.get_type_of_expr(ctx, value)?;

                if !self.type_is_coercible(ctx, expr_ty, ret_id) {
                    return Err(TcError::BadReturnType(expr_ty, ret_id));
                }
                let expr = self.get_expr_with_type(ctx, value, ret_id, defer)?;
                ctx.push_instr(TirInstr::Return(Some(expr)), defer);
                Ok(())
            }
            NirStmtKind::Let(decl) => self.visit_let(ctx, decl),
            NirStmtKind::Expr(expr) => {
                self.get_expr(ctx, *expr, defer)?;
                Ok(())
            }
            NirStmtKind::If {
                cond,
                then_block,
                else_block,
            } => {
                let bool_ty = self.get_primitive_type(ctx, PrimitiveTy::Bool);
                let cond_val = self.get_expr_with_type(ctx, *cond, bool_ty, defer)?;
                let if_scope = {
                    let mut if_scope = None;
                    ctx.with_scope(ScopeKind::If { cond: cond_val }, |ctx| {
                        if_scope = Some(ctx.current_scope);
                        ctx.with_scope(ScopeKind::Then(vec![]), |ctx| {
                            self.visit_stmt(ctx, then_block, defer)
                        })?;
                        if let Some(eblock) = else_block {
                            ctx.with_scope(ScopeKind::Else(vec![]), |ctx| {
                                self.visit_stmt(ctx, eblock, defer)
                            })
                        } else {
                            Ok(())
                        }
                    })?;
                    if_scope.unwrap()
                };
                ctx.push_instr(TirInstr::If(if_scope), defer);
                Ok(())
            }
            NirStmtKind::Block(stmts) => {
                let blk = {
                    let mut blk = None;
                    ctx.with_scope(ScopeKind::Block(vec![]), |ctx| {
                        blk = Some(ctx.current_scope);
                        stmts
                            .iter()
                            .try_for_each(|stmt| self.visit_stmt(ctx, stmt, defer))
                    })?;
                    blk.unwrap()
                };
                ctx.push_instr(TirInstr::Block(blk), defer);
                Ok(())
            }
            NirStmtKind::While { cond, body } => {
                let bool_ty = self.get_primitive_type(ctx, PrimitiveTy::Bool);
                let while_scope = {
                    let mut while_scope = None;
                    ctx.with_scope(ScopeKind::While, |ctx| {
                        while_scope = Some(ctx.current_scope);
                        let e = ctx.with_scope(ScopeKind::WhileCond(vec![]), |ctx| {
                            self.get_expr_with_type(ctx, *cond, bool_ty, defer)
                        })?;
                        ctx.with_scope(ScopeKind::WhileLoop(e, vec![]), |ctx| {
                            self.visit_stmt(ctx, body, defer)
                        })
                    })?;
                    while_scope.unwrap()
                };
                ctx.push_instr(TirInstr::While(while_scope), defer);
                Ok(())
            }
            NirStmtKind::Assign { assigned, value } => {
                let ty = self.get_type_of_expr(ctx, *assigned)?;
                let rval = self.get_expr_with_type(ctx, *value, ty, defer)?;
                self.visit_assign(ctx, *assigned, rval, defer)
            }
            NirStmtKind::Defer(stmt) => {
                let res = self.visit_stmt(ctx, stmt, true)?;
                ctx.defer_stack.last_mut().unwrap().push(vec![]);
                Ok(res)
            }
            x => todo!("{:?}", x),
        }
    }

    pub fn get_expr_ptr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
        defer: bool,
    ) -> Result<TirExprId, TcError> {
        let e = ctx.ctx.interner.get_expr(expr).clone();
        match &e.kind {
            NirExprKind::Named(name) => {
                if *name == ctx.ctx.interner.insert_symbol(&"true".to_string())
                    || *name == ctx.ctx.interner.insert_symbol(&"false".to_string())
                {
                    return Err(TcError::Text(format!("Invalid LValue")));
                }
                let name = name.clone();
                let def = ctx.get_symbol_def(name);
                if def.is_none() {
                    return Err(TcError::NameNotFound(name));
                }
                let def = ctx.ctx.interner.get_def(def.unwrap()).clone();
                match def {
                    Definition::Var(id) => {
                        let lval = self.create_expr(ctx, TirExpr::VarPtr(id), defer);
                        Ok(lval)
                    }
                    _ => todo!(),
                }
            }
            NirExprKind::Access { from, field } => {
                let from_expr = self.get_expr_ptr(ctx, *from, defer)?;
                let lval = self.create_expr(ctx, TirExpr::PtrAccess(from_expr, field.kind), defer);
                Ok(lval)
            }
            NirExprKind::Deref(e) => {
                let e = self.get_expr(ctx, *e, defer)?;
                Ok(e)
            }
            NirExprKind::Subscript { value, index } => {
                let index = self.get_expr(ctx, *index, defer)?;
                let ptr = self.get_expr(ctx, *value, defer)?;
                let e = self.create_expr(ctx, TirExpr::Subscript { ptr, index }, defer);
                Ok(e)
            }
            _ => todo!(),
        }
    }

    pub fn visit_assign(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        assigned: ExprId,
        rval: TirExprId,
        defer: bool,
    ) -> Result<(), TcError> {
        let e = ctx.ctx.interner.get_expr(assigned).clone();
        match &e.kind {
            NirExprKind::Tuple(exprs) => {
                for (i, expr) in exprs.iter().enumerate() {
                    let rval_i = self.create_expr(
                        ctx,
                        TirExpr::Access(rval, FieldAccessKind::Index(i as u32)),
                        defer,
                    );
                    self.visit_assign(ctx, *expr, rval_i, defer)?;
                }
                Ok(())
            }
            _ => {
                let expr_ptr = self.get_expr_ptr(ctx, assigned, defer)?;
                ctx.push_instr(TirInstr::Assign(expr_ptr, rval), defer);
                Ok(())
            }
        }
    }

    pub fn concretize_fun_proto(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        id: FunId,
    ) -> Result<(), TcError> {
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
            name: fun.name,
            params,
            return_ty,
            variadic: fun.variadic,
        };

        self.protos.insert(id, sig);

        Ok(())
    }

    pub fn create_type(&mut self, ctx: &mut TyCtx<'ctx>, ty: ConcreteType) -> TyId {
        let res = ctx.ctx.interner.insert_conc_type(ty);
        if !self.methods.contains_key(&res) {
            self.methods.insert(res, HashMap::new());
        }
        res
    }

    pub fn concretize_constructor(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirMethod,
    ) -> Result<FunId, TcError> {
        let current_class = self.class_stack.last().unwrap();
        let self_ty = self.create_type(ctx, ConcreteType::SpecializedClass(*current_class));
        let self_ptr_ty = self.create_type(ctx, ConcreteType::Ptr(self_ty));

        let self_symbol = ctx.ctx.interner.insert_symbol(&"self".to_string());

        let ty = ctx
            .ctx
            .interner
            .insert_type_expr(TypeExpr::Concrete(self_ptr_ty));

        let mut params = vec![TcParam {
            name: self_symbol,
            ty: ty,
        }];

        input.args.iter().try_for_each(|arg| {
            ctx.visit_type(&arg.ty)
                .map(|ty| params.push(TcParam { name: arg.name, ty }))
        })?;

        let return_ty = ctx
            .ctx
            .interner
            .insert_type_expr(TypeExpr::Primitive(PrimitiveTy::Void));

        let fun_id = ctx.ctx.interner.insert_fun(TcFunProto {
            name: input.name,
            params,
            return_ty,
            variadic: false,
        });

        let return_ty = self.visit_type(ctx, return_ty)?;
        let fun = ctx.ctx.interner.get_fun(fun_id).clone();

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
        let sig = Signature {
            name: fun.name,
            params,
            return_ty,
            variadic: fun.variadic,
        };

        self.protos.insert(fun_id, sig);
        Ok(fun_id)
    }

    pub fn concretize_method(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirMethod,
    ) -> Result<FunId, TcError> {
        let current_class = self.class_stack.last().unwrap();
        let self_ty = self.create_type(ctx, ConcreteType::SpecializedClass(*current_class));
        let self_ptr_ty = self.create_type(ctx, ConcreteType::Ptr(self_ty));

        let self_symbol = ctx.ctx.interner.insert_symbol(&"self".to_string());

        let ty = ctx
            .ctx
            .interner
            .insert_type_expr(TypeExpr::Concrete(self_ptr_ty));

        let mut params = vec![TcParam {
            name: self_symbol,
            ty: ty,
        }];

        input.args.iter().try_for_each(|arg| {
            ctx.visit_type(&arg.ty)
                .map(|ty| params.push(TcParam { name: arg.name, ty }))
        })?;

        let return_ty = match &input.return_ty {
            Some(ty) => ctx.visit_type(ty),
            None => Ok(ctx
                .ctx
                .interner
                .insert_type_expr(TypeExpr::Primitive(PrimitiveTy::Void))),
        }?;

        let fun_id = ctx.ctx.interner.insert_fun(TcFunProto {
            name: input.name,
            params,
            return_ty,
            variadic: false,
        });

        self.methods
            .get_mut(&self_ty)
            .unwrap()
            .insert(input.name, fun_id);
        let fun = ctx.ctx.interner.get_fun(fun_id).clone();

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
            name: fun.name,
            params,
            return_ty,
            variadic: fun.variadic,
        };

        self.protos.insert(fun_id, sig);
        Ok(fun_id)
    }

    pub fn visit_constructor(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirMethod,
        fun_id: FunId,
        item: ItemId,
    ) -> Result<(), TcError> {
        let current_class = self.class_stack.last().unwrap();
        let self_ty = self.create_type(ctx, ConcreteType::SpecializedClass(*current_class));
        let self_ptr_ty = self.create_type(ctx, ConcreteType::Ptr(self_ty));

        let self_symbol = ctx.ctx.interner.insert_symbol(&"self".to_string());

        let res = ctx.with_scope(ScopeKind::Function(fun_id, item, vec![]), |ctx| {
            if input.body.is_some() {
                // Self parameter
                {
                    let self_var_id = ctx.ctx.interner.insert_variable(VarDecl {
                        name: self_symbol,
                        ty: self_ptr_ty,
                    });
                    ctx.push_instr(TirInstr::VarDecl(self_var_id), false);
                    let self_value = self.create_expr(ctx, TirExpr::Arg(0), false);
                    ctx.push_instr(TirInstr::VarAssign(self_var_id, self_value), false);
                    let self_def = ctx.ctx.interner.insert_def(Definition::Var(self_var_id));
                    ctx.push_def(self_symbol, self_def);
                }

                // Other parameters
                {
                    input
                        .args
                        .clone()
                        .iter()
                        .enumerate()
                        .try_for_each(|(i, param)| {
                            let ty_id = ctx.visit_type(&param.ty)?;
                            let concrete_ty = self.visit_type(ctx, ty_id)?;

                            let var_id = ctx.ctx.interner.insert_variable(VarDecl {
                                name: param.name,
                                ty: concrete_ty,
                            });
                            ctx.push_instr(TirInstr::VarDecl(var_id), false);
                            // Offset by 1 because of `self` parameter
                            let e = self.create_expr(ctx, TirExpr::Arg(i + 1), false);
                            ctx.push_instr(TirInstr::VarAssign(var_id, e), false);
                            let def = ctx.ctx.interner.insert_def(Definition::Var(var_id));
                            ctx.push_def(param.name, def);
                            Ok(())
                        })?;
                }
            }

            input.body.as_ref().iter().try_for_each(|body| {
                body.iter()
                    .try_for_each(|stmt| self.visit_stmt(ctx, stmt, false))
            })
        })?;
        ctx.flush_deferred();

        Ok(res)
    }

    pub fn visit_method(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirMethod,
        item: ItemId,
    ) -> Result<(), TcError> {
        let current_class = self.class_stack.last().unwrap();
        let self_ty = self.create_type(ctx, ConcreteType::SpecializedClass(*current_class));
        let self_ptr_ty = self.create_type(ctx, ConcreteType::Ptr(self_ty));

        let self_symbol = ctx.ctx.interner.insert_symbol(&"self".to_string());

        let fun_id = self.methods[&self_ty][&input.name];

        let res = ctx.with_scope(ScopeKind::Function(fun_id, item, vec![]), |ctx| {
            if input.body.is_some() {
                // Self parameter
                {
                    let self_var_id = ctx.ctx.interner.insert_variable(VarDecl {
                        name: self_symbol,
                        ty: self_ptr_ty,
                    });
                    ctx.push_instr(TirInstr::VarDecl(self_var_id), false);
                    let self_value = self.create_expr(ctx, TirExpr::Arg(0), false);
                    ctx.push_instr(TirInstr::VarAssign(self_var_id, self_value), false);
                    let self_def = ctx.ctx.interner.insert_def(Definition::Var(self_var_id));
                    ctx.push_def(self_symbol, self_def);
                }

                // Other parameters
                {
                    input
                        .args
                        .clone()
                        .iter()
                        .enumerate()
                        .try_for_each(|(i, param)| {
                            let ty_id = ctx.visit_type(&param.ty)?;
                            let concrete_ty = self.visit_type(ctx, ty_id)?;

                            let var_id = ctx.ctx.interner.insert_variable(VarDecl {
                                name: param.name,
                                ty: concrete_ty,
                            });
                            ctx.push_instr(TirInstr::VarDecl(var_id), false);
                            // Offset by 1 because of `self` parameter
                            let e = self.create_expr(ctx, TirExpr::Arg(i + 1), false);
                            ctx.push_instr(TirInstr::VarAssign(var_id, e), false);
                            let def = ctx.ctx.interner.insert_def(Definition::Var(var_id));
                            ctx.push_def(param.name, def);
                            Ok(())
                        })?;
                }
            }

            input.body.as_ref().iter().try_for_each(|body| {
                body.iter()
                    .try_for_each(|stmt| self.visit_stmt(ctx, stmt, false))
            })
        })?;
        ctx.flush_deferred();

        Ok(res)
    }

    pub fn visit_fundef(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirFunctionDef,
    ) -> Result<(), TcError> {
        assert!(input.generic_args.len() == 0);
        ctx.clear_deferred();
        let f_id = ctx.get_current_fun().unwrap();
        //
        let proto = &self.protos[&f_id];
        if input.body.is_some() {
            proto
                .params
                .clone()
                .iter()
                .enumerate()
                .for_each(|(i, param)| {
                    let var_id = ctx.ctx.interner.insert_variable(VarDecl {
                        name: param.name,
                        ty: param.ty,
                    });
                    ctx.push_instr(TirInstr::VarDecl(var_id), false);
                    let e = self.create_expr(ctx, TirExpr::Arg(i), false);
                    ctx.push_instr(TirInstr::VarAssign(var_id, e), false);
                    let def = ctx.ctx.interner.insert_def(Definition::Var(var_id));
                    ctx.push_def(param.name, def);
                });
        }

        let res = input.body.as_ref().iter().try_for_each(|body| {
            body.iter()
                .try_for_each(|stmt| self.visit_stmt(ctx, stmt, false))
        })?;
        ctx.flush_deferred();
        Ok(res)
    }

    pub fn visit_module(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        module: &NirModuleDef,
    ) -> Result<(), TcError> {
        let children = ctx.get_last_scope().children.clone();
        module
            .items
            .iter()
            .zip(children.iter())
            .try_for_each(|(item, scope)| self.visit_item(ctx, *scope, *item))
    }

    pub fn visit_item(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        scope: ScopeId,
        item: ItemId,
    ) -> Result<(), TcError> {
        ctx.with_scope_id(scope, |ctx| {
            let nir = ctx.ctx.interner.get_item(item).clone();
            match nir {
                NirItem::Function(fdef) => self.visit_fundef(ctx, &fdef),
                NirItem::Alias(_, _) => Ok(()),
                NirItem::Module(def) => self.visit_module(ctx, &def),
                NirItem::Class(_) => Ok(()),
                _ => todo!(),
            }
        })
    }
}

impl<'ctx> Pass<'ctx, SurfaceResolutionPassOutput<'ctx>> for TirCtx {
    type Output = ();

    fn run(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: SurfaceResolutionPassOutput<'ctx>,
    ) -> Result<Self::Output, TcError> {
        pub fn visit_all_fundefs<'ctx>(
            this: &mut TirCtx,
            ctx: &mut TyCtx<'ctx>,
            scope: ScopeId,
        ) -> Result<(), TcError> {
            let s = ctx.get_scope(scope).clone();
            if let ScopeKind::Function(fun_id, _, _) = s.kind {
                this.concretize_fun_proto(ctx, fun_id)
            } else {
                s.children
                    .iter()
                    .try_for_each(|x| visit_all_fundefs(this, ctx, *x))
            }
        }

        visit_all_fundefs(self, ctx, ScopeId::new(0))?;

        for (scope, item) in input {
            self.visit_item(ctx, scope, item)?;
        }
        Ok(())
    }
}
