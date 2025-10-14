use std::collections::{HashMap, HashSet};

use crate::{
    common::{
        global_interner::{
            DefId, ExprId, FunId, ImplBlockId, ItemId, ModuleId, ScopeId, Symbol, TirExprId, TyId,
            TypeExprId,
        },
        pass::Pass,
    },
    nir::{
        interner::ConstructibleId,
        nir::{
            FieldAccess, FieldAccessKind, NirBinOp, NirBinOpKind, NirCall, NirExprKind,
            NirFunctionDef, NirItem, NirLiteral, NirMethod, NirModuleDef, NirPattern,
            NirPatternKind, NirStmt, NirStmtKind, NirVarDecl,
        },
    },
    ty::{
        PrimitiveTy, TcError, TcFunProto, TcParam, TyCtx,
        scope::{Class, ClassMember, Definition, Method, Pattern, ScopeKind, TypeExpr, VarDecl},
        surface_resolution::SurfaceResolutionPassOutput,
        tir::{
            ConcreteType, SCField, Signature, SpecializedClass, TirCtx, TirExpr, TirInstr,
            TypedIntLit,
        },
    },
};

#[derive(Debug)]
pub enum Receiver {
    Module(ModuleId),
    Object(TirExprId),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SpecInfo {
    pub def: DefId,
    pub args: Vec<TyId>,
}

impl TirCtx {
    pub fn new<'ctx>(ctx: &TyCtx<'ctx>) -> Self {
        Self {
            methods: HashMap::new(),
            protos: HashMap::new(),
            calculated: HashSet::new(),
            impls: Self::get_all_impls(ctx),
            class_stack: vec![],
            specs: HashMap::new(),
        }
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
        assert!(args.len() == 0);

        let spec_info = SpecInfo {
            def: template,
            args: vec![],
        };

        if self.specs.contains_key(&spec_info) {
            return Ok(self.specs[&spec_info]);
        }

        let class_id = {
            let def = ctx.ctx.interner.get_def(template);
            match def {
                Definition::Class(class_id) => *class_id,
                _ => unreachable!(),
            }
        };

        let Class {
            name,
            templates,
            members,
            methods,
        } = ctx.ctx.interner.get_class(class_id).clone();

        assert!(templates.len() == args.len());

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

        let c = SpecializedClass {
            original: template,
            name,
            fields,
            templates: vec![],
            constructors: vec![],
            methods: vec![],
        };

        let sc_id = ctx.ctx.interner.insert_sc(c);

        let ty = ctx
            .ctx
            .interner
            .insert_conc_type(ConcreteType::SpecializedClass(sc_id));

        self.specs.insert(spec_info, ty);

        assert!(self.impls.len() == 0);

        self.class_stack.push(sc_id);
        self.methods.insert(ty, HashMap::new());
        ctx.with_scope(ScopeKind::Spec(sc_id), |ctx| {
            {
                for Method { id: method_id, .. } in &methods {
                    let method_ast = match ctx.ctx.interner.get_item(*method_id) {
                        NirItem::Method(ast) => ast.clone(),
                        _ => unreachable!(),
                    };
                    self.concretize_method(ctx, &method_ast)?;
                }
            }

            {
                for Method { id: method_id, .. } in &methods {
                    let method_ast = match ctx.ctx.interner.get_item(*method_id) {
                        NirItem::Method(ast) => ast.clone(),
                        _ => unreachable!(),
                    };
                    self.visit_method(ctx, &method_ast, *method_id)?;
                }
            }
            Ok(())
        })?;

        self.class_stack.pop();

        Ok(ty)
    }

    pub fn visit_type(&mut self, ctx: &mut TyCtx<'ctx>, ty: TypeExprId) -> Result<TyId, TcError> {
        let te = ctx.ctx.interner.get_type_expr(ty).clone();
        match &te {
            TypeExpr::Template(_) => todo!(),
            TypeExpr::Associated(_) => todo!(),
            TypeExpr::Instantiation { template, args } => self.instantiate(ctx, *template, args),
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
            TypeExpr::Concrete(id) => Ok(*id),
        }
    }

    pub fn type_is_coercible(&mut self, ctx: &mut TyCtx<'ctx>, src: TyId, target: TyId) -> bool {
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

        todo!("Coerce {:?} into {:?} ?", s, t)
    }

    pub fn create_expr(&mut self, ctx: &mut TyCtx<'ctx>, expr: TirExpr) -> TirExprId {
        let e = ctx.ctx.interner.insert_te(expr);
        self.push_instr(ctx, TirInstr::Calculate(e));
        e
    }

    pub fn get_primitive_type(&mut self, ctx: &mut TyCtx<'ctx>, prim: PrimitiveTy) -> TyId {
        ctx.ctx
            .interner
            .insert_conc_type(ConcreteType::Primitive(prim))
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
                    if self.is_type_ptr(ctx, lt) {
                        Ok(lt)
                    } else if self.is_type_ptr(ctx, rt) {
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
                let mut ty = ctx.ctx.interner.get_conc_type(t);
                if let ConcreteType::Ptr(x) = ty {
                    ty = ctx.ctx.interner.get_conc_type(*x);
                }
                if let ConcreteType::SpecializedClass(sc_id) = ty {
                    let sc = ctx.ctx.interner.get_sc(*sc_id);
                    let field = sc
                        .fields
                        .iter()
                        .find(|elem| elem.name == field_name)
                        .ok_or(TcError::Text("Field named ??? not found in class ???"))?;
                    Ok(ctx
                        .ctx
                        .interner
                        .insert_conc_type(ConcreteType::Ptr(field.ty)))
                } else {
                    return Err(TcError::Text("No named field in non-class type"));
                }
            }
            TirExpr::PtrAccess(expr, FieldAccessKind::Index(i)) => {
                let t = self.get_type_of_tir_expr(ctx, expr).unwrap();
                let mut ty = ctx.ctx.interner.get_conc_type(t);
                if let ConcreteType::Ptr(x) = ty {
                    ty = ctx.ctx.interner.get_conc_type(*x);
                }
                if let ConcreteType::Tuple(ids) = ty {
                    if ids.len() <= i as usize {
                        return Err(TcError::Text("Tuple access out of range"));
                    }
                    Ok(ctx
                        .ctx
                        .interner
                        .insert_conc_type(ConcreteType::Ptr(ids[i as usize])))
                } else {
                    return Err(TcError::Text("No index field in non-tuple type"));
                }
            }
            TirExpr::VarPtr(id) => {
                let inner = ctx.ctx.interner.get_variable(id).ty;
                Ok(ctx.ctx.interner.insert_conc_type(ConcreteType::Ptr(inner)))
            }
        }
    }

    pub fn get_access_ty(
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

    pub fn get_ptr_to(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> TyId {
        ctx.ctx.interner.insert_conc_type(ConcreteType::Ptr(ty))
    }

    pub fn get_type_of_expr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr_id: ExprId,
    ) -> Result<TyId, TcError> {
        let expr = ctx.ctx.interner.get_expr(expr_id).clone();
        match &expr.kind {
            NirExprKind::Literal(nir_literal) => match nir_literal {
                NirLiteral::IntLiteral(_) => Ok(self.get_primitive_type(ctx, PrimitiveTy::I64)),
                NirLiteral::StringLiteral(_) => {
                    let ty = self.get_primitive_type(ctx, PrimitiveTy::U8);
                    Ok(self.get_ptr_to(ctx, ty))
                }
                _ => todo!(),
            },
            NirExprKind::Named(name) => {
                if *name == ctx.ctx.interner.insert_symbol(&"true".to_string())
                    || *name == ctx.ctx.interner.insert_symbol(&"false".to_string())
                {
                    return Ok(self.get_primitive_type(ctx, PrimitiveTy::Bool));
                }
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
                    FieldAccessKind::Symbol(name) => {
                        if let ConcreteType::SpecializedClass(sc_id) = ty {
                            let sc = ctx.ctx.interner.get_sc(*sc_id);
                            for f in &sc.fields {
                                if f.name == name {
                                    return Ok(f.ty);
                                }
                            }
                            return Err(TcError::Text("Field named ??? not found in class ???"));
                        } else {
                            return Err(TcError::Text("No named field in non-class type"));
                        }
                    }
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

                if self.is_type_ptr(ctx, lt) {
                    Ok(lt)
                } else if self.is_type_ptr(ctx, rt) {
                    Ok(rt)
                } else {
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
            }
            NirExprKind::Call(NirCall {
                called,
                generic_args,
                args,
                span: _,
            }) => {
                assert!(generic_args.len() == 0);

                let (f_id, self_arg): (FunId, Option<TirExprId>) = if called.receiver.is_some() {
                    let receiver = self.expr_as_receiver(ctx, called.receiver.unwrap())?;
                    match receiver {
                        Receiver::Module(id) => {
                            let m = ctx.ctx.interner.get_module(id);
                            let s = m.scope;
                            let def_id = ctx.get_symbol_def_in_scope(s, called.called);
                            if def_id.is_none() {
                                return Err(TcError::Text("No such function in module"));
                            }
                            let def_id = def_id.unwrap();
                            let def = ctx.ctx.interner.get_def(def_id);
                            match &def {
                                Definition::Function(fun_id) => (*fun_id, None),
                                _ => {
                                    return Err(TcError::Text("No such function in module"));
                                }
                            }
                        }
                        Receiver::Object(x) => {
                            let t = self.get_type_of_tir_expr(ctx, x)?;
                            let inner = Self::inner_ptr_ty(ctx, t).unwrap();
                            let methods = &self.methods[&inner];
                            if !methods.contains_key(&called.called) {
                                return Err(TcError::Text("No method named ??? in class ???"));
                            }
                            (methods[&called.called], Some(x))
                        }
                    }
                } else {
                    (self.get_fun_id_from_symbol(ctx, called.called)?, None)
                };

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
                    return Err(TcError::Text("Arg len mismatch in function call"));
                }

                Ok(sig.return_ty)
            }
            _ => todo!(),
        }
    }

    pub fn inner_ptr_ty(ctx: &mut TyCtx<'ctx>, ptr: TyId) -> Option<TyId> {
        match ctx.ctx.interner.get_conc_type(ptr) {
            ConcreteType::Ptr(x) => Some(*x),
            _ => None,
        }
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
    ) -> Result<Receiver, TcError> {
        if let Ok(id) = self.expr_as_module(ctx, expr) {
            return Ok(Receiver::Module(id));
        }
        self.get_expr_ptr(ctx, expr).map(Receiver::Object)
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

    pub fn debug_instrs(ctx: &mut TyCtx<'ctx>) {
        pub fn aux<'ctx>(ctx: &mut TyCtx<'ctx>, id: ScopeId) {
            ctx.with_scope_id(id, |ctx| {
                let instrs = match &ctx.get_last_scope().kind {
                    ScopeKind::Function(_, _, tir_instrs) => tir_instrs,
                    _ => &vec![],
                };

                for instr in instrs.clone() {
                    println!("{:?}", instr);
                }
                if let Some(parent) = ctx.get_last_scope().parent {
                    aux(ctx, parent);
                }
            })
        }
        aux(ctx, ScopeId::new(0));
    }

    pub fn debug_defs(ctx: &mut TyCtx<'ctx>) {
        pub fn aux<'ctx>(ctx: &mut TyCtx<'ctx>, id: ScopeId) {
            ctx.with_scope_id(id, |ctx| {
                for (def, _) in ctx.get_last_scope().definitions.clone() {
                    println!("[DEFINED] {}", ctx.ctx.interner.get_symbol(def))
                }
                if let Some(parent) = ctx.get_last_scope().parent {
                    aux(ctx, parent);
                }
            })
        }
        aux(ctx, ctx.current_scope);
    }

    pub fn get_type_size(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> usize {
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

    pub fn is_type_integer(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> bool {
        let t = ctx.ctx.interner.get_conc_type(ty);
        match t {
            ConcreteType::Ptr(_) => true,
            ConcreteType::Primitive(PrimitiveTy::Void) => false,
            ConcreteType::Primitive(_) => true,
            _ => false,
        }
    }

    pub fn is_type_ptr(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> bool {
        let t = ctx.ctx.interner.get_conc_type(ty);
        match t {
            ConcreteType::Ptr(_) => true,
            _ => false,
        }
    }

    pub fn get_expr_with_type(
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
                    Ok(self.create_expr(ctx, e))
                }
                NirLiteral::FloatLiteral(_) => todo!(),
                NirLiteral::StringLiteral(x) => {
                    if let ConcreteType::Ptr(inner) = t {
                        let inner = inner.clone();
                        if inner == self.get_primitive_type(ctx, PrimitiveTy::U8) {
                            Ok(self.create_expr(ctx, TirExpr::StringLiteral(*x)))
                        } else {
                            let e = self.create_expr(ctx, TirExpr::StringLiteral(*x));
                            Ok(self.create_expr(ctx, TirExpr::PtrCast(inner, e)))
                        }
                    } else {
                        todo!()
                    }
                }
                NirLiteral::CharLiteral(_) => todo!(),
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
                    let e = self.create_expr(ctx, expr);
                    let bool_ty = self.get_primitive_type(ctx, PrimitiveTy::Bool);
                    if ty == bool_ty {
                        return Ok(e);
                    } else if self.is_type_integer(ctx, ty) {
                        return Ok(self.create_expr(ctx, TirExpr::IntCast(ty, e)));
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
                        return Ok(self.create_expr(ctx, TirExpr::VarExpr(var_id)));
                    }
                    if !self.type_is_coercible(ctx, var.ty, ty) {
                        return Err(TcError::Text("Types are not coercible !"));
                    }
                    if self.is_type_integer(ctx, var.ty) && self.is_type_integer(ctx, ty) {
                        let var_expr = self.create_expr(ctx, TirExpr::VarExpr(var_id));
                        return Ok(self.create_expr(ctx, TirExpr::IntCast(ty, var_expr)));
                    }
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
                    Ok(self.create_expr(ctx, tuple))
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

                let (lt, rt) = if self.is_type_ptr(ctx, lt) {
                    (lt, self.get_primitive_type(ctx, PrimitiveTy::I64))
                } else if self.is_type_ptr(ctx, rt) {
                    (self.get_primitive_type(ctx, PrimitiveTy::I64), rt)
                } else if self.is_type_integer(ctx, lt) && self.is_type_integer(ctx, rt) {
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
                } else if self.is_type_ptr(ctx, lt) {
                    lt
                } else if self.is_type_ptr(ctx, rt) {
                    rt
                } else if lt_size > rt_size {
                    lt
                } else {
                    rt
                };

                let lhs = self.get_expr_with_type(ctx, *left, lt)?;
                let rhs = self.get_expr_with_type(ctx, *right, rt)?;
                let e = self.create_expr(ctx, TirExpr::BinOp { lhs, rhs, op: *op });

                Ok({
                    if value_type != ty {
                        self.create_expr(ctx, TirExpr::IntCast(ty, e))
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

                let (f_id, self_arg): (FunId, Option<TirExprId>) = if called.receiver.is_some() {
                    let receiver = self.expr_as_receiver(ctx, called.receiver.unwrap())?;
                    match receiver {
                        Receiver::Module(id) => {
                            let m = ctx.ctx.interner.get_module(id);
                            let s = m.scope;
                            let def_id = ctx.get_symbol_def_in_scope(s, called.called);
                            if def_id.is_none() {
                                return Err(TcError::Text("No such function in module"));
                            }
                            let def_id = def_id.unwrap();
                            let def = ctx.ctx.interner.get_def(def_id);
                            match &def {
                                Definition::Function(fun_id) => (*fun_id, None),
                                _ => {
                                    return Err(TcError::Text("No such function in module"));
                                }
                            }
                        }
                        Receiver::Object(x) => {
                            let t = self.get_type_of_tir_expr(ctx, x)?;
                            let inner = Self::inner_ptr_ty(ctx, t).unwrap();
                            let methods = &self.methods[&inner];
                            if !methods.contains_key(&called.called) {
                                return Err(TcError::Text("No method named ??? in class ???"));
                            }
                            (methods[&called.called], Some(x))
                        }
                    }
                } else {
                    (self.get_fun_id_from_symbol(ctx, called.called)?, None)
                };

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
                    return Err(TcError::Text("Arg len mismatch in function call"));
                }

                let mut params = sig
                    .params
                    .iter()
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
                            self.get_expr_with_type(ctx, *expr, param.unwrap().ty)
                        } else {
                            self.get_expr(ctx, *expr)
                        }
                    })
                    .try_collect::<Vec<_>>()?;

                self_arg.iter().for_each(|x| args.insert(0, *x));
                // args.insert(0, self_arg);

                Ok(self.create_expr(ctx, TirExpr::Funcall(f_id, args)))
            }
            x => todo!("{x:?}"),
        }
    }

    pub fn get_access(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: TirExprId,
        access: FieldAccessKind,
    ) -> Result<TirExprId, TcError> {
        match access {
            FieldAccessKind::Symbol(name) => {
                let t = self.get_type_of_tir_expr(ctx, expr)?;
                let ty = ctx.ctx.interner.get_conc_type(t);
                if let ConcreteType::SpecializedClass(sc_id) = ty {
                    let sc = ctx.ctx.interner.get_sc(*sc_id);
                    for f in &sc.fields {
                        if f.name == name {
                            return Ok(self.create_expr(ctx, TirExpr::Access(expr, access)));
                        }
                    }
                    return Err(TcError::Text("Field named ??? not found in class ???"));
                } else {
                    return Err(TcError::Text("No named field in non-class type"));
                }
            }
            FieldAccessKind::Index(i) => {
                let ty = self.get_type_of_tir_expr(ctx, expr)?;
                let t = ctx.ctx.interner.get_conc_type(ty);
                if let ConcreteType::Tuple(tys) = t {
                    if tys.len() <= i as usize {
                        return Err(TcError::Text("Tuple access out of range"));
                    }
                    Ok(self.create_expr(ctx, TirExpr::Access(expr, access)))
                } else {
                    return Err(TcError::Text("No integer field in non-tuple type"));
                }
            }
        }
    }

    pub fn get_expr(&mut self, ctx: &mut TyCtx<'ctx>, expr: ExprId) -> Result<TirExprId, TcError> {
        let ty = self.get_type_of_expr(ctx, expr)?;
        self.get_expr_with_type(ctx, expr, ty)
    }

    pub fn push_instr(&mut self, ctx: &mut TyCtx<'ctx>, instr: TirInstr) {
        match &instr {
            TirInstr::Calculate(id) => {
                self.calculated.insert(*id);
            }
            _ => (),
        };
        let scope = ctx.get_last_scope_mut();
        match &mut scope.kind {
            ScopeKind::Else(tir_instrs)
            | ScopeKind::Then(tir_instrs)
            | ScopeKind::Block(tir_instrs)
            | ScopeKind::WhileLoop(_, tir_instrs)
            | ScopeKind::WhileCond(tir_instrs)
            | ScopeKind::Function(_, _, tir_instrs) => tir_instrs.push(instr),
            _ => unreachable!(),
        }
    }

    pub fn visit_pattern(
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
                self.push_instr(ctx, TirInstr::VarDecl(id));
                ctx.push_def(*symb, d);
                expr.iter()
                    .for_each(|x| self.push_instr(ctx, TirInstr::VarAssign(id, *x)));
                Ok(())
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

                nirs.iter()
                    .zip(tys.iter())
                    .enumerate()
                    .try_for_each(|(i, (x, ty))| {
                        let expr = expr.map(|e| {
                            self.create_expr(
                                ctx,
                                TirExpr::Access(e, FieldAccessKind::Index(i as u32)),
                            )
                        });
                        self.declare_pattern(ctx, x, *ty, expr)
                    })
            }
        }
    }

    pub fn visit_let(&mut self, ctx: &mut TyCtx<'ctx>, input: &NirVarDecl) -> Result<(), TcError> {
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

    pub fn visit_stmt(&mut self, ctx: &mut TyCtx<'ctx>, input: &NirStmt) -> Result<(), TcError> {
        match &input.kind {
            NirStmtKind::Return { value } => {
                let void_ty = self.get_primitive_type(ctx, PrimitiveTy::Void);
                let return_ty = ctx.get_return_ty();
                let ret_id = return_ty.map_or(Ok(void_ty), |ty| self.visit_type(ctx, ty))?;

                if value.is_none() {
                    if ret_id != void_ty {
                        return Err(TcError::BadReturnType(void_ty, ret_id));
                    }
                    self.push_instr(ctx, TirInstr::Return(None));
                    return Ok(());
                }
                let value = value.unwrap();
                let expr_ty = self.get_type_of_expr(ctx, value)?;

                if !self.type_is_coercible(ctx, expr_ty, ret_id) {
                    return Err(TcError::BadReturnType(expr_ty, ret_id));
                }
                let expr = self.get_expr_with_type(ctx, value, ret_id)?;
                self.push_instr(ctx, TirInstr::Return(Some(expr)));
                Ok(())
            }
            NirStmtKind::Let(decl) => self.visit_let(ctx, decl),
            NirStmtKind::Expr(expr) => {
                self.get_expr(ctx, *expr)?;
                Ok(())
            }
            NirStmtKind::If {
                cond,
                then_block,
                else_block,
            } => {
                let bool_ty = self.get_primitive_type(ctx, PrimitiveTy::Bool);
                let cond_val = self.get_expr_with_type(ctx, *cond, bool_ty)?;
                let if_scope = {
                    let mut if_scope = None;
                    ctx.with_scope(ScopeKind::If { cond: cond_val }, |ctx| {
                        if_scope = Some(ctx.current_scope);
                        ctx.with_scope(ScopeKind::Then(vec![]), |ctx| {
                            self.visit_stmt(ctx, then_block)
                        })?;
                        if let Some(eblock) = else_block {
                            ctx.with_scope(ScopeKind::Else(vec![]), |ctx| {
                                self.visit_stmt(ctx, eblock)
                            })
                        } else {
                            Ok(())
                        }
                    })?;
                    if_scope.unwrap()
                };
                self.push_instr(ctx, TirInstr::If(if_scope));
                Ok(())
            }
            NirStmtKind::Block(stmts) => {
                let blk = {
                    let mut blk = None;
                    ctx.with_scope(ScopeKind::Block(vec![]), |ctx| {
                        blk = Some(ctx.current_scope);
                        stmts.iter().try_for_each(|stmt| self.visit_stmt(ctx, stmt))
                    })?;
                    blk.unwrap()
                };
                self.push_instr(ctx, TirInstr::Block(blk));
                Ok(())
            }
            NirStmtKind::While { cond, body } => {
                let bool_ty = self.get_primitive_type(ctx, PrimitiveTy::Bool);
                let while_scope = {
                    let mut while_scope = None;
                    ctx.with_scope(ScopeKind::While, |ctx| {
                        while_scope = Some(ctx.current_scope);
                        let e = ctx.with_scope(ScopeKind::WhileCond(vec![]), |ctx| {
                            self.get_expr_with_type(ctx, *cond, bool_ty)
                        })?;
                        ctx.with_scope(ScopeKind::WhileLoop(e, vec![]), |ctx| {
                            self.visit_stmt(ctx, body)
                        })
                    })?;
                    while_scope.unwrap()
                };
                self.push_instr(ctx, TirInstr::While(while_scope));
                Ok(())
            }
            NirStmtKind::Assign { assigned, value } => {
                let ty = self.get_type_of_expr(ctx, *assigned)?;
                let rval = self.get_expr_with_type(ctx, *value, ty)?;
                self.visit_assign(ctx, *assigned, rval)
            }
            x => todo!("{:?}", x),
        }
    }

    pub fn get_expr_ptr(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        expr: ExprId,
    ) -> Result<TirExprId, TcError> {
        let e = ctx.ctx.interner.get_expr(expr).clone();
        match &e.kind {
            NirExprKind::Named(name) => {
                if *name == ctx.ctx.interner.insert_symbol(&"true".to_string())
                    || *name == ctx.ctx.interner.insert_symbol(&"false".to_string())
                {
                    return Err(TcError::Text("Invalid LValue"));
                }
                let name = name.clone();
                let def = ctx.get_symbol_def(name);
                if def.is_none() {
                    return Err(TcError::NameNotFound(name));
                }
                let def = ctx.ctx.interner.get_def(def.unwrap()).clone();
                match def {
                    Definition::Var(id) => {
                        let lval = self.create_expr(ctx, TirExpr::VarPtr(id));
                        Ok(lval)
                    }
                    _ => todo!(),
                }
            }
            NirExprKind::Access { from, field } => {
                let from_expr = self.get_expr_ptr(ctx, *from)?;
                let lval = self.create_expr(ctx, TirExpr::PtrAccess(from_expr, field.kind));
                Ok(lval)
            }
            _ => todo!(),
        }
    }

    pub fn visit_assign(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        assigned: ExprId,
        rval: TirExprId,
    ) -> Result<(), TcError> {
        let e = ctx.ctx.interner.get_expr(assigned).clone();
        match &e.kind {
            // NirExprKind::Subscript { .. } => todo!(),
            // NirExprKind::Access { from, field } => {
            //     let from_expr = self.get_expr_ptr(ctx, *from)?;
            //     let lval = self.create_expr(ctx, TirExpr::PtrAccess(from_expr, field.kind));
            //     self.push_instr(ctx, TirInstr::Assign(lval, rval));
            //     Ok(())
            // }
            // NirExprKind::Named(name) => {
            //     if *name == ctx.ctx.interner.insert_symbol(&"true".to_string())
            //         || *name == ctx.ctx.interner.insert_symbol(&"false".to_string())
            //     {
            //         return Err(TcError::Text("Invalid LValue"));
            //     }
            //     let name = name.clone();
            //     let def = ctx.get_symbol_def(name);
            //     if def.is_none() {
            //         return Err(TcError::NameNotFound(name));
            //     }
            //     let def = ctx.ctx.interner.get_def(def.unwrap()).clone();
            //     match def {
            //         Definition::Var(id) => {
            //             let lval = self.create_expr(ctx, TirExpr::VarPtr(id));
            //             self.push_instr(ctx, TirInstr::Assign(lval, rval));
            //             Ok(())
            //         }
            //         _ => todo!(),
            //     }
            // }
            NirExprKind::Tuple(exprs) => {
                for (i, expr) in exprs.iter().enumerate() {
                    let rval_i = self
                        .create_expr(ctx, TirExpr::Access(rval, FieldAccessKind::Index(i as u32)));
                    self.visit_assign(ctx, *expr, rval_i)?;
                }
                Ok(())
            }
            _ => {
                let expr_ptr = self.get_expr_ptr(ctx, assigned)?;
                self.push_instr(ctx, TirInstr::Assign(expr_ptr, rval));
                Ok(())
            }
        }
    }

    pub fn get_nth_field_of_tuple_type(
        &self,
        ctx: &TyCtx<'ctx>,
        ty: TyId,
        index: usize,
    ) -> Option<TyId> {
        let t = ctx.ctx.interner.get_conc_type(ty);
        match t {
            ConcreteType::Tuple(ids) => ids.get(index).copied(),
            _ => None,
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

    pub fn concretize_method(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirMethod,
    ) -> Result<(), TcError> {
        let current_class = self.class_stack.last().unwrap();
        let self_ty = ctx
            .ctx
            .interner
            .insert_conc_type(ConcreteType::SpecializedClass(*current_class));
        let self_ptr_ty = ctx
            .ctx
            .interner
            .insert_conc_type(ConcreteType::Ptr(self_ty));

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
        Ok(())
    }

    pub fn visit_method(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirMethod,
        item: ItemId,
    ) -> Result<(), TcError> {
        let current_class = self.class_stack.last().unwrap();
        let self_ty = ctx
            .ctx
            .interner
            .insert_conc_type(ConcreteType::SpecializedClass(*current_class));
        let self_ptr_ty = ctx
            .ctx
            .interner
            .insert_conc_type(ConcreteType::Ptr(self_ty));

        let self_symbol = ctx.ctx.interner.insert_symbol(&"self".to_string());

        let fun_id = self.methods[&self_ty][&input.name];

        ctx.with_scope(ScopeKind::Function(fun_id, item, vec![]), |ctx| {
            if input.body.is_some() {
                // Self parameter
                {
                    let self_var_id = ctx.ctx.interner.insert_variable(VarDecl {
                        name: self_symbol,
                        ty: self_ptr_ty,
                    });
                    self.push_instr(ctx, TirInstr::VarDecl(self_var_id));
                    let self_value = self.create_expr(ctx, TirExpr::Arg(0));
                    self.push_instr(ctx, TirInstr::VarAssign(self_var_id, self_value));
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
                            self.push_instr(ctx, TirInstr::VarDecl(var_id));
                            // Offset by 1 because of `self` parameter
                            let e = self.create_expr(ctx, TirExpr::Arg(i + 1));
                            self.push_instr(ctx, TirInstr::VarAssign(var_id, e));
                            let def = ctx.ctx.interner.insert_def(Definition::Var(var_id));
                            ctx.push_def(param.name, def);
                            Ok(())
                        })?;
                }
            }

            input
                .body
                .as_ref()
                .iter()
                .try_for_each(|body| body.iter().try_for_each(|stmt| self.visit_stmt(ctx, stmt)))
        })
    }

    pub fn visit_fundef(
        &mut self,
        ctx: &mut TyCtx<'ctx>,
        input: &NirFunctionDef,
    ) -> Result<(), TcError> {
        assert!(input.generic_args.len() == 0);

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
                    self.push_instr(ctx, TirInstr::VarDecl(var_id));
                    let e = self.create_expr(ctx, TirExpr::Arg(i));
                    self.push_instr(ctx, TirInstr::VarAssign(var_id, e));
                    let def = ctx.ctx.interner.insert_def(Definition::Var(var_id));
                    ctx.push_def(param.name, def);
                });
        }

        input
            .body
            .as_ref()
            .iter()
            .try_for_each(|body| body.iter().try_for_each(|stmt| self.visit_stmt(ctx, stmt)))
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
