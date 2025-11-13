use std::collections::HashMap;

use inkwell::{
    AddressSpace, IntPredicate,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    targets::{TargetMachine, TargetTriple},
    types::{AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType},
    values::{
        AnyValue, AnyValueEnum, BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue,
        GlobalValue, InstructionOpcode, PointerValue,
    },
};

use crate::{
    common::{
        global_interner::{FunId, ScopeId, StringLiteral, TirExprId, TyId, VariableId},
        pass::Pass,
    },
    nir::{
        interner::ConstructibleId,
        nir::{FieldAccessKind, NirBinOpKind},
    },
    ty::{
        PrimitiveTy, TcError, TyCtx,
        scope::ScopeKind,
        tir::{ConcreteType, SCField, TirCtx, TirExpr, TirInstr, TypedIntLit},
    },
};

pub struct MonoIRPass<'a> {
    pub triple: TargetTriple,
    pub ictx: &'a Context,
    pub tir_ctx: &'a mut TirCtx,
    pub module: Module<'a>,
    pub builder: Builder<'a>,
    pub expressions: HashMap<TirExprId, AnyValueEnum<'a>>,
    pub vars: HashMap<VariableId, (BasicTypeEnum<'a>, PointerValue<'a>)>,
    pub tys: HashMap<TyId, AnyTypeEnum<'a>>,
    pub funs: HashMap<FunId, (FunctionValue<'a>, ScopeId)>,
    pub strlits: HashMap<StringLiteral, GlobalValue<'a>>,
}

impl<'ctx, 'a> Pass<'ctx, ()> for MonoIRPass<'a> {
    type Output = ();

    fn run(&mut self, ctx: &mut TyCtx<'ctx>, _: ()) -> Result<Self::Output, TcError> {
        self.visit_all_scopes(ctx);
        println!("{}", self.module.print_to_string().to_string());
        // self.module.verify().unwrap();
        Ok(())
    }
}

impl<'ctx, 'a> MonoIRPass<'a> {
    pub fn new(name: &str, ictx: &'a Context, tir_ctx: &'a mut TirCtx) -> Self {
        let triple = TargetMachine::get_default_triple();
        let module = ictx.create_module(name);
        let builder = ictx.create_builder();
        Self {
            triple,
            ictx,
            tir_ctx,
            module,
            builder,
            expressions: HashMap::new(),
            vars: HashMap::new(),
            tys: HashMap::new(),
            funs: HashMap::new(),
            strlits: HashMap::new(),
        }
    }

    pub fn visit_all_scopes(&mut self, ctx: &mut TyCtx<'ctx>) {
        fn aux<'ctx>(this: &mut MonoIRPass, ctx: &mut TyCtx<'ctx>) {
            if matches!(&ctx.get_last_scope().kind, ScopeKind::Function(_, _, _)) {
                this.declare_fundef(ctx);
            }

            for child in &ctx.get_last_scope().children.clone() {
                ctx.with_scope_id(*child, |ctx| {
                    aux(this, ctx);
                })
            }
        }

        ctx.with_scope_id(ScopeId::new(0), |ctx| {
            aux(self, ctx);
        });

        let keys = self.funs.keys().cloned().collect::<Vec<_>>();

        for fun_id in keys {
            self.visit_fundef(ctx, fun_id)
        }
    }

    fn visit_fundef(&mut self, ctx: &mut TyCtx<'ctx>, id: FunId) {
        let (fn_val, scope_id) = self.funs[&id].clone();
        ctx.with_scope_id(scope_id, |ctx| {
            let (_, instrs) = match &ctx.ctx.interner.get_scope(ctx.current_scope).kind {
                ScopeKind::Function(fun_id, _, instrs) => (*fun_id, instrs.clone()),
                _ => unreachable!(),
            };

            if !instrs.is_empty() {
                let entry_basic_block = self.ictx.append_basic_block(fn_val, "entry");
                self.builder.position_at_end(entry_basic_block);
            }
            instrs.iter().for_each(|instr| self.translate(ctx, instr));
            fn_val
                .get_last_basic_block()
                .inspect(|bb| match bb.get_terminator() {
                    None => {
                        self.builder.build_return(None).unwrap();
                    }
                    _ => (),
                });
        });
    }

    fn declare_fundef(&mut self, ctx: &mut TyCtx<'ctx>) {
        let fun_scope = ctx.get_current_fun_scope().unwrap();
        let (fun_id, instrs) = match &ctx.ctx.interner.get_scope(fun_scope).kind {
            ScopeKind::Function(fun_id, _, instrs) => (*fun_id, instrs.clone()),
            _ => unreachable!(),
        };

        let fn_val = self.setup_function(ctx, fun_id, instrs.is_empty());

        self.funs.insert(fun_id, (fn_val, ctx.current_scope));
    }

    fn get_iw_for_primitive(&self, p: PrimitiveTy) -> AnyTypeEnum<'a> {
        match p {
            PrimitiveTy::Void => self.ictx.void_type().as_any_type_enum(),
            PrimitiveTy::U8 | PrimitiveTy::I8 => self.ictx.i8_type().as_any_type_enum(),
            PrimitiveTy::U16 | PrimitiveTy::I16 => self.ictx.i16_type().as_any_type_enum(),
            PrimitiveTy::U32 | PrimitiveTy::I32 => self.ictx.i32_type().as_any_type_enum(),
            PrimitiveTy::U64 | PrimitiveTy::I64 => self.ictx.i64_type().as_any_type_enum(),
            PrimitiveTy::Bool => self.ictx.bool_type().as_any_type_enum(),
        }
    }

    /// This returns a vec because it destructures tuples and structs
    fn get_mono_ty(&mut self, ctx: &TyCtx<'ctx>, ty: TyId) -> AnyTypeEnum<'a> {
        if self.tys.contains_key(&ty) {
            return self.tys[&ty];
        }
        let t = ctx.ctx.interner.get_conc_type(ty);
        let res = match t {
            ConcreteType::SpecializedClass(sc_id) => {
                let sc = ctx.ctx.interner.get_sc(*sc_id);
                let fields = sc
                    .fields
                    .iter()
                    .map(|x| BasicTypeEnum::try_from(self.get_mono_ty(ctx, x.ty)).unwrap())
                    .collect::<Vec<_>>();
                let opaque_struct = self
                    .ictx
                    .opaque_struct_type(&ctx.ctx.interner.get_symbol(sc.name));
                opaque_struct.set_body(&fields[..], false);

                opaque_struct.as_any_type_enum()
            }
            ConcreteType::Primitive(primitive_ty) => self.get_iw_for_primitive(*primitive_ty),
            ConcreteType::Ptr(_) => self.ictx.ptr_type(AddressSpace::from(0)).as_any_type_enum(),
            ConcreteType::Tuple(tys) => {
                let field_types = tys
                    .clone()
                    .into_iter()
                    .map(|ty| self.get_mono_ty(ctx, ty).try_into().unwrap())
                    .collect::<Vec<_>>();
                self.ictx
                    .struct_type(&field_types[..], false)
                    .as_any_type_enum()
            }
        };
        self.tys.insert(ty, res);
        res
    }

    fn get_fun_type(&mut self, ctx: &TyCtx<'ctx>, id: FunId) -> FunctionType<'a> {
        let proto = self.tir_ctx.protos[&id].clone();
        let args = proto
            .params
            .iter()
            .map(|SCField { ty, .. }| {
                let ty = self.get_mono_ty(ctx, *ty);
                BasicMetadataTypeEnum::try_from(ty).unwrap()
            })
            .collect::<Vec<_>>();

        match self.get_mono_ty(ctx, proto.return_ty) {
            AnyTypeEnum::FloatType(x) => x.fn_type(&args[..], proto.variadic),
            AnyTypeEnum::IntType(x) => x.fn_type(&args[..], proto.variadic),
            AnyTypeEnum::PointerType(x) => x.fn_type(&args[..], proto.variadic),
            AnyTypeEnum::StructType(x) => x.fn_type(&args[..], proto.variadic),
            AnyTypeEnum::VoidType(x) => x.fn_type(&args[..], proto.variadic),
            _ => unreachable!(),
        }
    }

    fn get_fun_name(&self, ctx: &TyCtx<'ctx>, id: FunId) -> String {
        let proto = self.tir_ctx.protos[&id].clone();
        ctx.ctx.interner.get_symbol(proto.name).clone()
    }

    fn setup_function(
        &mut self,
        ctx: &TyCtx<'ctx>,
        id: FunId,
        is_empty: bool,
    ) -> FunctionValue<'a> {
        let fun_type = self.get_fun_type(ctx, id);
        let fun_name = self.get_fun_name(ctx, id);
        let fn_val = self.module.add_function(
            fun_name.as_ref(),
            fun_type,
            if is_empty {
                Some(Linkage::External)
            } else {
                None
            },
        );

        fn_val
    }

    fn calculate(&mut self, ctx: &mut TyCtx<'ctx>, expr: TirExprId) -> AnyValueEnum<'a> {
        // if self.expressions.contains_key(&expr) {
        //     return self.expressions[&expr].clone();
        // }
        println!("-------------------------------");
        let original_expr = dbg!(expr);
        let e = ctx.ctx.interner.get_te(expr).clone();
        let res = match dbg!(e) {
            TirExpr::Arg(i) => {
                let fun_id = ctx.get_current_fun().unwrap();
                let (fn_val, _) = self.funs[&fun_id].clone();
                fn_val.get_nth_param(i as u32).unwrap().as_any_value_enum()
            }
            TirExpr::TypedIntLit(typed_int_lit) => match typed_int_lit {
                TypedIntLit::Ptr(_, x) => {
                    let intlit_ptr = self.ictx.i64_type().const_int(x as u64, false);
                    self.builder
                        .build_int_to_ptr(intlit_ptr, self.ictx.ptr_type(AddressSpace::from(0)), "")
                        .unwrap()
                        .as_any_value_enum()
                }
                TypedIntLit::I8(x) => self
                    .ictx
                    .i8_type()
                    .const_int(x as u64, true)
                    .as_any_value_enum(),
                TypedIntLit::U8(x) => self
                    .ictx
                    .i8_type()
                    .const_int(x as u64, false)
                    .as_any_value_enum(),
                TypedIntLit::I16(x) => self
                    .ictx
                    .i16_type()
                    .const_int(x as u64, true)
                    .as_any_value_enum(),
                TypedIntLit::U16(x) => self
                    .ictx
                    .i16_type()
                    .const_int(x as u64, false)
                    .as_any_value_enum(),
                TypedIntLit::I32(x) => self
                    .ictx
                    .i32_type()
                    .const_int(x as u64, true)
                    .as_any_value_enum(),
                TypedIntLit::U32(x) => self
                    .ictx
                    .i32_type()
                    .const_int(x as u64, false)
                    .as_any_value_enum(),
                TypedIntLit::I64(x) => self
                    .ictx
                    .i64_type()
                    .const_int(x as u64, true)
                    .as_any_value_enum(),
                TypedIntLit::U64(x) => self
                    .ictx
                    .i64_type()
                    .const_int(x as u64, false)
                    .as_any_value_enum(),
                TypedIntLit::Bool(x) => self
                    .ictx
                    .bool_type()
                    .const_int(x as u64, false)
                    .as_any_value_enum(),
            },
            TirExpr::Access(expr, FieldAccessKind::Index(x)) => {
                let agg = self.expressions[&expr].into_struct_value();
                self.builder
                    .build_extract_value(agg, x, "")
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::Access(expr, FieldAccessKind::Symbol(field_name)) => {
                // check if its a pointer
                let agg = self.expressions[&expr];

                let t = self.tir_ctx.get_type_of_tir_expr(ctx, expr).unwrap();
                let mut ty = ctx.ctx.interner.get_conc_type(t);
                let is_ptr = if let ConcreteType::Ptr(inner) = ty {
                    ty = ctx.ctx.interner.get_conc_type(*inner);
                    Some(*inner)
                } else {
                    None
                };
                if let ConcreteType::SpecializedClass(sc_id) = ty {
                    let sc = ctx.ctx.interner.get_sc(*sc_id);
                    let index = sc
                        .fields
                        .iter()
                        .position(|elem| elem.name == field_name)
                        .unwrap() as u32;
                    if let Some(inner) = is_ptr {
                        let inner_ty = self.get_mono_ty(ctx, inner);
                        let ptr = self
                            .builder
                            .build_struct_gep(
                                BasicTypeEnum::try_from(inner_ty).unwrap(),
                                agg.into_pointer_value(),
                                index,
                                "",
                            )
                            .unwrap();
                        let field_ty = self
                            .tir_ctx
                            .get_type_of_tir_expr(ctx, original_expr)
                            .unwrap();
                        let field_ty = self.get_mono_ty(ctx, field_ty);
                        self.builder
                            .build_load(BasicTypeEnum::try_from(field_ty).unwrap(), ptr, "")
                            .unwrap()
                            .as_any_value_enum()
                    } else {
                        self.builder
                            .build_extract_value(agg.into_struct_value(), index, "")
                            .unwrap()
                            .as_any_value_enum()
                    }
                } else {
                    unreachable!()
                }
            }
            TirExpr::VarExpr(var_id) => {
                let (var_ty, var_ptr) = self.vars[&var_id];
                let value = self.builder.build_load(var_ty, var_ptr, "").unwrap();
                value.as_any_value_enum()
            }
            TirExpr::IntCast(int_ty, expr_id) => {
                let ty = self.get_mono_ty(ctx, int_ty);

                let int_ty = BasicTypeEnum::try_from(ty).unwrap().into_int_type();

                let int_expr = BasicValueEnum::try_from(self.expressions[&expr_id])
                    .unwrap()
                    .into_int_value();

                self.builder
                    .build_int_cast(int_expr, int_ty, "")
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::PtrCast(_, e) => {
                let e_val = self.expressions[&e];
                e_val.into_pointer_value().as_any_value_enum()
            }
            TirExpr::Tuple(exprs) => {
                let iw_exprs = exprs
                    .iter()
                    .map(|x| BasicValueEnum::try_from(self.expressions[x]).unwrap())
                    .collect::<Vec<_>>();
                let ty = self.tir_ctx.get_type_of_tir_expr(ctx, expr).unwrap();
                let t = self.get_mono_ty(ctx, ty).into_struct_type();

                let mut tuple_val = t.get_undef();
                for (i, iw_expr) in iw_exprs.into_iter().enumerate() {
                    tuple_val = self
                        .builder
                        .build_insert_value(tuple_val, iw_expr, i as u32, "")
                        .unwrap()
                        .into_struct_value();
                }
                tuple_val.as_any_value_enum()
            }
            TirExpr::BinOp { lhs, rhs, op } => {
                let lhs_val = BasicValueEnum::try_from(self.expressions[&lhs]).unwrap();
                let rhs_val = BasicValueEnum::try_from(self.expressions[&rhs]).unwrap();
                assert!(
                    (lhs_val.get_type().is_pointer_type())
                        || lhs_val.get_type() == rhs_val.get_type()
                        || lhs_val.get_type().is_int_type() && rhs_val.get_type().is_int_type(),
                    "\nLHS: {}\nRHS: {}",
                    lhs_val.get_type(),
                    rhs_val.get_type()
                );

                if lhs_val.get_type().is_pointer_type() {
                    match op {
                        NirBinOpKind::Add => {
                            let ptr_ty = self.tir_ctx.get_type_of_tir_expr(ctx, lhs).unwrap();
                            let inner = match ctx.ctx.interner.get_conc_type(ptr_ty) {
                                ConcreteType::Ptr(ty) => *ty,
                                _ => unreachable!(),
                            };
                            let inner = BasicTypeEnum::try_from(self.get_mono_ty(ctx, inner))
                                .unwrap_or(self.ictx.i8_type().as_basic_type_enum());

                            unsafe {
                                self.builder
                                    .build_gep(
                                        inner,
                                        lhs_val.into_pointer_value(),
                                        &[rhs_val.into_int_value()],
                                        "",
                                    )
                                    .unwrap()
                                    .as_any_value_enum()
                            }
                        }
                        NirBinOpKind::Sub => todo!(),
                        _ => unreachable!(),
                    }
                } else if lhs_val.get_type().is_pointer_type() {
                    match op {
                        NirBinOpKind::Add => todo!(),
                        NirBinOpKind::Sub => todo!(),
                        _ => unreachable!(),
                    }
                } else if matches!(
                    op,
                    NirBinOpKind::Geq
                        | NirBinOpKind::Leq
                        | NirBinOpKind::Gt
                        | NirBinOpKind::Lt
                        | NirBinOpKind::Equ
                        | NirBinOpKind::Dif
                ) {
                    self.builder
                        .build_int_compare(
                            match op {
                                NirBinOpKind::Geq => IntPredicate::SGE,
                                NirBinOpKind::Leq => IntPredicate::SLE,
                                NirBinOpKind::Gt => IntPredicate::SGT,
                                NirBinOpKind::Lt => IntPredicate::SLT,
                                NirBinOpKind::Equ => IntPredicate::EQ,
                                NirBinOpKind::Dif => IntPredicate::NE,
                                _ => unreachable!(),
                            },
                            lhs_val.into_int_value(),
                            rhs_val.into_int_value(),
                            "",
                        )
                        .unwrap()
                        .as_any_value_enum()
                } else {
                    // TODO: determine unsigned / signed
                    let opcode = match op {
                        NirBinOpKind::Add => InstructionOpcode::Add,
                        NirBinOpKind::Sub => InstructionOpcode::Sub,
                        NirBinOpKind::Mul => InstructionOpcode::Mul,
                        NirBinOpKind::Div => InstructionOpcode::SDiv,
                        NirBinOpKind::Mod => InstructionOpcode::SRem,
                        NirBinOpKind::LOr => todo!(),
                        NirBinOpKind::LAnd => todo!(),
                        NirBinOpKind::BOr => todo!(),
                        NirBinOpKind::BAnd => todo!(),
                        NirBinOpKind::BXor => todo!(),
                        NirBinOpKind::Equ
                        | NirBinOpKind::Dif
                        | NirBinOpKind::Geq
                        | NirBinOpKind::Leq
                        | NirBinOpKind::Gt
                        | NirBinOpKind::Lt => {
                            todo!()
                        }
                    };

                    self.builder
                        .build_binop(opcode, lhs_val, rhs_val, "")
                        .unwrap()
                        .as_any_value_enum()
                }
            }
            TirExpr::Funcall(fun_id, args) => {
                let (val, _) = self.funs[&fun_id].clone();
                let args_expr = args
                    .clone()
                    .iter()
                    .map(|x| BasicMetadataValueEnum::try_from(self.expressions[x]).unwrap())
                    .collect::<Vec<_>>();

                self.builder
                    .build_call(val, &args_expr[..], "")
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::StringLiteral(x) => {
                if let Some(strlit) = self.strlits.get(&x) {
                    strlit.as_any_value_enum()
                } else {
                    let escaped = &ctx.ctx.interner.get_string(x).0;
                    let unescaped = unescape::unescape(escaped.as_str()).unwrap();
                    let res = self
                        .builder
                        .build_global_string_ptr(unescaped.as_str(), "")
                        .unwrap();
                    self.strlits.insert(x, res);
                    res.as_any_value_enum()
                }
            }
            TirExpr::True => self
                .ictx
                .bool_type()
                .const_int(1, false)
                .as_any_value_enum(),
            TirExpr::False => self.ictx.bool_type().const_zero().as_any_value_enum(),
            TirExpr::PtrAccess(expr, FieldAccessKind::Index(x)) => {
                let ty = self.tir_ctx.get_type_of_tir_expr(ctx, expr).unwrap();
                let t = ctx.ctx.interner.get_conc_type(ty);
                let ty = match t {
                    ConcreteType::Ptr(x) => *x,
                    _ => unreachable!(),
                };
                let pointee = self.get_mono_ty(ctx, ty);
                let ptr = self.expressions[&expr];
                self.builder
                    .build_struct_gep(
                        BasicTypeEnum::try_from(pointee).unwrap(),
                        ptr.into_pointer_value(),
                        x,
                        "",
                    )
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::PtrAccess(expr, FieldAccessKind::Symbol(field_name)) => {
                let t = self.tir_ctx.get_type_of_tir_expr(ctx, expr).unwrap();
                let ty = ctx.ctx.interner.get_conc_type(t);
                let t = match ty {
                    ConcreteType::Ptr(x) => *x,
                    _ => unreachable!(),
                };
                let mut ty = ctx.ctx.interner.get_conc_type(t);

                let is_ptr = if let ConcreteType::Ptr(inner) = ty {
                    ty = ctx.ctx.interner.get_conc_type(*inner);
                    Some(*inner)
                } else {
                    None
                };
                if let ConcreteType::SpecializedClass(sc_id) = ty {
                    let sc = ctx.ctx.interner.get_sc(*sc_id);
                    let index = sc
                        .fields
                        .iter()
                        .position(|elem| elem.name == field_name)
                        .unwrap();

                    let pointee = self.get_mono_ty(ctx, t);

                    let ptr = self.expressions[&expr];
                    if let Some(inner) = is_ptr {
                        let inner_ty = self.get_mono_ty(ctx, inner);
                        let derefed = self
                            .builder
                            .build_load(pointee.into_pointer_type(), ptr.into_pointer_value(), "")
                            .unwrap();
                        self.builder
                            .build_struct_gep(
                                inner_ty.into_struct_type(),
                                derefed.into_pointer_value(),
                                index as u32,
                                "",
                            )
                            .unwrap()
                            .as_any_value_enum()
                    } else {
                        self.builder
                            .build_struct_gep(
                                BasicTypeEnum::try_from(pointee).unwrap(),
                                ptr.into_pointer_value(),
                                index as u32,
                                "",
                            )
                            .unwrap()
                            .as_any_value_enum()
                    }
                } else {
                    unreachable!()
                }
            }
            TirExpr::VarPtr(var_id) => self.vars[&var_id].1.as_any_value_enum(),
            TirExpr::Deref(val) => {
                let ptr = self.expressions[&val];
                let ty = self.tir_ctx.get_type_of_tir_expr(ctx, val).unwrap();
                let ty = TirCtx::inner_ptr_ty(ctx, ty).unwrap();
                let ty = self.get_mono_ty(ctx, ty);
                let ptr = ptr.into_pointer_value();
                self.builder
                    .build_load(BasicTypeEnum::try_from(ty).unwrap(), ptr, "")
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::Minus(x) => {
                let original = self.expressions[&x].into_int_value();
                self.builder
                    .build_int_neg(original, "")
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::Alloca(ty) => {
                let ty = self.get_mono_ty(ctx, ty);
                self.builder
                    .build_alloca(BasicTypeEnum::try_from(ty).unwrap(), "")
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::Subscript { ptr, index } => {
                let ptr_val = self.expressions[&ptr].into_pointer_value();
                let index = self.expressions[&index].into_int_value();
                let pointer_ty = self.tir_ctx.get_type_of_tir_expr(ctx, ptr).unwrap();
                let pointee_ty = match ctx.ctx.interner.get_conc_type(pointer_ty) {
                    ConcreteType::Ptr(id) => *id,
                    _ => unreachable!(),
                };
                let pointee_ty =
                    BasicTypeEnum::try_from(self.get_mono_ty(ctx, pointee_ty)).unwrap();
                let ptr = unsafe {
                    self.builder
                        .build_gep(pointee_ty, ptr_val, &[index], "")
                        .unwrap()
                };

                ptr.as_any_value_enum()
            }
        };
        println!("Inserting {:?}", expr);
        self.expressions.insert(expr, res.clone());
        res
    }

    fn translate(&mut self, ctx: &mut TyCtx<'ctx>, instr: &TirInstr) {
        if self
            .builder
            .get_insert_block()
            .unwrap()
            .get_terminator()
            .is_some()
        {
            // todo: issue warning maybe
            return;
        }
        match instr {
            TirInstr::Return(val) => {
                self.builder
                    .build_return(
                        val.as_ref()
                            .map(|v| {
                                let b: Box<dyn BasicValue> = Box::new(
                                    BasicValueEnum::try_from(self.expressions[v]).unwrap(),
                                );
                                b
                            })
                            .as_ref()
                            .map(|x| x.as_ref()),
                    )
                    .unwrap();
            }
            TirInstr::VarDecl(var_id) => {
                let decl = ctx.ctx.interner.get_variable(*var_id).clone();
                let ty = BasicTypeEnum::try_from(self.get_mono_ty(ctx, decl.ty)).unwrap();
                let name = format!("{}_ptr", ctx.ctx.interner.get_symbol(decl.name));

                let var_ptr = self.builder.build_alloca(ty, name.as_str()).unwrap();
                self.vars.insert(*var_id, (ty, var_ptr));
            }
            TirInstr::VarAssign(var_id, expr_id) => {
                let (_, var_ptr) = self.vars[var_id];
                let expr = BasicValueEnum::try_from(self.expressions[expr_id]).unwrap();
                self.builder.build_store(var_ptr, expr).unwrap();
            }
            TirInstr::Calculate(expr) => {
                self.calculate(ctx, *expr);
            }
            TirInstr::If(scope_id) => {
                let scope = ctx.ctx.interner.get_scope(*scope_id);
                let cond = match &scope.kind {
                    ScopeKind::If { cond } => cond,
                    x => unreachable!("{:?}", x),
                };
                let then_instrs = match &ctx.ctx.interner.get_scope(scope.children[0]).kind {
                    ScopeKind::Then(instrs) => instrs.clone(),
                    _ => unreachable!(),
                };
                let else_instrs = scope
                    .children
                    .get(1)
                    .map(|s| match &ctx.ctx.interner.get_scope(*s).kind {
                        ScopeKind::Else(instrs) => instrs.clone(),
                        _ => unreachable!(),
                    })
                    .unwrap_or(vec![]);

                let cond_val = self.expressions[&cond];
                let fn_id = ctx.get_current_fun().unwrap();
                let (fn_val, _) = self.funs[&fn_id];
                let then_bb = self.ictx.append_basic_block(fn_val, "then");
                let else_bb = self.ictx.append_basic_block(fn_val, "else");
                let merge_bb = self.ictx.append_basic_block(fn_val, "merge");

                self.builder
                    .build_conditional_branch(cond_val.into_int_value(), then_bb, else_bb)
                    .unwrap();

                self.builder.position_at_end(then_bb);
                for instr in &then_instrs {
                    self.translate(ctx, instr);
                }
                if let None = then_bb.get_terminator() {
                    self.builder.build_unconditional_branch(merge_bb).unwrap();
                }

                self.builder.position_at_end(else_bb);
                for instr in &else_instrs {
                    self.translate(ctx, instr);
                }
                if let None = else_bb.get_terminator() {
                    self.builder.build_unconditional_branch(merge_bb).unwrap();
                }
                self.builder.position_at_end(merge_bb);
            }
            TirInstr::Block(id) => {
                let scope = ctx.ctx.interner.get_scope(*id).clone();
                let instrs = match &scope.kind {
                    ScopeKind::Block(instr) => instr,
                    x => unreachable!("{:?}", x),
                };
                for instr in instrs {
                    self.translate(ctx, instr);
                }
            }
            TirInstr::While(scope_id) => {
                let scope = ctx.ctx.interner.get_scope(*scope_id);
                let cond_instrs = match &ctx.ctx.interner.get_scope(scope.children[0]).kind {
                    ScopeKind::WhileCond(instrs) => instrs.clone(),
                    _ => unreachable!(),
                };
                let (cond, body) = match &ctx.ctx.interner.get_scope(scope.children[1]).kind {
                    ScopeKind::WhileLoop(cond, body) => (cond.clone(), body.clone()),
                    _ => unreachable!(),
                };
                let fn_id = ctx.get_current_fun().unwrap();
                let (fn_val, _) = self.funs[&fn_id];

                let cond_bb = self.ictx.append_basic_block(fn_val, "while_cond");
                let body_bb = self.ictx.append_basic_block(fn_val, "while_body");
                let end_bb = self.ictx.append_basic_block(fn_val, "while_end");

                self.builder.build_unconditional_branch(cond_bb).unwrap();

                self.builder.position_at_end(cond_bb);
                for i in &cond_instrs {
                    self.translate(ctx, i);
                }
                self.builder
                    .build_conditional_branch(
                        self.expressions[&cond].into_int_value(),
                        body_bb,
                        end_bb,
                    )
                    .unwrap();

                self.builder.position_at_end(body_bb);
                for i in &body {
                    self.translate(ctx, i);
                }
                self.builder.build_unconditional_branch(cond_bb).unwrap();

                self.builder.position_at_end(end_bb);
            }
            TirInstr::Assign(ptr, val) => {
                let ptr = self.expressions[ptr];

                let val = self.expressions[val];
                println!("Module:{}", self.module.to_string());
                println!("PTR IS {}", ptr);
                self.builder
                    .build_store(
                        ptr.into_pointer_value(),
                        BasicValueEnum::try_from(val).unwrap(),
                    )
                    .unwrap();
            }
        }
    }
}
