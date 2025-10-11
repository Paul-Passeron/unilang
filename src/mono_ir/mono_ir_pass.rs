use std::collections::HashMap;

use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::Module,
    targets::{TargetMachine, TargetTriple},
    types::{AnyType, AnyTypeEnum, AsTypeRef, BasicMetadataTypeEnum, BasicTypeEnum, FunctionType},
    values::{
        AnyValue, AnyValueEnum, AsValueRef, BasicValue, BasicValueEnum, FunctionValue,
        InstructionOpcode, PointerValue,
    },
};

use crate::{
    common::{
        global_interner::{FunId, ScopeId, TirExprId, TyId, VariableId},
        pass::Pass,
    },
    nir::{interner::ConstructibleId, nir::NirBinOpKind},
    ty::{
        PrimitiveTy, TcError, TyCtx,
        scope::ScopeKind,
        tir::{ConcreteType, SCField, TirCtx, TirExpr, TirInstr, TypedIntLit},
    },
};

pub struct MonoIRPass<'a> {
    triple: TargetTriple,
    ictx: &'a Context,
    tir_ctx: &'a TirCtx,
    module: Module<'a>,
    builder: Builder<'a>,

    expressions: HashMap<TirExprId, AnyValueEnum<'a>>,
    vars: HashMap<VariableId, (BasicTypeEnum<'a>, PointerValue<'a>)>,
    tys: HashMap<TyId, AnyTypeEnum<'a>>,
}

impl<'ctx, 'a> Pass<'ctx, ()> for MonoIRPass<'a> {
    type Output = ();

    fn run(&mut self, ctx: &mut TyCtx<'ctx>, _: ()) -> Result<Self::Output, TcError> {
        self.visit_all_scopes(ctx);
        println!("{}", self.module.print_to_string().to_string());
        self.module.verify().unwrap();
        Ok(())
    }
}

impl<'ctx, 'a> MonoIRPass<'a> {
    pub fn new(name: &str, ictx: &'a Context, tir_ctx: &'a TirCtx) -> Self {
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
        }
    }

    pub fn visit_all_scopes(&mut self, ctx: &mut TyCtx<'ctx>) {
        fn aux<'ctx>(this: &mut MonoIRPass, ctx: &mut TyCtx<'ctx>) {
            if matches!(&ctx.get_last_scope().kind, ScopeKind::Function(_, _, _)) {
                this.visit_fundef(ctx);
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
    }

    fn visit_fundef(&mut self, ctx: &mut TyCtx<'ctx>) {
        let fun_scope = ctx.get_current_fun_scope().unwrap();
        let (fun_id, instrs) = match &ctx.ctx.interner.get_scope(fun_scope).kind {
            ScopeKind::Function(fun_id, _, instrs) => (*fun_id, instrs.clone()),
            _ => unreachable!(),
        };

        let fn_val = self.setup_function(ctx, fun_id);
        instrs.iter().for_each(|instr| self.translate(ctx, instr));
        fn_val
            .get_last_basic_block()
            .inspect(|bb| match bb.get_terminator() {
                None => {
                    self.builder.build_return(None).unwrap();
                }
                _ => (),
            });
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
    fn get_mono_ty(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> AnyTypeEnum<'a> {
        if self.tys.contains_key(&ty) {
            return self.tys[&ty];
        }
        let t = ctx.ctx.interner.get_conc_type(ty);
        let res = match t {
            ConcreteType::SpecializedClass(_) => todo!(),
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

    fn get_fun_type(&mut self, ctx: &mut TyCtx<'ctx>, id: FunId) -> FunctionType<'a> {
        let proto = self.tir_ctx.protos[&id].clone();
        let args = proto
            .params
            .iter()
            .map(|SCField { ty, .. }| {
                let ty = self.get_mono_ty(ctx, *ty);
                unsafe { BasicMetadataTypeEnum::new(ty.as_type_ref()) }
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

    fn get_fun_name(&self, ctx: &mut TyCtx<'ctx>, id: FunId) -> String {
        let proto = self.tir_ctx.protos[&id].clone();
        ctx.ctx.interner.get_symbol(proto.name).clone()
    }

    fn setup_function(&mut self, ctx: &mut TyCtx<'ctx>, id: FunId) -> FunctionValue<'a> {
        let proto = self.tir_ctx.protos[&id].clone();
        let fun_type = self.get_fun_type(ctx, id);
        let fun_name = self.get_fun_name(ctx, id);
        let fn_val = self.module.add_function(fun_name.as_ref(), fun_type, None);

        let entry_basic_block = self.ictx.append_basic_block(fn_val, "entry");
        self.builder.position_at_end(entry_basic_block);
        assert!(proto.params.len() == 0);
        println!(
            "Function type for {}: {}",
            ctx.ctx.interner.get_symbol(proto.name),
            fun_type
        );
        fn_val
    }

    fn calculate(&mut self, ctx: &mut TyCtx<'ctx>, expr: TirExprId) -> AnyValueEnum {
        let e = ctx.ctx.interner.get_te(expr).clone();
        let res = match e {
            TirExpr::Arg(_) => todo!(),
            TirExpr::TypedIntLit(typed_int_lit) => match typed_int_lit {
                TypedIntLit::Ptr(one_shot_id, x) => {
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
            TirExpr::Access(one_shot_id, field_access_kind) => todo!(),
            TirExpr::VarExpr(var_id) => {
                let (var_ty, var_ptr) = self.vars[&var_id];
                let var_decl = ctx.ctx.interner.get_variable(var_id);
                let value = self.builder.build_load(var_ty, var_ptr, "").unwrap();
                value.as_any_value_enum()
            }
            TirExpr::IntCast(int_ty, expr_id) => {
                let ty = self.get_mono_ty(ctx, int_ty);
                let int_ty = unsafe { BasicTypeEnum::new(ty.as_type_ref()) }.into_int_type();

                let expr = &self.expressions[&expr_id];
                let int_expr = unsafe { BasicValueEnum::new(expr.as_value_ref()) }.into_int_value();

                self.builder
                    .build_int_cast(int_expr, int_ty, "")
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::PtrCast(one_shot_id, one_shot_id1) => todo!(),
            TirExpr::Tuple(one_shot_ids) => todo!(),
            TirExpr::BinOp { lhs, rhs, op } => {
                let lhs_val = unsafe { BasicValueEnum::new(self.expressions[&lhs].as_value_ref()) };
                let rhs_val = unsafe { BasicValueEnum::new(self.expressions[&rhs].as_value_ref()) };
                assert!(
                    (!lhs_val.get_type().is_pointer_type())
                        || lhs_val.get_type() == rhs_val.get_type(),
                );

                // TODO: determine unsigned / signed
                let opcode = match op {
                    NirBinOpKind::Add => InstructionOpcode::Add,
                    NirBinOpKind::Sub => InstructionOpcode::Sub,
                    NirBinOpKind::Mul => InstructionOpcode::Mul,
                    NirBinOpKind::Div => InstructionOpcode::SDiv,
                    NirBinOpKind::Mod => InstructionOpcode::SRem,
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
                    NirBinOpKind::Lt => {
                        todo!()
                    }
                };

                self.builder
                    .build_binop(opcode, lhs_val, rhs_val, "")
                    .unwrap()
                    .as_any_value_enum()
            }
            TirExpr::Funcall(one_shot_id, one_shot_ids) => todo!(),
            TirExpr::StringLiteral(one_shot_id) => todo!(),
        };
        self.expressions.insert(expr, res.clone());
        res
    }

    fn translate(&mut self, ctx: &mut TyCtx<'ctx>, instr: &TirInstr) {
        match instr {
            TirInstr::Return(val) => {
                self.builder
                    .build_return(
                        val.as_ref()
                            .map(|v| unsafe {
                                let b: Box<dyn BasicValue> = Box::new(BasicValueEnum::new(
                                    self.expressions[v].as_value_ref(),
                                ));
                                b
                            })
                            .as_ref()
                            .map(|x| x.as_ref()),
                    )
                    .unwrap();
            }
            TirInstr::VarDecl(var_id) => {
                let decl = ctx.ctx.interner.get_variable(*var_id).clone();
                let ty =
                    unsafe { BasicTypeEnum::new(self.get_mono_ty(ctx, decl.ty).as_type_ref()) };
                let name = format!("{}_ptr", ctx.ctx.interner.get_symbol(decl.name));

                let var_ptr = self.builder.build_alloca(ty, name.as_str()).unwrap();
                self.vars.insert(*var_id, (ty, var_ptr));
            }
            TirInstr::Assign(var_id, expr_id) => {
                let (_, var_ptr) = self.vars[var_id];
                let expr = unsafe { BasicValueEnum::new(self.expressions[expr_id].as_value_ref()) };
                self.builder.build_store(var_ptr, expr).unwrap();
            }
            TirInstr::Calculate(expr) => {
                self.calculate(ctx, *expr);
            }
        }
    }
}
