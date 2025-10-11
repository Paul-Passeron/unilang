use std::collections::HashMap;

use inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::Module,
    targets::{TargetMachine, TargetTriple},
    types::{AnyType, AnyTypeEnum, AsTypeRef, BasicMetadataTypeEnum, FunctionType},
    values::{AnyValue, AnyValueEnum, AsValueRef, BasicValue, BasicValueEnum},
};

use crate::{
    common::{
        global_interner::{FunId, ScopeId, TirExprId, TyId},
        pass::Pass,
    },
    nir::interner::ConstructibleId,
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
    expressions: HashMap<TirExprId, inkwell::values::AnyValueEnum<'a>>,
    builder: Builder<'a>,
}

impl<'ctx, 'a> Pass<'ctx, ()> for MonoIRPass<'a> {
    type Output = ();

    fn run(&mut self, ctx: &mut TyCtx<'ctx>, _: ()) -> Result<Self::Output, TcError> {
        self.visit_all_scopes(ctx);
        println!("{}", self.module.print_to_string().to_string());

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
            expressions: HashMap::new(),
            builder,
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

        self.setup_function(ctx, fun_id);

        instrs.iter().for_each(|instr| self.translate(ctx, instr));
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
    fn get_mono_ty(&self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> AnyTypeEnum<'a> {
        let t = ctx.ctx.interner.get_conc_type(ty);
        match t {
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
        }
    }

    fn get_fun_type(&self, ctx: &mut TyCtx<'ctx>, id: FunId) -> FunctionType<'a> {
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

    fn setup_function(&mut self, ctx: &mut TyCtx<'ctx>, id: FunId) {
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
    }

    fn calculate(&mut self, ctx: &mut TyCtx<'ctx>, expr: TirExprId) -> AnyValueEnum {
        let e = ctx.ctx.interner.get_te(expr);
        let res = match e {
            TirExpr::Arg(_) => todo!(),
            TirExpr::TypedIntLit(typed_int_lit) => match typed_int_lit {
                TypedIntLit::Ptr(one_shot_id, x) => {
                    let intlit_ptr = self.ictx.i64_type().const_int(*x as u64, false);
                    self.builder
                        .build_int_to_ptr(intlit_ptr, self.ictx.ptr_type(AddressSpace::from(0)), "")
                        .unwrap()
                        .as_any_value_enum()
                }
                TypedIntLit::I8(x) => self
                    .ictx
                    .i8_type()
                    .const_int(*x as u64, true)
                    .as_any_value_enum(),
                TypedIntLit::U8(x) => self
                    .ictx
                    .i8_type()
                    .const_int(*x as u64, false)
                    .as_any_value_enum(),
                TypedIntLit::I16(x) => self
                    .ictx
                    .i16_type()
                    .const_int(*x as u64, true)
                    .as_any_value_enum(),
                TypedIntLit::U16(x) => self
                    .ictx
                    .i16_type()
                    .const_int(*x as u64, false)
                    .as_any_value_enum(),
                TypedIntLit::I32(x) => self
                    .ictx
                    .i32_type()
                    .const_int(*x as u64, true)
                    .as_any_value_enum(),
                TypedIntLit::U32(x) => self
                    .ictx
                    .i32_type()
                    .const_int(*x as u64, false)
                    .as_any_value_enum(),
                TypedIntLit::I64(x) => self
                    .ictx
                    .i64_type()
                    .const_int(*x as u64, true)
                    .as_any_value_enum(),
                TypedIntLit::U64(x) => self
                    .ictx
                    .i64_type()
                    .const_int(*x as u64, false)
                    .as_any_value_enum(),
                TypedIntLit::Bool(x) => self
                    .ictx
                    .bool_type()
                    .const_int(*x as u64, false)
                    .as_any_value_enum(),
            },
            TirExpr::Access(one_shot_id, field_access_kind) => todo!(),
            TirExpr::VarExpr(one_shot_id) => todo!(),
            TirExpr::IntCast(one_shot_id, one_shot_id1) => todo!(),
            TirExpr::PtrCast(one_shot_id, one_shot_id1) => todo!(),
            TirExpr::Tuple(one_shot_ids) => todo!(),
            TirExpr::BinOp { lhs, rhs, op } => todo!(),
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
            TirInstr::VarDecl(one_shot_id) => todo!(),
            TirInstr::Assign(one_shot_id, one_shot_id1) => todo!(),
            TirInstr::Calculate(expr) => {
                self.calculate(ctx, *expr);
            }
        }
    }
}
