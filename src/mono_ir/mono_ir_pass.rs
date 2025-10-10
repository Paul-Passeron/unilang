
// use crate::{
//     common::{
//         global_interner::{FunId, ScopeId, TyId},
//         pass::Pass,
//     },
//     nir::interner::ConstructibleId,
//     ty::{
//         PrimitiveTy, TcError, TyCtx,
//         scope::ScopeKind,
//         tir::{ConcreteType, TirInstr},
//     },
// };

// pub struct ClirPass {
//     triple: Triple,
// }

// impl<'ctx> Pass<'ctx, ()> for ClirPass {
//     type Output = ();

//     fn run(&mut self, ctx: &mut TyCtx<'ctx>, _: ()) -> Result<Self::Output, TcError> {
//         self.visit_all_scopes(ctx);
//         Ok(())
//     }
// }

// impl<'ctx> ClirPass {
//     pub fn new() -> Self {
//         Self {
//             triple: Triple::host(),
//         }
//     }

//     pub fn visit_all_scopes(&mut self, ctx: &mut TyCtx<'ctx>) {
//         fn aux<'ctx>(this: &mut ClirPass, ctx: &mut TyCtx<'ctx>) {
//             if matches!(&ctx.get_last_scope().kind, ScopeKind::Function(_, _, _)) {
//                 this.visit_fundef(ctx);
//             }

//             for child in &ctx.get_last_scope().children.clone() {
//                 ctx.with_scope_id(*child, |ctx| {
//                     aux(this, ctx);
//                 })
//             }
//         }
//         ctx.with_scope_id(ScopeId::new(0), |ctx| {
//             aux(self, ctx);
//         });
//     }

//     fn visit_fundef(&mut self, ctx: &mut TyCtx<'ctx>) {
//         let fun_scope = ctx.get_current_fun_scope().unwrap();
//         let (fun_id, instrs) = match &ctx.ctx.interner.get_scope(fun_scope).kind {
//             ScopeKind::Function(fun_id, _, instrs) => (*fun_id, instrs.clone()),
//             _ => unreachable!(),
//         };

//         self.setup_function(ctx, fun_id);

//         instrs.iter().for_each(|instr| self.translate(ctx, instr));
//     }

//     fn get_clir_for_primitive(p: PrimitiveTy) -> Option<_> {
//         match p {
//             PrimitiveTy::Void => None,
//             PrimitiveTy::I8 => prelude::Type::int(8),
//             PrimitiveTy::I16 => prelude::Type::int(16),
//             PrimitiveTy::I32 => prelude::Type::int(32),
//             PrimitiveTy::I64 => prelude::Type::int(64),
//             PrimitiveTy::U8 => prelude::Type::int(8),
//             PrimitiveTy::U16 => prelude::Type::int(16),
//             PrimitiveTy::U32 => prelude::Type::int(32),
//             PrimitiveTy::U64 => prelude::Type::int(64),
//             PrimitiveTy::Bool => prelude::Type::int(1),
//         }
//     }

//     /// This returns a vec because it destructures tuples and structs
//     fn get_clir_ty(&mut self, ctx: &mut TyCtx<'ctx>, ty: TyId) -> Vec<prelude::Type> {
//         let t = ctx.ctx.interner.get_conc_type(ty);
//         match t {
//             ConcreteType::SpecializedClass(one_shot_id) => todo!(),
//             ConcreteType::Primitive(primitive_ty) => Self::get_clir_for_primitive(*primitive_ty)
//                 .into_iter()
//                 .collect(),
//             ConcreteType::Ptr(_) => vec![prelude::Type::triple_pointer_type(&self.triple)],
//             ConcreteType::Tuple(tys) => tys
//                 .clone()
//                 .into_iter()
//                 .flat_map(|ty| self.get_clir_ty(ctx, ty))
//                 .collect(),
//         }
//     }

//     fn setup_function(&mut self, ctx: &mut TyCtx<'ctx>, id: FunId) {
//         todo!()
//     }

//     fn translate(&mut self, ctx: &mut TyCtx<'ctx>, instr: &TirInstr) {
//         todo!()
//     }
// }
