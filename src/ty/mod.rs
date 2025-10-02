use std::{collections::HashMap, rc::Rc};

use strum::{EnumIter, IntoEnumIterator};

use crate::{
    nir::{
        context::GlobalContext,
        interner::{Interner, ItemId, ScopeId, Symbol, TyId, TypeExprId, TypeInterner},
        nir::NirType,
    },
    ty::scope::{Definition, Scope, ScopeKind, TypeExpr},
};

pub mod pass;
pub mod scope;
pub mod surface_resolution;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructField {
    pub name: Symbol,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumIter)]
pub enum PrimitiveTy {
    Void,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TcTy {
    Ptr(TyId),
    Primitive(PrimitiveTy),
    Struct { fields: Vec<StructField> },
    Tuple(Vec<TyId>),
    Unresolved(NirType),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TcParam {
    pub name: Symbol,
    pub ty: TypeExprId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TcFunProto {
    pub name: Symbol,
    pub params: Vec<TcParam>,
    pub return_ty: TypeExprId,
    pub variadic: bool,
}

#[derive(Debug)]
pub struct TyCtx<'ctx> {
    pub types: HashMap<TyId, NirType>,
    pub methods: HashMap<TyId, Vec<TcFunProto>>,
    pub current_scope: ScopeId,
    pub ctx: &'ctx mut GlobalContext,
}

#[derive(Debug)]
pub enum TcError {
    Todo,
    NameNotFound(Symbol),
    Aggregate(Vec<(ItemId, TcError)>),
}

impl PrimitiveTy {
    pub fn get_name(&self) -> &str {
        match self {
            PrimitiveTy::Void => "void",
            PrimitiveTy::I8 => "i8",
            PrimitiveTy::I16 => "i16",
            PrimitiveTy::I32 => "i32",
            PrimitiveTy::I64 => "i64",
            PrimitiveTy::U8 => "u8",
            PrimitiveTy::U16 => "u16",
            PrimitiveTy::U32 => "u32",
            PrimitiveTy::U64 => "u64",
            PrimitiveTy::Bool => "bool",
        }
    }

    const INTEGERS: &[PrimitiveTy] = &[
        PrimitiveTy::I8,
        PrimitiveTy::I16,
        PrimitiveTy::I32,
        PrimitiveTy::I64,
        PrimitiveTy::U8,
        PrimitiveTy::U16,
        PrimitiveTy::U32,
        PrimitiveTy::U64,
        PrimitiveTy::Bool,
    ];

    fn size(&self) -> usize {
        match &self {
            PrimitiveTy::Void => 0,
            PrimitiveTy::I8 => 1,
            PrimitiveTy::I16 => 2,
            PrimitiveTy::I32 => 4,
            PrimitiveTy::I64 => 8,
            PrimitiveTy::U8 => 1,
            PrimitiveTy::U16 => 2,
            PrimitiveTy::U32 => 4,
            PrimitiveTy::U64 => 8,
            PrimitiveTy::Bool => 1,
        }
    }
}

impl TcTy {
    pub fn get_size(&self, _inter: &TypeInterner) -> usize {
        match &self {
            TcTy::Ptr(_) => std::mem::size_of::<*const u8>(),
            TcTy::Primitive(primitive_ty) => primitive_ty.size(),
            TcTy::Struct { fields } => {
                todo!("{fields:#?}")
            }
            TcTy::Tuple(_) => todo!(),
            TcTy::Unresolved(_) => todo!(),
        }
    }
}

impl<'ctx> TyCtx<'ctx> {
    fn declare_type(&mut self, val: TcTy) -> TyId {
        if let Some(id) = self.ctx.interner.type_interner.contains(&val) {
            id
        } else {
            let ty = self.ctx.interner.type_interner.insert(val);
            self.methods.insert(ty, vec![]);
            ty
        }
    }

    fn declare_primitive_types(&mut self) {
        let create_alias = |this: &mut Self, ty, name: &str| {
            let symb = this.ctx.interner.symbol_interner.insert(name.to_string());
            let res = (
                symb,
                Rc::new(Definition::Type(
                    this.ctx
                        .interner
                        .type_expr_interner
                        .insert(TypeExpr::Resolved(ty)),
                )),
            );
            this.get_last_scope_mut().definitions.push(res);
        };

        for prim in PrimitiveTy::iter() {
            let ty = self.declare_type(TcTy::Primitive(prim));
            create_alias(self, ty, prim.get_name());
        }

        let int_ty = self
            .ctx
            .interner
            .type_interner
            .contains(&TcTy::Primitive(PrimitiveTy::I32))
            .unwrap();
        create_alias(self, int_ty, "int");

        let usize_ty = self
            .ctx
            .interner
            .type_interner
            .contains(&TcTy::Primitive(PrimitiveTy::U32))
            .unwrap();
        create_alias(self, usize_ty, "usize");

        let char_ty = self
            .ctx
            .interner
            .type_interner
            .contains(&TcTy::Primitive(PrimitiveTy::U8))
            .unwrap();
        create_alias(self, char_ty, "char");
    }

    // fn populate_integer_ty(&mut self, prim: PrimitiveTy) {
    //     let ty = self
    //         .ctx
    //         .interner
    //         .type_interner
    //         .contains(&TcTy::Primitive(prim))
    //         .unwrap();

    //     let builtin_methods = self.get_methods_for_builtin(ty);

    //     let int_methods = self.get_methods_for_integer(ty);

    //     let methods = builtin_methods.into_iter().chain(int_methods.into_iter());

    //     for m in methods {
    //         if let Err(_) = self.add_method(ty, m) {
    //             panic!("Could not add builtin method in builtin type, this is a compiler bug.");
    //         }
    //     }
    // }

    // fn populate_void(&mut self) {
    //     let ty = self
    //         .ctx
    //         .interner
    //         .type_interner
    //         .contains(&TcTy::Primitive(PrimitiveTy::Void))
    //         .unwrap();

    //     let methods = self.get_methods_for_builtin(ty);

    //     for m in methods {
    //         if let Err(_) = self.add_method(ty, m) {
    //             panic!("Could not add builtin method in builtin type, this is a compiler bug.");
    //         }
    //     }
    // }

    pub fn add_builtins(&mut self) {
        self.declare_primitive_types();
        // for prim in PrimitiveTy::INTEGERS {
        //     self.populate_integer_ty(*prim);
        // }
        // self.populate_void();
    }

    fn symb(&mut self, name: &str) -> Symbol {
        self.ctx.interner.insert_symbol(&name.to_string())
    }

    fn get_symb(&self, s: &str) -> Symbol {
        self.ctx.interner.get_symbol_for(&s.to_string()).unwrap()
    }

    // fn get_methods_for_builtin(&mut self, _ty: TyId) -> Vec<TcFunProto> {
    //     let size_fun_name = self.symb("__builtin_size");
    //     let size_fun = TcFunProto {
    //         name: size_fun_name,
    //         params: vec![],
    //         return_ty: self
    //             .ctx
    //             .interner
    //             .type_interner
    //             .contains(&TcTy::Primitive(PrimitiveTy::U32))
    //             .unwrap(),
    //         variadic: false,
    //     };
    //     vec![size_fun]
    // }

    // fn get_methods_for_integer(&mut self, _ty: TyId) -> Vec<TcFunProto> {
    //     vec![]
    // }

    pub fn new(ctx: &'ctx mut GlobalContext) -> Self {
        let first_scope = Scope {
            kind: ScopeKind::Global,
            parent: None,
            children: Vec::new(),
            definitions: Vec::new(),
        };

        let scope_id = ctx.interner.scope_interner.insert(first_scope);

        let mut res = Self {
            types: HashMap::new(),
            methods: HashMap::new(),
            current_scope: scope_id,
            ctx,
        };
        res.add_builtins();
        res
    }

    // pub fn visit_program(&mut self, program: &NirProgram) -> Result<Strategy::Output, TcError> {
    //     let items = program
    //         .0
    //         .iter()
    //         .map(|id| (*id, self.ctx.interner.get_item(*id).clone()))
    //         .collect::<Vec<_>>();
    //     self.visit_item_group(items)
    // }

    // pub fn visit_item_group(
    //     &mut self,
    //     items: Vec<(ItemId, NirItem)>,
    // ) -> Result<Strategy::Output, TcError> {
    //     let mut successes = vec![];
    //     let mut temp_interner: HashMap<ItemId, NirItem, RandomState> = HashMap::from_iter(items);

    //     let mut working_stack: Vec<_> = temp_interner.keys().copied().collect();
    //     let mut errors = vec![];
    //     while working_stack.len() > 0 {
    //         errors.clear();
    //         let mut new_working_stack = vec![];
    //         for id in &working_stack {
    //             let interner = self.ctx.interner.clone();
    //             let current = self.current_scope;

    //             let item = temp_interner.get_mut(id).unwrap();
    //             let iteration = match item {
    //                 NirItem::Function(fdef) => self.visit_fundef(fdef),
    //                 NirItem::Module(mdef) => self.visit_module(mdef),
    //                 NirItem::Class(cdef) => self.visit_class(cdef),
    //                 NirItem::Trait(tdef) => self.visit_trait(tdef),
    //                 NirItem::Impl(impl_block) => self.visit_impl(impl_block),
    //                 NirItem::Method(_) => unreachable!(),
    //             };
    //             if iteration.is_err() {
    //                 new_working_stack.push(*id);
    //                 errors.push((*id, iteration.unwrap_err()));

    //                 self.ctx.interner = interner;
    //                 self.current_scope = current;
    //             } else {
    //                 successes.push(iteration.unwrap());
    //             }
    //         }

    //         let current_set: HashSet<ItemId, RandomState> = HashSet::from_iter(working_stack);
    //         let new_set: HashSet<ItemId, RandomState> =
    //             HashSet::from_iter(new_working_stack.iter().copied());
    //         working_stack = new_working_stack;
    //         if current_set == new_set {
    //             break; // No progress made, we must stop
    //         }
    //     }
    //     if !working_stack.is_empty() {
    //         Err(TcError::Aggregate(errors))
    //     } else {
    //         Ok(Strategy::Output::from_successes(successes))
    //     }
    // }

    fn get_type_string(&self, _ty: &TypeExpr) -> String {
        todo!()
    }

    pub fn print_error(&mut self, _error: &TcError) {
        todo!()
    }

    // fn visit_type(&mut self, ty: &mut NirType) -> Result<TyId, TcError> {
    //     let res = match &mut ty.kind {
    //         NirTypeKind::Ptr(t) => {
    //             let inner = self.visit_type(t.as_mut())?;
    //             Ok(self.ctx.interner.type_interner.insert(TcTy::Ptr(inner)))
    //         }
    //         NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
    //             let def = self
    //                 .get_last_scope()
    //                 .get_definition_for_symbol(*name, &self.ctx.interner.scope_interner);
    //             match def {
    //                 Some(Definition::Type(TypeKind::Resolved(id))) => Ok(id),
    //                 Some(Definition::Class(_)) => {
    //                     // let c = self.ctx.interner.class_interner.get(id);
    //                     // if c.templates.len() != 0 {
    //                     //     panic!()
    //                     // }

    //                     let expr = self.get_type_expr(ty)?;
    //                     self.resolve_type_expr(&expr)
    //                 }
    //                 _ => todo!(),
    //             }
    //         }
    //         NirTypeKind::Named { .. } => todo!("Handle generic types"),
    //         NirTypeKind::Tuple(_nir_types) => todo!(),
    //     }?;
    //     Ok(res)
    // }

    fn is_type_primitive(&self, ty: TyId) -> bool {
        let t = self.ctx.interner.type_interner.get(ty);
        match &t {
            TcTy::Primitive(_) => true,
            _ => false,
        }
    }

    fn get_size(&self, ty: TyId) -> usize {
        let t = self.ctx.interner.type_interner.get(ty);
        t.get_size(&self.ctx.interner.type_interner)
    }

    fn is_type_ptr(&mut self, ty: TyId) -> bool {
        let t = self.ctx.interner.type_interner.get(ty);
        matches!(t, TcTy::Ptr(_))
    }

    // fn get_type_of_binop(&mut self, left: ExprId, right: ExprId) -> Result<TyId, TcError> {
    //     let tl = self.get_type_of_expr(left)?;
    //     let tr = self.get_type_of_expr(right)?;
    //     if self.is_type_primitive(tl) && self.is_type_primitive(tr) {
    //         if self.get_size(tl) > self.get_size(tr) {
    //             Ok(tl)
    //         } else {
    //             Ok(tr)
    //         }
    //     } else {
    //         if self.is_type_primitive(tl) && self.is_type_ptr(tr) {
    //             Ok(tr)
    //         } else if self.is_type_primitive(tr) && self.is_type_ptr(tl) {
    //             Ok(tl)
    //         } else {
    //             todo!()
    //         }
    //     }
    // }

    // fn get_type_of_expr(&mut self, expr: ExprId) -> Result<TyId, TcError> {
    //     if self.expr_types.contains_key(&expr) {
    //         return Ok(*&self.expr_types[&expr]);
    //     }

    //     let ast = self.ctx.interner.expr_interner.get(expr).clone();

    //     let res = match &ast.kind {
    //         NirExprKind::Literal(nir_literal) => match nir_literal {
    //             NirLiteral::IntLiteral(_num) => Ok(self.aliases[&self.get_symb("i64")]),
    //             NirLiteral::FloatLiteral(_my_float) => todo!(),
    //             NirLiteral::StringLiteral(_string_literal) => {
    //                 let char_ty = self.get_simple_named("char").unwrap();
    //                 let ty = TcTy::Ptr(char_ty);
    //                 Ok(self.ctx.interner.type_interner.insert(ty))
    //             }
    //             NirLiteral::CharLiteral(_) => Ok(self.get_simple_named("char").unwrap()),
    //         },
    //         NirExprKind::BinOp(op) => {
    //             let l = op.left;
    //             let r = op.right;
    //             self.get_type_of_binop(l, r)
    //         }
    //         NirExprKind::UnOp { .. } => todo!(),
    //         NirExprKind::Call(call) => match call.called.receiver {
    //             Some(_) => todo!(),
    //             None => {
    //                 let scope = self.get_last_scope();
    //                 let def = scope.get_definition_for_symbol(
    //                     call.called.called,
    //                     &self.ctx.interner.scope_interner,
    //                 );
    //                 if def.is_none() {
    //                     return Err(TcError::NameNotFound(call.called.called));
    //                 }
    //                 let f = match def.unwrap() {
    //                     Definition::Function(f) => f,
    //                     _ => return Err(TcError::NotAFunction(call.called.called)),
    //                 };
    //                 let proto = self.ctx.interner.fun_interner.get(f).clone();
    //                 let return_ty = proto.return_ty;

    //                 if proto.params.len() > call.args.len()
    //                     || (!proto.variadic && proto.params.len() != call.args.len())
    //                 {
    //                     return Err(TcError::BadNumberOfArgs {
    //                         fun: f,
    //                         got: call.args.len(),
    //                     });
    //                 }

    //                 for (i, TcParam { ty, .. }) in proto.params.iter().enumerate() {
    //                     let arg = call.args[i];
    //                     let expr_ty = self.get_type_of_expr(arg)?;
    //                     if !self.type_is_coercible(expr_ty, *ty) {
    //                         return Err(TcError::ExprNotCoercible {
    //                             ty: *ty,
    //                             expr: expr_ty,
    //                         });
    //                     }
    //                 }

    //                 Ok(return_ty)
    //             }
    //         },
    //         NirExprKind::Subscript { .. } => todo!(),
    //         NirExprKind::Access { .. } => todo!(),
    //         NirExprKind::Named(symb) => {
    //             let def = self
    //                 .get_last_scope()
    //                 .get_definition_for_symbol(*symb, &self.ctx.interner.scope_interner);
    //             if def.is_none() {
    //                 return Err(TcError::NameNotFound(*symb));
    //             }
    //             let var_id = match def.unwrap() {
    //                 Definition::Variable(id) => id,
    //                 x => return Err(TcError::IsNotExpr(x)),
    //             };

    //             let var = self.ctx.interner.variable_interner.get(var_id);

    //             let ty = self
    //                 .get_type_of_symb_in_pattern(&var.name, *symb, var.ty)
    //                 .unwrap();

    //             Ok(ty)
    //         }
    //         NirExprKind::PostIncr(_expr_id) => todo!(),
    //         NirExprKind::PreIncr(_expr_id) => todo!(),
    //         NirExprKind::PostDecr(_expr_id) => todo!(),
    //         NirExprKind::PreDecr(_expr_id) => todo!(),
    //         NirExprKind::AddrOf(_expr_id) => todo!(),
    //         NirExprKind::Deref(_expr_id) => todo!(),
    //         NirExprKind::SizeOf(_nir_type) => todo!(),
    //         NirExprKind::StringOf(_nir_type) => todo!(),
    //         NirExprKind::Minus(_expr_id) => todo!(),
    //         NirExprKind::Not(_expr_id) => todo!(),
    //         NirExprKind::New { .. } => todo!(),
    //         NirExprKind::As { ty, expr } => {
    //             todo!()
    //         }
    //         NirExprKind::Tuple(_expr_ids) => todo!(),
    //         NirExprKind::Range { .. } => todo!(),
    //     };

    //     match res {
    //         Ok(x) => {
    //             self.expr_types.insert(expr, x);
    //         }
    //         _ => (),
    //     };
    //     res
    // }

    // fn type_is_coercible(&mut self, source: TyId, dest: TyId) -> bool {
    //     if source == dest {
    //         true
    //     } else {
    //         let source = self.ctx.interner.type_interner.get(source);
    //         let dest = self.ctx.interner.type_interner.get(dest);
    //         match (source, dest) {
    //             (TcTy::Primitive(_), TcTy::Primitive(_)) => true,
    //             (TcTy::Ptr(_), TcTy::Ptr(_)) => true,
    //             (TcTy::Ptr(_), TcTy::Primitive(_)) => true,
    //             (TcTy::Primitive(_), TcTy::Ptr(_)) => true,
    //             _ => todo!(),
    //         }
    //     }
    // }

    // fn visit_pattern(&self, pat: &NirPattern) -> Pattern {
    //     match &pat.kind {
    //         NirPatternKind::Wildcard => Pattern::Wildcard,
    //         NirPatternKind::Symbol(symbol) => Pattern::Symbol(*symbol),
    //         NirPatternKind::Tuple(nir_patterns) => {
    //             Pattern::Tuple(nir_patterns.iter().map(|x| self.visit_pattern(x)).collect())
    //         }
    //     }
    // }

    fn get_last_scope_mut(&mut self) -> &mut Scope {
        self.ctx.interner.scope_interner.get_mut(self.current_scope)
    }

    fn get_last_scope(&self) -> &Scope {
        self.ctx.interner.scope_interner.get(self.current_scope)
    }

    // fn declare_variable(&mut self, pattern: Pattern, expr: VarExpr, ty: TyId) {
    //     let var_decl = VarDecl {
    //         name: pattern.clone(),
    //         ty,
    //         expr,
    //     };

    //     let id = self.ctx.interner.variable_interner.insert(var_decl);
    //     self.declare_variable_impl(&pattern, id);
    // }

    // fn declare_variable_impl(&mut self, pattern: &Pattern, id: VariableId) {
    //     match pattern {
    //         Pattern::Wildcard => (),
    //         Pattern::Symbol(symbol) => self
    //             .get_last_scope_mut()
    //             .definitions
    //             .push((*symbol, Definition::Variable(id))),
    //         Pattern::Tuple(patterns) => patterns.iter().for_each(|x| {
    //             self.declare_variable_impl(x, id);
    //         }),
    //     }
    // }

    // fn inner<T, V>(x: Option<Result<T, V>>) -> Result<Option<T>, V> {
    //     match x {
    //         Some(Ok(x)) => Ok(Some(x)),
    //         None => Ok(None),
    //         Some(Err(x)) => Err(x),
    //     }
    // }

    // fn visit_stmt(&mut self, stmt: &mut NirStmt) -> Result<(), TcError> {
    //     match &mut stmt.kind {
    //         NirStmtKind::Expr(expr) => {
    //             self.get_type_of_expr(*expr)?;
    //             Ok(())
    //         }
    //         NirStmtKind::Block(_nir_stmts) => todo!(),
    //         NirStmtKind::If { .. } => todo!(),
    //         NirStmtKind::While { .. } => todo!(),
    //         NirStmtKind::For { .. } => todo!(),
    //         NirStmtKind::Let(decl) => {
    //             let pattern = self.visit_pattern(&decl.pattern);
    //             let expected_type = Self::inner(decl.ty.as_mut().map(|ty| self.visit_type(ty)))?;
    //             let actual_type = Self::inner(decl.value.map(|x| self.get_type_of_expr(x)))?;
    //             let ty = match (expected_type, actual_type) {
    //                 (Some(x), None) => x,
    //                 (None, Some(x)) => x,
    //                 (Some(x), Some(y)) => {
    //                     if self.type_is_coercible(y, x) {
    //                         x
    //                     } else {
    //                         todo!("report error of var decl mismatched types")
    //                     }
    //                 }
    //                 (None, None) => panic!("Type inference is not supported"),
    //             };
    //             self.declare_variable(pattern, VarExpr::Expr(decl.value), ty);
    //             Ok(())
    //         }
    //         NirStmtKind::Assign { .. } => todo!(),
    //         NirStmtKind::Return { value } => {
    //             let return_ty = self.get_return_type();
    //             match (return_ty, &value) {
    //                 (Some(ty), Some(expr)) => {
    //                     let expr_ty = self.get_type_of_expr(*expr)?;
    //                     if self.type_is_coercible(expr_ty, ty) {
    //                         Ok(())
    //                     } else {
    //                         todo!("Report error")
    //                     }
    //                 }
    //                 (None, None) => Ok(()),
    //                 _ => {
    //                     println!("Return: {:?}", return_ty);
    //                     println!("Got: {:?}", value);
    //                     todo!()
    //                 }
    //             }
    //         }
    //         NirStmtKind::Break => todo!(),
    //     }
    // }

    // fn visit_fundef(&mut self, fdef: &mut NirFunctionDef) -> Result<(), TcError> {
    //     let proto = self.visit_fundef_proto(fdef)?;
    //     let fun_id = self.ctx.interner.fun_interner.insert(proto);
    //     let proto = self.ctx.interner.fun_interner.get(fun_id).clone();

    //     let parent_id = self.current_scope;

    //     let parent_scope = self.ctx.interner.scope_interner.get_mut(parent_id);
    //     parent_scope
    //         .definitions
    //         .push((proto.name, Definition::Function(fun_id)));

    //     let scope = Scope {
    //         kind: ScopeKind::Function(fun_id),
    //         parent: Some(self.current_scope),
    //         children: Vec::new(),
    //         definitions: Vec::new(),
    //     };

    //     let scope_id = self.ctx.interner.scope_interner.insert(scope);

    //     let parent_scope = self.ctx.interner.scope_interner.get_mut(parent_id);
    //     parent_scope.children.push(scope_id);
    //     self.current_scope = scope_id;

    //     for (i, param) in proto.params.iter().enumerate() {
    //         self.declare_variable(Pattern::Symbol(param.name), VarExpr::Param(i), param.ty);
    //     }

    //     fdef.body
    //         .iter_mut()
    //         .map(|body| {
    //             for stmt in body {
    //                 self.visit_stmt(stmt)?
    //             }
    //             Ok(())
    //         })
    //         .collect::<Result<Vec<_>, _>>()?;

    //     self.current_scope = parent_id;

    //     Ok(())
    // }

    // fn visit_fundef_proto(&mut self, fdef: &mut NirFunctionDef) -> Result<TcFunProto, TcError> {
    //     let name = fdef.name;
    //     let return_ty = self.visit_type(&mut fdef.return_ty)?;
    //     let params = fdef
    //         .args
    //         .iter_mut()
    //         .map(|x| {
    //             self.visit_type(&mut x.ty)
    //                 .map(|ty| TcParam { name: x.name, ty })
    //         })
    //         .collect::<Result<Vec<_>, _>>()?;

    //     Ok(TcFunProto {
    //         name,
    //         params,
    //         return_ty,
    //         variadic: fdef.is_variadic,
    //     })
    // }

    // fn get_return_type_impl(&self, id: ScopeId) -> Option<TyId> {
    //     let scope = self.ctx.interner.scope_interner.get(id);
    //     match scope.kind {
    //         ScopeKind::Function(fun_id) => {
    //             let fun = self.ctx.interner.fun_interner.get(fun_id);
    //             Some(fun.return_ty)
    //         }
    //         _ => scope.parent.map(|x| self.get_return_type_impl(x)).flatten(),
    //     }
    // }

    // pub fn get_return_type(&self) -> Option<TyId> {
    //     self.get_return_type_impl(self.current_scope)
    // }

    // fn get_type_of_symb_in_pattern(
    //     &self,
    //     pattern: &Pattern,
    //     symb: Symbol,
    //     ty: TyId,
    // ) -> Option<TyId> {
    //     match pattern {
    //         Pattern::Symbol(symbol) if *symbol == symb => Some(ty),
    //         Pattern::Tuple(patterns) => {
    //             let t = self.ctx.interner.type_interner.get(ty);
    //             match &t {
    //                 TcTy::Tuple(ty_ids) => {
    //                     for (p, t) in patterns.iter().zip(ty_ids) {
    //                         if let Some(x) = self.get_type_of_symb_in_pattern(p, symb, *t) {
    //                             return Some(x);
    //                         }
    //                     }
    //                     None
    //                 }
    //                 _ => None,
    //             }
    //         }
    //         _ => None,
    //     }
    // }

    // fn get_type_expr(&mut self, ty: &NirType) -> Result<TypeExpr, TcError> {
    //     match &ty.kind {
    //         NirTypeKind::Ptr(nir_type) => {
    //             Ok(TypeExpr::Ptr(Box::new(self.get_type_expr(nir_type)?)))
    //         }
    //         NirTypeKind::Named { name, generic_args } if generic_args.len() > 0 => {
    //             let def = self
    //                 .get_last_scope()
    //                 .get_definition_for_symbol(*name, &self.ctx.interner.scope_interner);

    //             if def.is_none() {
    //                 return Err(TcError::NameNotFound(*name));
    //             }

    //             let def = def.unwrap();

    //             let args = generic_args
    //                 .iter()
    //                 .map(|x| self.get_type_expr(x))
    //                 .collect::<Result<Vec<_>, _>>()?;
    //             Ok(TypeExpr::Instantiation {
    //                 template: def,
    //                 args,
    //             })
    //         }

    //         NirTypeKind::Named { name, .. } => {
    //             let def = self
    //                 .get_last_scope()
    //                 .get_definition_for_symbol(*name, &self.ctx.interner.scope_interner);

    //             if def.is_none() {
    //                 return Err(TcError::NameNotFound(*name));
    //             }

    //             let def = def.unwrap();

    //             Ok(TypeExpr::Resolved(self.get_resolved_type(def)?))
    //         }

    //         NirTypeKind::Tuple(nir_types) => Ok(TypeExpr::Tuple(
    //             nir_types
    //                 .iter()
    //                 .map(|x| self.get_type_expr(x))
    //                 .collect::<Result<_, _>>()?,
    //         )),
    //     }
    // }

    // fn get_trait(&mut self, name: Symbol) -> Option<TraitId> {
    //     let s = self
    //         .get_last_scope()
    //         .get_definition_for_symbol(name, &self.ctx.interner.scope_interner);
    //     match s {
    //         Some(Definition::Trait(id)) => Some(id),
    //         _ => self.ctx.interner.trait_interner.get_with_name(name),
    //     }
    // }

    // fn visit_class(&mut self, cdef: &mut NirClassDef) -> Result<(), TcError> {
    //     let templates = {
    //         let mut templates = Vec::with_capacity(cdef.generic_args.len());
    //         for arg in &cdef.generic_args {
    //             let mut constraints = Vec::with_capacity(arg.constraints.len());
    //             for constraint in &arg.constraints {
    //                 let id = self.get_trait(constraint.name);
    //                 if id.is_none() {
    //                     return Err(TcError::NameNotFound(constraint.name));
    //                 }
    //                 constraints.push(id.unwrap());
    //             }
    //             templates.push(TemplateArgument {
    //                 name: arg.name,
    //                 constraints,
    //             });
    //         }
    //         templates
    //     };
    //     let c = Class {
    //         name: cdef.name,
    //         templates: templates.clone(),
    //         members: Vec::new(),
    //     };
    //     let id = self.ctx.interner.class_interner.insert(c);
    //     let parent_scope = self.current_scope;

    //     let new_scope = Scope {
    //         kind: ScopeKind::Class(id),
    //         parent: Some(self.current_scope),
    //         children: Vec::new(),
    //         definitions: Vec::new(),
    //     };
    //     let new_scope_id = self.ctx.interner.scope_interner.insert(new_scope);

    //     let last_scope = self.get_last_scope_mut();
    //     last_scope.children.push(new_scope_id);
    //     last_scope
    //         .definitions
    //         .push((cdef.name, Definition::Class(id)));
    //     self.current_scope = new_scope_id;

    //     let current_scope = self.get_last_scope_mut();

    //     for (i, TemplateArgument { name, .. }) in templates.iter().enumerate() {
    //         current_scope
    //             .definitions
    //             .push((*name, Definition::Type(TypeKind::Templated(i))))
    //     }

    //     let mut members = Vec::with_capacity(cdef.members.len());

    //     for member in &cdef.members {
    //         members.push(ClassMember {
    //             name: member.name,
    //             ty: self.get_type_expr(&member.ty)?,
    //         });
    //     }

    //     let cmut = self.ctx.interner.class_interner.get_mut(id);
    //     cmut.members = members;

    //     println!("members: {:?}", cmut.members);

    //     println!(
    //         "Todo: Do the work here ! {}:{}:{}",
    //         file!(),
    //         line!(),
    //         column!()
    //     );

    //     self.current_scope = parent_scope;
    //     Ok(())
    // }

    // fn resolve_type_expr(&mut self, expr: &TypeExpr) -> Result<TyId, TcError> {
    //     match expr {
    //         TypeExpr::Resolved(ty_id) => Ok(*ty_id),
    //         TypeExpr::Template(_) => Err(TcError::NotAResolvedType(expr.clone())),
    //         TypeExpr::Instantiation { template, args } => self.instantiate(*template, args),
    //         TypeExpr::Ptr(type_expr) => {
    //             let ty = self.resolve_type_expr(&type_expr)?;
    //             Ok(self.ctx.interner.type_interner.insert(TcTy::Ptr(ty)))
    //         }
    //         TypeExpr::Tuple(type_exprs) => {
    //             let ty = TcTy::Tuple(
    //                 type_exprs
    //                     .iter()
    //                     .map(|x| self.resolve_type_expr(x))
    //                     .collect::<Result<_, _>>()?,
    //             );

    //             Ok(self.ctx.interner.type_interner.insert(ty))
    //         }
    //     }
    // }

    // fn get_resolved_type(&mut self, def: Definition) -> Result<TyId, TcError> {
    //     match def {
    //         Definition::Class(id) => {
    //             let mems = self.ctx.interner.class_interner.get(id).members.clone();
    //             let ty = TcTy::Struct {
    //                 fields: mems
    //                     .iter()
    //                     .map(|x| {
    //                         self.resolve_type_expr(&x.ty).map(|y| StructField {
    //                             name: x.name,
    //                             ty: y,
    //                         })
    //                     })
    //                     .collect::<Result<_, _>>()?,
    //             };
    //             Ok(self.ctx.interner.type_interner.insert(ty))
    //         }
    //         Definition::Type(type_kind) => match type_kind {
    //             TypeKind::Resolved(ty_id) => Ok(ty_id),
    //             TypeKind::Templated(x) => Err(TcError::NotAResolvedType(TypeExpr::Template(x))),
    //         },
    //         _ => Err(TcError::NotATypeDef(def)),
    //     }
    // }

    // fn instantiate(&mut self, _template: Definition, _args: &[TypeExpr]) -> Result<TyId, TcError> {
    //     todo!()
    // }
}
