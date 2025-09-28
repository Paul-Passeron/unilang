use std::{
    collections::{HashMap, HashSet},
    hash::RandomState,
};

use strum::{EnumIter, IntoEnumIterator};

use crate::{
    nir::{
        context::GlobalContext,
        interner::{
            ConstructibleId, ExprId, Interner, ItemId, ScopeId, Symbol, TyId, TypeInterner,
            VariableId,
        },
        nir::{
            NirExprKind, NirFunctionDef, NirItem, NirLiteral, NirPattern, NirPatternKind,
            NirProgram, NirStmt, NirStmtKind, NirType, NirTypeKind,
        },
    },
    ty::scope::{Definition, Pattern, Scope, ScopeKind, VarDecl},
};

pub mod scope;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldTy {
    Generic(u32),
    Ty(TyId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructField {
    pub name: Symbol,
    pub ty: TyId,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TcTy {
    Ptr(TyId),
    Primitive(PrimitiveTy),
    Struct { fields: Vec<StructField> },
    Tuple(Vec<TyId>),
    Unresolved(NirType),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct DefId(pub u32);
impl ConstructibleId for DefId {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

#[derive(Debug)]
pub struct TcParam {
    pub name: Symbol,
    pub ty: TyId,
}

#[derive(Debug)]
pub struct TcFunProto {
    pub name: Symbol,
    pub params: Vec<TcParam>,
    pub return_ty: TyId,
}

#[derive(Debug)]
pub struct TyCtx<'ctx> {
    pub aliases: HashMap<Symbol, TyId>,
    pub types: HashMap<TyId, NirType>,
    pub methods: HashMap<TyId, Vec<TcFunProto>>,
    pub current_scope: ScopeId,
    pub expr_types: HashMap<ExprId, TyId>,
    pub ctx: &'ctx mut GlobalContext,
}

#[derive(Debug)]
pub enum TcError {
    AlreadyDefinedMethod { ty: TyId, name: Symbol },
    Todo,
    NameNotFound(Symbol),
    Aggregate(Vec<(ItemId, TcError)>),
    NotAFunction(Symbol),
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
        for prim in PrimitiveTy::iter() {
            let ty = self.declare_type(TcTy::Primitive(prim));
            self.create_alias(ty, prim.get_name());
        }

        let int_ty = self
            .ctx
            .interner
            .type_interner
            .contains(&TcTy::Primitive(PrimitiveTy::I32))
            .unwrap();
        self.create_alias(int_ty, "int");

        let usize_ty = self
            .ctx
            .interner
            .type_interner
            .contains(&TcTy::Primitive(PrimitiveTy::U32))
            .unwrap();
        self.create_alias(usize_ty, "usize");

        let char_ty = self
            .ctx
            .interner
            .type_interner
            .contains(&TcTy::Primitive(PrimitiveTy::U8))
            .unwrap();
        self.create_alias(char_ty, "char");
    }

    fn populate_integer_ty(&mut self, prim: PrimitiveTy) {
        let ty = self
            .ctx
            .interner
            .type_interner
            .contains(&TcTy::Primitive(prim))
            .unwrap();

        let builtin_methods = self.get_methods_for_builtin(ty);

        let int_methods = self.get_methods_for_integer(ty);

        let methods = builtin_methods.into_iter().chain(int_methods.into_iter());

        for m in methods {
            if let Err(_) = self.add_method(ty, m) {
                panic!("Could not add builtin method in builtin type, this is a compiler bug.");
            }
        }
    }

    fn populate_void(&mut self) {
        let ty = self
            .ctx
            .interner
            .type_interner
            .contains(&TcTy::Primitive(PrimitiveTy::Void))
            .unwrap();

        let methods = self.get_methods_for_builtin(ty);

        for m in methods {
            if let Err(_) = self.add_method(ty, m) {
                panic!("Could not add builtin method in builtin type, this is a compiler bug.");
            }
        }
    }

    pub fn add_method(&mut self, ty: TyId, method: TcFunProto) -> Result<(), TcError> {
        let methods = self.methods.get_mut(&ty).unwrap();
        for m in &*methods {
            if m.name == method.name {
                return Err(TcError::AlreadyDefinedMethod {
                    ty,
                    name: method.name,
                });
            }
        }
        methods.push(method);
        Ok(())
    }

    pub fn get_simple_named(&self, name: &str, ctx: &GlobalContext) -> Option<TyId> {
        let name = ctx.interner.get_symbol_for(&name.to_string())?;
        self.aliases.get(&name).copied()
    }

    pub fn create_alias(&mut self, ty: TyId, alias: &str) {
        let s = self.symb(alias);
        self.aliases.insert(s, ty);
    }

    pub fn add_builtins(&mut self) {
        self.declare_primitive_types();
        for prim in PrimitiveTy::INTEGERS {
            self.populate_integer_ty(*prim);
        }
        self.populate_void();
    }

    fn symb(&mut self, name: &str) -> Symbol {
        self.ctx.interner.insert_symbol(&name.to_string())
    }

    fn get_symb(&self, s: &str) -> Symbol {
        self.ctx.interner.get_symbol_for(&s.to_string()).unwrap()
    }

    fn get_methods_for_builtin(&mut self, _ty: TyId) -> Vec<TcFunProto> {
        let size_fun_name = self.symb("__builtin_size");
        let size_fun = TcFunProto {
            name: size_fun_name,
            params: vec![],
            return_ty: self
                .ctx
                .interner
                .type_interner
                .contains(&TcTy::Primitive(PrimitiveTy::U32))
                .unwrap(),
        };
        vec![size_fun]
    }

    fn get_methods_for_integer(&mut self, _ty: TyId) -> Vec<TcFunProto> {
        vec![]
    }

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
            aliases: HashMap::new(),
            expr_types: HashMap::new(),
            current_scope: scope_id,
            ctx,
        };

        res.add_builtins();

        let first_scope = res.ctx.interner.scope_interner.get_mut(scope_id);
        for (symb, ty) in &res.aliases {
            first_scope
                .definitions
                .push((*symb, Definition::Builtin(*ty)));
        }
        res
    }

    pub fn visit_program(&mut self, program: &NirProgram) -> Result<(), TcError> {
        let items = program
            .0
            .iter()
            .map(|id| (*id, self.ctx.interner.get_item(*id).clone()))
            .collect::<Vec<_>>();
        self.visit_item_group(items)
    }

    pub fn visit_item_group(&mut self, items: Vec<(ItemId, NirItem)>) -> Result<(), TcError> {
        let mut temp_interner: HashMap<ItemId, NirItem, RandomState> = HashMap::from_iter(items);

        let mut working_stack: Vec<_> = temp_interner.keys().copied().collect();
        let mut errors = vec![];
        while working_stack.len() > 0 {
            errors.clear();
            let mut new_working_stack = vec![];
            for id in &working_stack {
                let item = temp_interner.get_mut(id).unwrap();
                let iteration: Result<(), TcError> = match item {
                    NirItem::Function(fdef) => self.visit_fundef(fdef, *id),
                    NirItem::Module(_nir_module_def) => todo!("module"),
                    NirItem::Class(_nir_class_def) => todo!("class"),
                    NirItem::Trait(_nir_trait_def) => todo!("trait"),
                    NirItem::Impl(_nir_impl_block) => todo!("impl"),
                    NirItem::Method(_nir_method) => unreachable!(),
                };
                if iteration.is_err() {
                    new_working_stack.push(*id);
                    errors.push((*id, iteration.unwrap_err()));
                }
            }

            let current_set: HashSet<ItemId, RandomState> = HashSet::from_iter(working_stack);
            let new_set: HashSet<ItemId, RandomState> =
                HashSet::from_iter(new_working_stack.iter().copied());
            working_stack = new_working_stack;
            if current_set == new_set {
                break; // No progress made, we must stop
            }
        }
        if !working_stack.is_empty() {
            Err(TcError::Aggregate(errors))
        } else {
            Ok(())
        }
    }

    fn get_type_string(&self, ty: TyId) -> String {
        let t = self.ctx.interner.type_interner.get(ty);
        match t {
            TcTy::Ptr(ty_id) => self.get_type_string(*ty_id) + "*",
            TcTy::Primitive(primitive_ty) => primitive_ty.get_name().to_string(),
            TcTy::Struct { fields } => {
                let mut res = "struct {\n".to_string();
                for f in fields {
                    res += "\t";
                    res += self.ctx.interner.get_symbol(f.name);
                    res += ": ";
                    res += &self.get_type_string(f.ty);
                    res += "\n";
                }
                res += "}";
                res
            }
            TcTy::Tuple(ty_ids) => {
                "(".to_string()
                    + &ty_ids
                        .iter()
                        .map(|x| self.get_type_string(*x))
                        .collect::<Vec<_>>()
                        .join(", ")
                    + ")"
            }
            TcTy::Unresolved(_) => todo!(),
        }
    }

    pub fn print_error(&mut self, error: &TcError) {
        match &error {
            TcError::AlreadyDefinedMethod { ty, name } => eprintln!(
                "Method {} is already defined for type {}!",
                self.ctx.interner.symbol_interner.get(*name),
                self.get_type_string(*ty),
            ),
            TcError::Todo => todo!("Todo error"),
            TcError::NameNotFound(symbol) => {
                eprintln!(
                    "Symbol {} is not defined in the current scope.",
                    self.ctx.interner.symbol_interner.get(*symbol),
                )
            }
            TcError::NotAFunction(symb) => {
                eprintln!(
                    "Symbol {} cannot be called.",
                    self.ctx.interner.symbol_interner.get(*symb),
                )
            }
            TcError::Aggregate(_) => todo!(),
        }
    }

    fn visit_type(&mut self, ty: &mut NirType) -> Result<TyId, TcError> {
        let res = match &mut ty.kind {
            NirTypeKind::Resolved(ty_id) => Ok(*ty_id),
            NirTypeKind::Ptr(t) => {
                let inner = self.visit_type(t.as_mut())?;
                Ok(self.ctx.interner.type_interner.insert(TcTy::Ptr(inner)))
            }
            NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
                assert!(name.len() == 1, "todo: path names");
                let name = name[0];
                match self.aliases.get(&name) {
                    Some(x) => Ok(*x),
                    None => Err(TcError::NameNotFound(name)),
                }
            }
            NirTypeKind::Named { .. } => todo!("Handle generic types"),
            NirTypeKind::Tuple(_nir_types) => todo!(),
        }?;
        ty.kind = NirTypeKind::Resolved(res);
        Ok(res)
    }

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

    fn get_type_of_binop(&mut self, left: ExprId, right: ExprId) -> Result<TyId, TcError> {
        let tl = self.get_type_of_expr(left)?;
        let tr = self.get_type_of_expr(right)?;
        if self.is_type_primitive(tl) && self.is_type_primitive(tr) {
            if self.get_size(tl) > self.get_size(tr) {
                Ok(tl)
            } else {
                Ok(tr)
            }
        } else {
            if self.is_type_primitive(tl) && self.is_type_ptr(tr) {
                Ok(tr)
            } else if self.is_type_primitive(tr) && self.is_type_ptr(tl) {
                Ok(tl)
            } else {
                todo!()
            }
        }
    }

    fn get_type_of_expr(&mut self, expr: ExprId) -> Result<TyId, TcError> {
        if self.expr_types.contains_key(&expr) {
            return Ok(*&self.expr_types[&expr]);
        }

        let ast = self.ctx.interner.expr_interner.get(expr);

        let res = match &ast.kind {
            NirExprKind::Literal(nir_literal) => match nir_literal {
                NirLiteral::IntLiteral(_num) => Ok(self.aliases[&self.get_symb("i64")]),
                NirLiteral::FloatLiteral(_my_float) => todo!(),
                NirLiteral::StringLiteral(_string_literal) => todo!(),
                NirLiteral::CharLiteral(_) => todo!(),
            },
            NirExprKind::BinOp(op) => {
                let l = op.left;
                let r = op.right;
                self.get_type_of_binop(l, r)
            }
            NirExprKind::UnOp { .. } => todo!(),
            NirExprKind::Call(call) => match call.called.receiver {
                Some(_) => todo!(),
                None => {
                    let scope = self.get_last_scope();
                    let def = scope.get_definition_for_symbol(
                        call.called.called,
                        &self.ctx.interner.scope_interner,
                    );
                    if def.is_none() {
                        return Err(TcError::NameNotFound(call.called.called));
                    }
                    let f = match def.unwrap() {
                        Definition::Function(f) => f,
                        _ => return Err(TcError::NotAFunction(call.called.called)),
                    };
                    let proto = self.ctx.interner.fun_interner.get(f);
                    let return_ty = proto.return_ty;

                    println!("Todo: check args");

                    Ok(return_ty)
                }
            },
            NirExprKind::Subscript { .. } => todo!(),
            NirExprKind::Access { .. } => todo!(),
            NirExprKind::Named(_symbol) => todo!(),
            NirExprKind::PostIncr(_expr_id) => todo!(),
            NirExprKind::PreIncr(_expr_id) => todo!(),
            NirExprKind::PostDecr(_expr_id) => todo!(),
            NirExprKind::PreDecr(_expr_id) => todo!(),
            NirExprKind::AddrOf(_expr_id) => todo!(),
            NirExprKind::Deref(_expr_id) => todo!(),
            NirExprKind::SizeOf(_nir_type) => todo!(),
            NirExprKind::StringOf(_nir_type) => todo!(),
            NirExprKind::Minus(_expr_id) => todo!(),
            NirExprKind::Not(_expr_id) => todo!(),
            NirExprKind::New { .. } => todo!(),
            NirExprKind::As { .. } => todo!(),
            NirExprKind::Tuple(_expr_ids) => todo!(),
            NirExprKind::Range { .. } => todo!(),
        };

        match res {
            Ok(x) => {
                self.expr_types.insert(expr, x);
            }
            _ => (),
        };
        res
    }

    fn type_is_coercible(&mut self, source: TyId, dest: TyId) -> bool {
        if source == dest {
            true
        } else {
            let source = self.ctx.interner.type_interner.get(source);
            let dest = self.ctx.interner.type_interner.get(dest);
            match (source, dest) {
                (TcTy::Primitive(_), TcTy::Primitive(_)) => true,
                _ => todo!(),
            }
        }
    }

    fn visit_pattern(&self, pat: &NirPattern) -> Pattern {
        match &pat.kind {
            NirPatternKind::Wildcard => Pattern::Wildcard,
            NirPatternKind::Symbol(symbol) => Pattern::Symbol(*symbol),
            NirPatternKind::Tuple(nir_patterns) => {
                Pattern::Tuple(nir_patterns.iter().map(|x| self.visit_pattern(x)).collect())
            }
        }
    }

    fn get_last_scope_mut(&mut self) -> &mut Scope {
        self.ctx.interner.scope_interner.get_mut(self.current_scope)
    }

    fn get_last_scope(&self) -> &Scope {
        self.ctx.interner.scope_interner.get(self.current_scope)
    }

    fn declare_variable(&mut self, pattern: Pattern, expr: Option<ExprId>, ty: TyId) {
        let var_decl = VarDecl {
            name: pattern.clone(),
            ty,
            expr,
        };

        let id = self.ctx.interner.variable_interner.insert(var_decl);

        self.declare_variable_impl(&pattern, id);
    }

    fn declare_variable_impl(&mut self, pattern: &Pattern, id: VariableId) {
        match pattern {
            Pattern::Wildcard => (),
            Pattern::Symbol(symbol) => self
                .get_last_scope_mut()
                .definitions
                .push((*symbol, Definition::Variable(id))),
            Pattern::Tuple(patterns) => patterns.iter().for_each(|x| {
                self.declare_variable_impl(x, id);
            }),
        }
    }

    fn inner<T, V>(x: Option<Result<T, V>>) -> Result<Option<T>, V> {
        match x {
            Some(Ok(x)) => Ok(Some(x)),
            None => Ok(None),
            Some(Err(x)) => Err(x),
        }
    }

    fn visit_stmt(&mut self, stmt: &mut NirStmt) -> Result<(), TcError> {
        match &mut stmt.kind {
            NirStmtKind::Expr(expr) => {
                self.get_type_of_expr(*expr)?;
                Ok(())
            }
            NirStmtKind::Block(_nir_stmts) => todo!(),
            NirStmtKind::If { .. } => todo!(),
            NirStmtKind::While { .. } => todo!(),
            NirStmtKind::For { .. } => todo!(),
            NirStmtKind::Let(decl) => {
                let pattern = self.visit_pattern(&decl.pattern);
                let expected_type = Self::inner(decl.ty.as_mut().map(|ty| self.visit_type(ty)))?;
                let actual_type = Self::inner(decl.value.map(|x| self.get_type_of_expr(x)))?;
                let ty = match (expected_type, actual_type) {
                    (Some(x), None) => x,
                    (None, Some(x)) => x,
                    (Some(x), Some(y)) => {
                        if self.type_is_coercible(y, x) {
                            x
                        } else {
                            todo!("report error of var decl mismatched types")
                        }
                    }
                    (None, None) => panic!("Type inference is not supported"),
                };
                self.declare_variable(pattern, decl.value, ty);
                Ok(())
            }
            NirStmtKind::Assign { .. } => todo!(),
            NirStmtKind::Return { value } => {
                let return_ty = self.get_return_type();
                match (return_ty, &value) {
                    (Some(ty), Some(expr)) => {
                        let expr_ty = self.get_type_of_expr(*expr)?;
                        if self.type_is_coercible(expr_ty, ty) {
                            Ok(())
                        } else {
                            todo!("Report error")
                        }
                    }
                    (None, None) => Ok(()),
                    _ => {
                        println!("Return: {:?}", return_ty);
                        println!("Got: {:?}", value);
                        todo!()
                    }
                }
            }
            NirStmtKind::Break => todo!(),
        }
    }

    fn visit_fundef(&mut self, fdef: &mut NirFunctionDef, _id: ItemId) -> Result<(), TcError> {
        let proto = self.visit_fundef_proto(fdef)?;
        let fun_id = self.ctx.interner.fun_interner.insert(proto);
        let proto = self.ctx.interner.fun_interner.get(fun_id);

        let parent_id = self.current_scope;

        let parent_scope = self.ctx.interner.scope_interner.get_mut(parent_id);
        parent_scope
            .definitions
            .push((proto.name, Definition::Function(fun_id)));

        let scope = Scope {
            kind: ScopeKind::Function(fun_id),
            parent: Some(self.current_scope),
            children: Vec::new(),
            definitions: Vec::new(),
        };

        let scope_id = self.ctx.interner.scope_interner.insert(scope);

        let parent_scope = self.ctx.interner.scope_interner.get_mut(parent_id);
        parent_scope.children.push(scope_id);
        self.current_scope = scope_id;

        fdef.body
            .iter_mut()
            .map(|body| {
                for stmt in body {
                    self.visit_stmt(stmt)?
                }
                Ok(())
            })
            .collect::<Result<Vec<_>, _>>()?;

        self.current_scope = parent_id;

        Ok(())
    }

    fn visit_fundef_proto(&mut self, fdef: &mut NirFunctionDef) -> Result<TcFunProto, TcError> {
        let name = fdef.name;
        let return_ty = self.visit_type(&mut fdef.return_ty)?;
        let params = fdef
            .args
            .iter_mut()
            .map(|x| {
                self.visit_type(&mut x.ty)
                    .map(|ty| TcParam { name: x.name, ty })
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(TcFunProto {
            name,
            params,
            return_ty,
        })
    }

    fn get_return_type_impl(&self, id: ScopeId) -> Option<TyId> {
        let scope = self.ctx.interner.scope_interner.get(id);
        match scope.kind {
            ScopeKind::Function(fun_id) => {
                let fun = self.ctx.interner.fun_interner.get(fun_id);
                Some(fun.return_ty)
            }
            _ => scope.parent.map(|x| self.get_return_type_impl(x)).flatten(),
        }
    }

    pub fn get_return_type(&self) -> Option<TyId> {
        self.get_return_type_impl(self.current_scope)
    }
}
