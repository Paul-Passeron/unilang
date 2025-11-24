use crate::{
    common::{
        context::GlobalContext,
        global_interner::{DefId, ExprId, FunId, ScopeId, Symbol, TyId, TypeExprId, UnresolvedId},
        source_location::Span,
    },
    nir::nir::{NirPath, NirType, NirTypeKind},
    ty::{
        scope::{Definition, Scope, ScopeKind, TypeExpr, Unresolved, UnresolvedKind},
        tir::TirInstr,
    },
};

pub mod concrete_type;
pub mod displays;
pub mod expr_translator;
pub mod scope;
pub mod specialized_class;
pub mod surface_resolution;
pub mod tir;
pub mod tir_pass;
pub mod type_checker;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, strum::EnumIter)]
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
    pub current_scope: ScopeId,
    pub ctx: &'ctx mut GlobalContext,
    pub backpatching: Vec<(DefId, UnresolvedId)>,
    pub defer_stack: Vec<Vec<Vec<TirInstr>>>,
}

#[derive(Clone, Debug)]
pub enum TcError {
    Aggregate(Vec<TcError>),
    BadReturnType(TyId, TyId),
    Text(String),
    NotAModule(ExprId),
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

impl<'ctx> TyCtx<'ctx> {
    pub fn push_instr(&mut self, instr: TirInstr, defer: bool) {
        if defer {
            self.defer_stack
                .last_mut()
                .unwrap()
                .last_mut()
                .unwrap()
                .push(instr);
        } else {
            let scope = self.get_last_scope_mut();
            match &mut scope.kind {
                ScopeKind::Else(tir_instrs)
                | ScopeKind::Then(tir_instrs)
                | ScopeKind::Block(tir_instrs)
                | ScopeKind::WhileLoop(_, tir_instrs)
                | ScopeKind::WhileCond(tir_instrs)
                | ScopeKind::Function(_, _, tir_instrs) => tir_instrs.push(instr),
                _ => unreachable!("{:?}", scope.kind),
            }
        }
    }

    pub fn clear_deferred(&mut self) {
        self.defer_stack.clear();
        self.defer_stack.push(vec![Vec::new()]);
    }

    pub fn flush_deferred(&mut self) {
        self.push_all_deferred();
        self.clear_deferred();
    }

    pub fn enter_scope(&mut self, kind: ScopeKind) -> ScopeId {
        let mut should_register = false;
        let id = if let Some(id) = self.ctx.interner.contains_scopekind(&kind) {
            id
        } else {
            should_register = true;
            let parent = self.current_scope;
            let scope = Scope {
                kind,
                parent: Some(parent),
                children: Vec::new(),
                definitions: Vec::new(),
            };

            self.ctx.interner.insert_scope(scope)
        };
        if should_register {
            let parent = self.current_scope;

            // register in parent
            let parent_mut = self.ctx.interner.get_scope_mut(parent);
            parent_mut.children.push(id);
            self.current_scope = id;
            self.defer_stack.push(vec![Vec::new()]);
        }
        self.current_scope = id;
        self.defer_stack.push(vec![Vec::new()]);
        id
    }

    pub fn push_all_deferred(&mut self) {
        let mut stack = self.defer_stack.clone();
        while let Some(mut last) = stack.pop() {
            while let Some(instr_block) = last.pop() {
                for instr in instr_block {
                    self.push_instr(instr, false);
                }
            }
        }
    }

    pub fn exit_scope(&mut self) {
        if let Some(parent) = self.ctx.interner.get_scope(self.current_scope).parent {
            let mut last = self.defer_stack.pop().unwrap();
            while let Some(instr_block) = last.pop() {
                for instr in instr_block {
                    self.push_instr(instr, false);
                }
            }
            self.current_scope = parent;
        }
    }

    pub fn with_scope<F, R>(&mut self, kind: ScopeKind, f: F) -> R
    where
        F: FnOnce(&mut TyCtx<'ctx>) -> R,
    {
        let _scope = self.enter_scope(kind);
        let res = f(self);
        self.exit_scope();
        res
    }

    pub fn with_scope_id<F, R>(&mut self, id: ScopeId, f: F) -> R
    where
        F: FnOnce(&mut TyCtx<'ctx>) -> R,
    {
        let before = self.current_scope;
        self.current_scope = id;
        let res = f(self);
        self.current_scope = before;
        res
    }

    pub fn get_symbol_def_in_scope(&self, id: ScopeId, symb: Symbol) -> Option<DefId> {
        self.get_scope(id)
            .get_definition_for_symbol(symb, self.ctx.interner.scope_interner())
    }

    pub fn get_symbol_def(&self, symb: Symbol) -> Option<DefId> {
        self.get_last_scope()
            .get_definition_for_symbol(symb, &self.ctx.interner.scope_interner())
    }

    pub fn push_def(&mut self, symb: Symbol, def: DefId) {
        self.get_last_scope_mut().definitions.push((symb, def));
    }

    pub fn pop_def(&mut self) {
        let _ = self.get_last_scope_mut().definitions.pop();
    }

    pub fn get_scope(&self, id: ScopeId) -> &Scope {
        self.ctx.interner.get_scope(id)
    }

    fn declare_primitive_types(&mut self) {
        let create_alias = |this: &mut Self, ty: PrimitiveTy, name: &str| {
            let symb = this.ctx.interner.insert_symbol(&name.to_string());
            let te = this.ctx.interner.insert_type_expr(TypeExpr::Primitive(ty));
            let def = this.ctx.interner.insert_def(Definition::Type(te));
            this.push_def(symb, def);
        };

        let mut alias = |prim| create_alias(self, prim, prim.get_name());

        alias(PrimitiveTy::Void);
        alias(PrimitiveTy::I8);
        alias(PrimitiveTy::I16);
        alias(PrimitiveTy::I32);
        alias(PrimitiveTy::I64);
        alias(PrimitiveTy::U8);
        alias(PrimitiveTy::U16);
        alias(PrimitiveTy::U32);
        alias(PrimitiveTy::U64);
        alias(PrimitiveTy::Bool);

        create_alias(self, PrimitiveTy::I32, "int");
        create_alias(self, PrimitiveTy::U32, "usize");
        create_alias(self, PrimitiveTy::U8, "char");
    }

    pub fn add_builtins(&mut self) {
        self.declare_primitive_types();
    }

    pub fn new(ctx: &'ctx mut GlobalContext) -> Self {
        let first_scope = Scope {
            kind: ScopeKind::Global,
            parent: None,
            children: Vec::new(),
            definitions: Vec::new(),
        };

        let scope_id = ctx.interner.insert_scope(first_scope);

        let mut res = Self {
            current_scope: scope_id,
            ctx,
            backpatching: Vec::new(),
            defer_stack: vec![],
        };
        res.add_builtins();
        res
    }

    pub fn get_last_scope_mut(&mut self) -> &mut Scope {
        self.ctx.interner.get_scope_mut(self.current_scope)
    }

    pub fn get_last_scope(&self) -> &Scope {
        self.ctx.interner.get_scope(self.current_scope)
    }

    fn visit_type_as_def(&mut self, input: &NirType) -> Result<DefId, TcError> {
        match &input.kind {
            NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
                let def = self.resolve_path(name);
                Ok(def)
            }
            NirTypeKind::Named { name, generic_args } => {
                let args = generic_args
                    .iter()
                    .map(|x| self.visit_type(x))
                    .collect::<Result<_, _>>()?;
                let from = self.resolve_path(name);
                let te = self.ctx.interner.insert_type_expr(TypeExpr::Instantiation {
                    template: (from, name.clone()),
                    args,
                });
                let def = self.ctx.interner.insert_def(Definition::Type(te));
                Ok(def)
            }
            _ => unreachable!(),
        }
    }

    pub fn visit_type(&mut self, input: &NirType) -> Result<TypeExprId, TcError> {
        match &input.kind {
            NirTypeKind::Ptr(nir_type) => self
                .visit_type(nir_type)
                .map(|x| self.ctx.interner.insert_type_expr(TypeExpr::Ptr(x))),
            NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
                let def = self.resolve_path(name);
                match self.ctx.interner.get_def(def) {
                    Definition::Class(_) => {
                        Ok(self.ctx.interner.insert_type_expr(TypeExpr::Instantiation {
                            template: (def, name.clone()),
                            args: vec![],
                        }))
                    }
                    Definition::Type(x) => Ok(*x),
                    Definition::Unresolved(_) => {
                        let ty = TypeExpr::Instantiation {
                            template: (def, name.clone()),
                            args: vec![],
                        };
                        Ok(self.ctx.interner.insert_type_expr(ty))
                    }
                    _ => todo!("{def:?}"),
                }
            }
            NirTypeKind::Named { name, generic_args } => {
                let args = generic_args
                    .iter()
                    .map(|x| self.visit_type(x))
                    .collect::<Result<_, _>>()?;
                let def = self.resolve_path(name);

                Ok(self.ctx.interner.insert_type_expr(TypeExpr::Instantiation {
                    template: (def, name.clone()),
                    args,
                }))
            }
            NirTypeKind::Tuple(nir_types) => {
                let tys = nir_types
                    .iter()
                    .map(|x| self.visit_type(x))
                    .collect::<Result<_, _>>()?;
                Ok(self.ctx.interner.insert_type_expr(TypeExpr::Tuple(tys)))
            }
        }
    }

    fn resolve_path(&mut self, name: &NirPath) -> DefId {
        let def = {
            name.path.iter().fold(None, |acc, (x, span)| match acc {
                Some(def) => Some(self.resolve_access(def, *x, *span).unwrap()),
                None => self.get_symbol_def(*x).or_else(|| {
                    let insert = self.ctx.interner.insert_unresolved(Unresolved {
                        scope: self.current_scope,
                        kind: UnresolvedKind::Symb(*x, *span),
                    });
                    let def = self.ctx.interner.insert_def(Definition::Unresolved(insert));
                    self.backpatching.insert(0, (def, insert));
                    Some(def)
                }),
            })
        }
        .unwrap();
        def
    }

    fn resolve_access(
        &mut self,
        from_def: DefId,
        index: Symbol,
        span: Span,
    ) -> Result<DefId, TcError> {
        match self.ctx.interner.get_def(from_def) {
            Definition::Class(_) => todo!(),
            Definition::Function(_) => todo!(),
            Definition::Module(module_id) => {
                let module = self.ctx.interner.get_module(*module_id);
                let def_opt = self.get_symbol_def_in_scope(module.scope, index);
                if def_opt.is_some() {
                    return Ok(def_opt.unwrap());
                }

                let id = self.ctx.interner.insert_unresolved(Unresolved {
                    scope: module.scope,
                    kind: UnresolvedKind::Symb(index, span),
                });

                let def = self.ctx.interner.insert_def(Definition::Unresolved(id));
                self.backpatching.insert(0, (def, id));
                Ok(def)
            }
            Definition::Var(_) => todo!(),
            Definition::Trait(_) => todo!(),
            Definition::Type(_) => todo!(),
            Definition::Unresolved(u_id) => {
                let un = Unresolved {
                    scope: self.current_scope,
                    kind: UnresolvedKind::From(*u_id, index),
                };
                let id = self.ctx.interner.insert_unresolved(un);
                let def = self.ctx.interner.insert_def(Definition::Unresolved(id));
                self.backpatching.insert(0, (def, id));
                Ok(def)
            }
        }
    }

    pub fn get_current_fun_scope(&mut self) -> Option<ScopeId> {
        match self.get_last_scope().kind.clone() {
            ScopeKind::Function(_, _, _) => Some(self.current_scope),
            ScopeKind::Else(_)
            | ScopeKind::Then(_)
            | ScopeKind::If { .. }
            | ScopeKind::Block(_) => {
                let parent = self.get_last_scope().parent.unwrap();
                self.with_scope_id(parent, |ctx| ctx.get_current_fun_scope())
            }
            _ => None,
        }
    }

    pub fn get_current_fun(&mut self) -> Option<FunId> {
        match self.get_last_scope().kind.clone() {
            ScopeKind::Function(fun_id, _, _) => Some(fun_id),
            ScopeKind::Else(_)
            | ScopeKind::Then(_)
            | ScopeKind::If { .. }
            | ScopeKind::Block(_) => {
                let parent = self.get_last_scope().parent.unwrap();
                self.with_scope_id(parent, |ctx| ctx.get_current_fun())
            }
            _ => None,
        }
    }

    pub fn get_return_ty(&mut self) -> Option<TypeExprId> {
        self.get_current_fun()
            .map(|id| self.ctx.interner.get_fun(id).return_ty)
    }
}
