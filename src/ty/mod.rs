use strum::{EnumIter, IntoEnumIterator};

use crate::{
    common::source_location::Span,
    nir::{
        context::GlobalContext,
        interner::{DefId, ScopeId, Symbol, TypeExprId, UnresolvedId},
        nir::{NirPath, NirType, NirTypeKind},
    },
    ty::scope::{Definition, Scope, ScopeKind, TypeExpr, Unresolved, UnresolvedKind},
};

pub mod pass;
pub mod scope;
pub mod surface_resolution;
pub mod tir;

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
}

#[derive(Debug)]
pub enum TcError {
    Todo,
    NameNotFound(Symbol),
    Aggregate(Vec<TcError>),
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

impl<'ctx> TyCtx<'ctx> {
    pub fn enter_scope(&mut self, kind: ScopeKind) -> ScopeId {
        let parent = self.current_scope;
        let scope = Scope {
            kind,
            parent: Some(parent),
            children: Vec::new(),
            definitions: Vec::new(),
        };
        let id = self.ctx.interner.insert_scope(scope);
        // register in parent
        let parent_mut = self.ctx.interner.get_scope_mut(parent);
        parent_mut.children.push(id);
        self.current_scope = id;
        println!("Entering scope {:?}", id);
        id
    }

    pub fn exit_scope(&mut self) {
        if let Some(parent) = self.ctx.interner.get_scope(self.current_scope).parent {
            println!(
                "Exiting scope {:?} to scope {:?}",
                self.current_scope, parent
            );
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

    pub fn get_scope(&self, id: ScopeId) -> &Scope {
        self.ctx.interner.get_scope(id)
    }

    fn declare_primitive_types(&mut self) {
        let create_alias = |this: &mut Self, ty: PrimitiveTy, name: &str| {
            let symb = this.ctx.interner.insert_symbol(&name.to_string());
            let te = this.ctx.interner.insert_type_expr(TypeExpr::Primitive(ty));
            let def = this.ctx.interner.insert_def(Definition::Type(te));
            this.get_last_scope_mut().definitions.push((symb, def));
        };

        for prim in PrimitiveTy::iter() {
            create_alias(self, prim, prim.get_name());
        }

        create_alias(self, PrimitiveTy::I32, "int");
        create_alias(self, PrimitiveTy::U32, "usize");
        create_alias(self, PrimitiveTy::U8, "char");
    }

    pub fn add_builtins(&mut self) {
        self.declare_primitive_types();
    }

    fn symb(&mut self, name: &str) -> Symbol {
        self.ctx.interner.insert_symbol(&name.to_string())
    }

    fn get_symb(&self, s: &str) -> Symbol {
        self.ctx.interner.get_symbol_for(&s.to_string())
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
        };
        res.add_builtins();
        res
    }

    fn get_type_string(&self, _ty: &TypeExpr) -> String {
        todo!()
    }

    pub fn print_error(&mut self, _error: &TcError) {
        todo!()
    }

    fn get_last_scope_mut(&mut self) -> &mut Scope {
        self.ctx.interner.get_scope_mut(self.current_scope)
    }

    fn get_last_scope(&self) -> &Scope {
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
                    template: from,
                    args,
                });
                let def = self.ctx.interner.insert_def(Definition::Type(te));
                Ok(def)
            }
            _ => unreachable!(),
        }
    }

    fn visit_type(&mut self, input: &NirType) -> Result<TypeExprId, TcError> {
        match &input.kind {
            NirTypeKind::Ptr(nir_type) => self
                .visit_type(nir_type)
                .map(|x| self.ctx.interner.insert_type_expr(TypeExpr::Ptr(x))),
            NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
                let def = self.resolve_path(name);
                match self.ctx.interner.get_def(def) {
                    Definition::Class(_) => {
                        Ok(self.ctx.interner.insert_type_expr(TypeExpr::Instantiation {
                            template: def,
                            args: vec![],
                        }))
                    }
                    Definition::Type(x) => Ok(*x),
                    Definition::Unresolved(_) => {
                        let ty = TypeExpr::Instantiation {
                            template: def,
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
                    template: def,
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
            Definition::Variable(_) => todo!(),
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
}
