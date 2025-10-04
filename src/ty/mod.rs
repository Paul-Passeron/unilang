use std::{collections::HashMap, rc::Rc};

use strum::{EnumIter, IntoEnumIterator};

use crate::{
    nir::{
        context::GlobalContext,
        interner::{ScopeId, Symbol, TyId, TypeExprId, TypeInterner},
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

    pub fn get_symbol_def_in_scope(&self, id: ScopeId, symb: Symbol) -> Option<Rc<Definition>> {
        self.get_scope(id)
            .get_definition_for_symbol(symb, self.ctx.interner.scope_interner())
    }

    pub fn get_symbol_def(&self, symb: Symbol) -> Option<Rc<Definition>> {
        self.get_last_scope()
            .get_definition_for_symbol(symb, &self.ctx.interner.scope_interner())
    }

    pub fn push_def(&mut self, symb: Symbol, def: Rc<Definition>) {
        self.get_last_scope_mut().definitions.push((symb, def));
    }

    pub fn get_scope(&self, id: ScopeId) -> &Scope {
        self.ctx.interner.get_scope(id)
    }

    fn declare_type(&mut self, val: TcTy) -> TyId {
        self.ctx.interner.insert_ty(val)
    }

    fn declare_primitive_types(&mut self) {
        let create_alias = |this: &mut Self, ty, name: &str| {
            let symb = this.ctx.interner.insert_symbol(&name.to_string());
            let res = (
                symb,
                Rc::new(Definition::Type(
                    this.ctx.interner.insert_type_expr(TypeExpr::Resolved(ty)),
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
            .contains_ty(&TcTy::Primitive(PrimitiveTy::I32))
            .unwrap();
        create_alias(self, int_ty, "int");

        let usize_ty = self
            .ctx
            .interner
            .contains_ty(&TcTy::Primitive(PrimitiveTy::U32))
            .unwrap();
        create_alias(self, usize_ty, "usize");

        let char_ty = self
            .ctx
            .interner
            .contains_ty(&TcTy::Primitive(PrimitiveTy::U8))
            .unwrap();
        create_alias(self, char_ty, "char");
    }

    // fn populate_integer_ty(&mut self, prim: PrimitiveTy) {
    //     let ty = self
    //         .ctx
    //         .interner
    //         .ty
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
    //         .ty
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
        self.ctx.interner.get_symbol_for(&s.to_string())
    }

    // fn get_methods_for_builtin(&mut self, _ty: TyId) -> Vec<TcFunProto> {
    //     let size_fun_name = self.symb("__builtin_size");
    //     let size_fun = TcFunProto {
    //         name: size_fun_name,
    //         params: vec![],
    //         return_ty: self
    //             .ctx
    //             .interner
    //             .ty
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

        let scope_id = ctx.interner.insert_scope(first_scope);

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
    //             Ok(self.ctx.interner.insert_ty(TcTy::Ptr(inner)))
    //         }
    //         NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
    //             let def = self
    //                 .get_last_scope()
    //                 .get_definition_for_symbol(*name, self.ctx.scope_interner());
    //             match def {
    //                 Some(Definition::Type(TypeKind::Resolved(id))) => Ok(id),
    //                 Some(Definition::Class(_)) => {
    //                     // let c = self.ctx.interner.get_class(id);
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
        let t = self.ctx.interner.get_ty(ty);
        match &t {
            TcTy::Primitive(_) => true,
            _ => false,
        }
    }

    fn get_size(&self, ty: TyId) -> usize {
        let t = self.ctx.interner.get_ty(ty);
        t.get_size(self.ctx.interner.get_ty_interner())
    }

    fn is_type_ptr(&mut self, ty: TyId) -> bool {
        let t = self.ctx.interner.get_ty(ty);
        matches!(t, TcTy::Ptr(_))
    }

    fn get_last_scope_mut(&mut self) -> &mut Scope {
        self.ctx.interner.get_scope_mut(self.current_scope)
    }

    fn get_last_scope(&self) -> &Scope {
        self.ctx.interner.get_scope(self.current_scope)
    }
}
