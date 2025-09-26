use std::{
    collections::{HashMap, HashSet},
    hash::RandomState,
};

use strum::{EnumIter, IntoEnumIterator};

use crate::nir::{
    context::GlobalContext,
    interner::{ConstructibleId, Interner, ItemId, Symbol, TyId},
    nir::{NirFunctionDef, NirItem, NirProgram, NirStmt, NirStmtKind, NirType, NirTypeKind},
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
    pub ty: FieldTy,
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TcTy {
    Ptr(TyId),
    Primitive(PrimitiveTy),
    Struct {
        generic_args: Vec<TyId>,
        fields: Vec<StructField>,
    },
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
    pub functions: HashMap<ItemId, TcFunProto>,
    pub ctx: &'ctx mut GlobalContext,
}

#[derive(Debug)]
pub enum TcError {
    AlreadyDefinedMethod { ty: TyId, name: Symbol },
    Todo,
    NameNotFound(Symbol),
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
        let mut res = Self {
            types: HashMap::new(),
            methods: HashMap::new(),
            aliases: HashMap::new(),
            functions: HashMap::new(),
            ctx,
        };
        res.add_builtins();
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
                    NirItem::Module(_nir_module_def) => Err(TcError::Todo),
                    NirItem::Class(_nir_class_def) => Err(TcError::Todo),
                    NirItem::Trait(_nir_trait_def) => Err(TcError::Todo),
                    NirItem::Impl(_nir_impl_block) => Err(TcError::Todo),
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
            todo!(
                "Report error for every item that could not type check.\n{:#?}",
                errors
            );
        }
        Ok(())
    }

    fn visit_type(&mut self, ty: &mut NirType) -> Result<TyId, TcError> {
        let res = match &ty.kind {
            NirTypeKind::Resolved(ty_id) => Ok(*ty_id),
            NirTypeKind::Ptr(_nir_type) => todo!(),
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

    fn visit_stmt(&mut self, stmt: &mut NirStmt) -> Result<(), TcError> {
        match &mut stmt.kind {
            NirStmtKind::Expr(_nir_expr) => todo!(),
            NirStmtKind::Block(_nir_stmts) => todo!(),
            NirStmtKind::If { .. } => todo!(),
            NirStmtKind::While { .. } => todo!(),
            NirStmtKind::For { .. } => todo!(),
            NirStmtKind::Let(_nir_var_decl) => todo!(),
            NirStmtKind::Assign { .. } => todo!(),
            NirStmtKind::Return { .. } => todo!(),
            NirStmtKind::Break => todo!(),
        }
    }

    fn visit_fundef(&mut self, fdef: &mut NirFunctionDef, id: ItemId) -> Result<(), TcError> {
        let proto = self.visit_fundef_proto(fdef)?;
        self.functions.insert(id, proto);
        fdef.body
            .iter_mut()
            .map(|body| {
                for stmt in body {
                    self.visit_stmt(stmt)?
                }
                Ok(())
            })
            .collect::<Result<Vec<_>, _>>()?;

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
}
