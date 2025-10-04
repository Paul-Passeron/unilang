use std::{
    collections::HashMap,
    fmt::{self, Debug},
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    nir::nir::{NirExpr, NirItem},
    ty::{
        TcFunProto, TcTy,
        scope::{
            Class, Definition, ImplBlock, Module, Scope, Trait, TypeExpr, Unresolved, VarDecl,
        },
    },
};

pub trait Interner<'ctx, Value> {
    type Id;
    fn contains(&'ctx self, v: &Value) -> Option<Self::Id>;
    fn insert(&'ctx mut self, v: Value) -> Self::Id;
    fn get(&'ctx self, id: Self::Id) -> &'ctx Value;
    fn get_mut(&'ctx mut self, id: Self::Id) -> &'ctx mut Value;
    fn len(&'ctx self) -> usize;
}

pub trait ConstructibleId: fmt::Debug + Eq + Hash + Copy {
    fn new(id: u32) -> Self;
}

#[derive(Debug, Clone)]
pub struct HashInterner<Id: ConstructibleId, Value> {
    last_id: u32,
    map: HashMap<Id, Value>,
}

impl<Id: ConstructibleId, Value: Hash + Eq + Clone> HashInterner<Id, Value> {
    pub fn new() -> Self {
        Self {
            last_id: 0,
            map: HashMap::new(),
        }
    }
}

impl<'ctx, Id: ConstructibleId, Value: Hash + Eq + Clone> Interner<'ctx, Value>
    for HashInterner<Id, Value>
{
    type Id = Id;

    fn contains(&'ctx self, v: &Value) -> Option<Self::Id> {
        self.map
            .iter()
            .find_map(|(k, val)| (val == v).then_some(*k))
    }

    fn insert(&'ctx mut self, v: Value) -> Self::Id {
        if let Some(id) = self.contains(&v) {
            id
        } else {
            let res = Id::new(self.last_id);
            self.last_id += 1;
            self.map.insert(res, v);
            res
        }
    }

    fn get(&'ctx self, id: Self::Id) -> &'ctx Value {
        self.map.get(&id).unwrap()
    }

    fn get_mut(&'ctx mut self, id: Self::Id) -> &'ctx mut Value {
        self.map.get_mut(&id).unwrap()
    }

    fn len(&'ctx self) -> usize {
        self.map.len()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringLiteral(u32);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ItemId(pub u32);
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyId(pub u32);

impl ConstructibleId for Symbol {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

impl ConstructibleId for StringLiteral {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

impl ConstructibleId for ItemId {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

impl ConstructibleId for ExprId {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

impl ConstructibleId for TyId {
    fn new(id: u32) -> Self {
        Self(id)
    }
}
pub type SymbolInterner = HashInterner<Symbol, String>;
pub type StringInterner = HashInterner<StringLiteral, String>;
pub type ItemInterner = HashInterner<ItemId, NirItem>;
pub type ExprInterner = HashInterner<ExprId, NirExpr>;
pub type TypeInterner = HashInterner<TyId, TcTy>;

#[derive(Debug, Clone)]
pub struct OneShotInterner<T>(Vec<T>);
pub struct OneShotId<T>(pub u32, PhantomData<T>);

impl<T> Hash for OneShotId<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T> PartialEq for OneShotId<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for OneShotId<T> {}

impl<T> fmt::Debug for OneShotId<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}({})", std::any::type_name::<T>(), self.0)
    }
}

impl<T> Clone for OneShotId<T> {
    fn clone(&self) -> Self {
        Self(self.0, PhantomData::default())
    }
}

impl<T> Copy for OneShotId<T> {}

impl<T: fmt::Debug> ConstructibleId for OneShotId<T> {
    fn new(id: u32) -> Self {
        Self(id, PhantomData::default())
    }
}

impl<T> OneShotInterner<T> {
    fn new() -> Self {
        Self(Vec::new())
    }
}

impl<'ctx, T> Interner<'ctx, T> for OneShotInterner<T>
where
    T: Debug,
{
    type Id = OneShotId<T>;

    fn contains(&'ctx self, _: &T) -> Option<Self::Id> {
        None
    }

    fn insert(&'ctx mut self, v: T) -> Self::Id {
        let id = OneShotId::new(self.0.len() as u32);
        self.0.push(v);
        id
    }

    fn get(&'ctx self, id: Self::Id) -> &'ctx T {
        &self.0[id.0 as usize]
    }

    fn get_mut(&'ctx mut self, id: Self::Id) -> &'ctx mut T {
        &mut self.0[id.0 as usize]
    }

    fn len(&'ctx self) -> usize {
        self.0.len()
    }
}

pub type ScopeInterner = OneShotInterner<Scope>;
pub type ScopeId = OneShotId<Scope>;

pub type ModuleInterner = OneShotInterner<Module>;
pub type ModuleId = OneShotId<Module>;

pub type ClassInterner = OneShotInterner<Class>;
pub type ClassId = OneShotId<Class>;

pub type FunInterner = OneShotInterner<TcFunProto>;
pub type FunId = OneShotId<TcFunProto>;

pub type VariableInterner = OneShotInterner<VarDecl>;
pub type VariableId = OneShotId<VarDecl>;

pub type TraitInterner = OneShotInterner<Trait>;
pub type TraitId = OneShotId<Trait>;

pub type UnresolvedInterner = HashInterner<UnresolvedId, Unresolved>;
pub type UnresolvedId = OneShotId<Unresolved>;

pub type ImplBlockInterner = OneShotInterner<ImplBlock>;
pub type ImplBlockId = OneShotId<ImplBlock>;

pub type TypeExprId = OneShotId<TypeExpr>;
pub type TypeExprInterner = HashInterner<TypeExprId, TypeExpr>;

pub type DefInterner = OneShotInterner<Definition>;
pub type DefId = OneShotId<Definition>;

#[derive(Debug, Clone)]
pub struct GlobalInterner {
    symbol: SymbolInterner,
    string: StringInterner,
    item: ItemInterner,
    expr: ExprInterner,
    ty: TypeInterner,
    scope: ScopeInterner,
    fun: FunInterner,
    class: ClassInterner,
    module: ModuleInterner,
    variable: VariableInterner,
    tr: TraitInterner,
    type_expr: TypeExprInterner,
    imp: ImplBlockInterner,
    def: DefInterner,
}

impl GlobalInterner {
    pub fn new() -> Self {
        Self {
            symbol: SymbolInterner::new(),
            string: StringInterner::new(),
            item: ItemInterner::new(),
            expr: ExprInterner::new(),
            ty: TypeInterner::new(),
            scope: ScopeInterner::new(),
            fun: FunInterner::new(),
            class: ClassInterner::new(),
            module: ModuleInterner::new(),
            variable: VariableInterner::new(),
            tr: TraitInterner::new(),
            type_expr: TypeExprInterner::new(),
            imp: ImplBlockInterner::new(),
            def: DefInterner::new(),
        }
    }

    pub fn insert_symbol(&mut self, value: &String) -> Symbol {
        if let Some(res) = self.symbol.contains(value) {
            res
        } else {
            self.symbol.insert(value.clone())
        }
    }
    pub fn insert_string(&mut self, value: &String) -> StringLiteral {
        if let Some(res) = self.string.contains(value) {
            res
        } else {
            self.string.insert(value.clone())
        }
    }

    pub fn insert_item(&mut self, value: NirItem) -> ItemId {
        self.item.insert(value)
    }
    pub fn insert_expr(&mut self, value: NirExpr) -> ExprId {
        self.expr.insert(value)
    }
    pub fn insert_ty(&mut self, value: TcTy) -> TyId {
        self.ty.insert(value)
    }
    pub fn insert_scope(&mut self, value: Scope) -> ScopeId {
        self.scope.insert(value)
    }
    pub fn insert_fun(&mut self, value: TcFunProto) -> FunId {
        self.fun.insert(value)
    }
    pub fn insert_class(&mut self, value: Class) -> ClassId {
        self.class.insert(value)
    }
    pub fn insert_module(&mut self, value: Module) -> ModuleId {
        self.module.insert(value)
    }
    pub fn insert_variable(&mut self, value: VarDecl) -> VariableId {
        self.variable.insert(value)
    }
    pub fn insert_tr(&mut self, value: Trait) -> TraitId {
        self.tr.insert(value)
    }
    pub fn insert_type_expr(&mut self, value: TypeExpr) -> TypeExprId {
        self.type_expr.insert(value)
    }
    pub fn insert_imp(&mut self, value: ImplBlock) -> ImplBlockId {
        self.imp.insert(value)
    }
    pub fn insert_def(&mut self, value: Definition) -> DefId {
        self.def.insert(value)
    }

    pub fn get_symbol(&self, id: Symbol) -> &String {
        self.symbol.get(id)
    }
    pub fn get_string(&self, id: StringLiteral) -> &String {
        self.string.get(id)
    }
    pub fn get_item(&self, id: ItemId) -> &NirItem {
        self.item.get(id)
    }
    pub fn get_expr(&self, id: ExprId) -> &NirExpr {
        self.expr.get(id)
    }
    pub fn get_ty(&self, id: TyId) -> &TcTy {
        self.ty.get(id)
    }
    pub fn get_scope(&self, id: ScopeId) -> &Scope {
        self.scope.get(id)
    }
    pub fn get_fun(&self, id: FunId) -> &TcFunProto {
        self.fun.get(id)
    }
    pub fn get_class(&self, id: ClassId) -> &Class {
        self.class.get(id)
    }
    pub fn get_module(&self, id: ModuleId) -> &Module {
        self.module.get(id)
    }
    pub fn get_variable(&self, id: VariableId) -> &VarDecl {
        self.variable.get(id)
    }
    pub fn get_tr(&self, id: TraitId) -> &Trait {
        self.tr.get(id)
    }
    pub fn get_type_expr(&self, id: TypeExprId) -> &TypeExpr {
        self.type_expr.get(id)
    }
    pub fn get_imp(&self, id: ImplBlockId) -> &ImplBlock {
        self.imp.get(id)
    }
    pub fn get_def(&self, id: DefId) -> &Definition {
        self.def.get(id)
    }

    pub fn get_symbol_mut(&mut self, id: Symbol) -> &mut String {
        self.symbol.get_mut(id)
    }
    pub fn get_string_mut(&mut self, id: StringLiteral) -> &mut String {
        self.string.get_mut(id)
    }
    pub fn get_item_mut(&mut self, id: ItemId) -> &mut NirItem {
        self.item.get_mut(id)
    }
    pub fn get_expr_mut(&mut self, id: ExprId) -> &mut NirExpr {
        self.expr.get_mut(id)
    }
    pub fn get_ty_mut(&mut self, id: TyId) -> &mut TcTy {
        self.ty.get_mut(id)
    }
    pub fn get_scope_mut(&mut self, id: ScopeId) -> &mut Scope {
        self.scope.get_mut(id)
    }
    pub fn get_fun_mut(&mut self, id: FunId) -> &mut TcFunProto {
        self.fun.get_mut(id)
    }
    pub fn get_class_mut(&mut self, id: ClassId) -> &mut Class {
        self.class.get_mut(id)
    }
    pub fn get_module_mut(&mut self, id: ModuleId) -> &mut Module {
        self.module.get_mut(id)
    }
    pub fn get_variable_mut(&mut self, id: VariableId) -> &mut VarDecl {
        self.variable.get_mut(id)
    }
    pub fn get_tr_mut(&mut self, id: TraitId) -> &mut Trait {
        self.tr.get_mut(id)
    }
    pub fn get_type_expr_mut(&mut self, id: TypeExprId) -> &mut TypeExpr {
        self.type_expr.get_mut(id)
    }
    pub fn get_imp_mut(&mut self, id: ImplBlockId) -> &mut ImplBlock {
        self.imp.get_mut(id)
    }
    pub fn get_def_mut(&mut self, id: DefId) -> &mut Definition {
        self.def.get_mut(id)
    }

    pub fn contains_item(&self, value: &NirItem) -> Option<ItemId> {
        self.item.contains(value)
    }
    pub fn contains_expr(&self, value: &NirExpr) -> Option<ExprId> {
        self.expr.contains(value)
    }
    pub fn contains_ty(&self, value: &TcTy) -> Option<TyId> {
        self.ty.contains(value)
    }
    pub fn contains_scope(&self, value: &Scope) -> Option<ScopeId> {
        self.scope.contains(value)
    }
    pub fn contains_fun(&self, value: &TcFunProto) -> Option<FunId> {
        self.fun.contains(value)
    }
    pub fn contains_class(&self, value: &Class) -> Option<ClassId> {
        self.class.contains(value)
    }
    pub fn contains_module(&self, value: &Module) -> Option<ModuleId> {
        self.module.contains(value)
    }
    pub fn contains_variable(&self, value: &VarDecl) -> Option<VariableId> {
        self.variable.contains(value)
    }
    pub fn contains_tr(&self, value: &Trait) -> Option<TraitId> {
        self.tr.contains(value)
    }
    pub fn contains_type_expr(&self, value: &TypeExpr) -> Option<TypeExprId> {
        self.type_expr.contains(value)
    }
    pub fn contains_imp(&self, value: &ImplBlock) -> Option<ImplBlockId> {
        self.imp.contains(value)
    }
    pub fn contains_def(&self, value: &Definition) -> Option<DefId> {
        self.def.contains(value)
    }

    pub fn debug_print(&self) {
        println!("symbol_interner: {} items", self.symbol.len());
        println!("string_interner: {} items", self.string.len());
        println!("item_interner: {} items", self.item.len());
        println!("expr_interner: {} items", self.expr.len());
        println!("type_interner: {} items", self.ty.len());
        println!("scope_interner: {} items", self.scope.len());
        println!("fun_interner: {} items", self.fun.len());
        println!("class_interner: {} items", self.class.len());
        println!("module_interner: {} items", self.module.len());
        println!("variable_interner: {} items", self.variable.len());
        println!("trait_interner: {} items", self.tr.len());
        println!("type_expr_interner: {} items", self.ty.len());
        println!("impl_interner: {} items", self.imp.len());
    }

    pub fn get_symbol_for(&self, value: &String) -> Symbol {
        self.symbol.contains(value).unwrap()
    }

    pub fn scope_interner(&self) -> &OneShotInterner<Scope> {
        &self.scope
    }
    pub fn get_ty_interner(&self) -> &TypeInterner {
        &self.ty
    }
}
