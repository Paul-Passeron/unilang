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
        scope::{Class, ImplBlock, Module, Scope, Trait, TypeExpr, Unresolved, VarDecl},
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

#[derive(Debug, Clone)]
pub struct GlobalInterner {
    pub symbol_interner: SymbolInterner,
    pub string_interner: StringInterner,
    pub item_interner: ItemInterner,
    pub expr_interner: ExprInterner,
    pub type_interner: TypeInterner,
    pub scope_interner: ScopeInterner,
    pub fun_interner: FunInterner,
    pub class_interner: ClassInterner,
    pub module_interner: ModuleInterner,
    pub variable_interner: VariableInterner,
    pub trait_interner: TraitInterner,
    pub type_expr_interner: TypeExprInterner,
    pub impl_interner: ImplBlockInterner,
}

impl GlobalInterner {
    pub fn new() -> Self {
        Self {
            symbol_interner: SymbolInterner::new(),
            string_interner: StringInterner::new(),
            item_interner: ItemInterner::new(),
            expr_interner: ExprInterner::new(),
            type_interner: TypeInterner::new(),
            scope_interner: ScopeInterner::new(),
            fun_interner: FunInterner::new(),
            class_interner: ClassInterner::new(),
            module_interner: ModuleInterner::new(),
            variable_interner: VariableInterner::new(),
            trait_interner: TraitInterner::new(),
            type_expr_interner: TypeExprInterner::new(),
            impl_interner: ImplBlockInterner::new(),
        }
    }

    pub fn get_symbol<'ctx>(&'ctx self, id: Symbol) -> &'ctx String {
        self.symbol_interner.get(id)
    }

    pub fn get_string<'ctx>(&'ctx self, id: StringLiteral) -> &'ctx String {
        self.string_interner.get(id)
    }

    pub fn get_item<'ctx>(&'ctx self, id: ItemId) -> &'ctx NirItem {
        &self.item_interner.get(id)
    }

    pub fn get_expr<'ctx>(&'ctx self, id: ExprId) -> &'ctx NirExpr {
        &self.expr_interner.get(id)
    }

    pub fn get_mut_symbol<'ctx>(&'ctx mut self, id: Symbol) -> &'ctx mut String {
        self.symbol_interner.get_mut(id)
    }

    pub fn get_mut_string<'ctx>(&'ctx mut self, id: StringLiteral) -> &'ctx mut String {
        self.string_interner.get_mut(id)
    }

    pub fn get_mut_item<'ctx>(&'ctx mut self, id: ItemId) -> &'ctx mut NirItem {
        self.item_interner.get_mut(id)
    }

    pub fn get_mut_expr<'ctx>(&'ctx mut self, id: ExprId) -> &'ctx mut NirExpr {
        self.expr_interner.get_mut(id)
    }

    pub fn insert_symbol<'ctx>(&'ctx mut self, val: &String) -> Symbol {
        if let Some(id) = self.symbol_interner.contains(val) {
            id
        } else {
            self.symbol_interner.insert(val.clone())
        }
    }

    pub fn get_symbol_for<'ctx>(&'ctx self, id: &str) -> Option<Symbol> {
        self.symbol_interner.contains(&id.to_string())
    }

    pub fn insert_string<'ctx>(&'ctx mut self, val: &String) -> StringLiteral {
        if let Some(id) = self.string_interner.contains(val) {
            id
        } else {
            self.string_interner.insert(val.clone())
        }
    }

    pub fn insert_item<'ctx>(&'ctx mut self, val: NirItem) -> ItemId {
        self.item_interner.insert(val)
    }

    pub fn insert_expr<'ctx>(&'ctx mut self, val: NirExpr) -> ExprId {
        self.expr_interner.insert(val)
    }

    pub fn debug_print(&self) {
        println!("symbol_interner: {} items", self.symbol_interner.len());
        println!("string_interner: {} items", self.string_interner.len());
        println!("item_interner: {} items", self.item_interner.len());
        println!("expr_interner: {} items", self.expr_interner.len());
        println!("type_interner: {} items", self.type_interner.len());
        println!("scope_interner: {} items", self.scope_interner.len());
        println!("fun_interner: {} items", self.fun_interner.len());
        println!("class_interner: {} items", self.class_interner.len());
        println!("module_interner: {} items", self.module_interner.len());
        println!("variable_interner: {} items", self.variable_interner.len());
        println!("trait_interner: {} items", self.trait_interner.len());
        println!(
            "type_expr_interner: {} items",
            self.type_expr_interner.len()
        );
        println!("impl_interner: {} items", self.impl_interner.len());
    }
}
