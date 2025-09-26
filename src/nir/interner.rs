use std::{collections::HashMap, fmt, hash::Hash};

use crate::{
    nir::nir::{NirExpr, NirItem},
    ty::{TcTy, scope::Scope},
};

pub trait Interner<'ctx, Value> {
    type Id;
    fn contains(&'ctx self, v: &Value) -> Option<Self::Id>;
    fn insert(&'ctx mut self, v: Value) -> Self::Id;
    fn get(&'ctx self, id: Self::Id) -> &'ctx Value;
    fn get_mut(&'ctx mut self, id: Self::Id) -> &'ctx mut Value;
}

pub trait ConstructibleId: fmt::Debug + Eq + Hash + Copy {
    fn new(id: u32) -> Self;
}

#[derive(Debug, Clone)]
pub struct HashInterner<Id: ConstructibleId, Value> {
    last_id: u32,
    map: HashMap<Id, Value>,
    rev_map: HashMap<Value, Id>,
}

impl<Id: ConstructibleId, Value: Hash + Eq + Clone> HashInterner<Id, Value> {
    pub fn new() -> Self {
        Self {
            last_id: 0,
            map: HashMap::new(),
            rev_map: HashMap::new(),
        }
    }
}

impl<'ctx, Id: ConstructibleId, Value: Hash + Eq + Clone> Interner<'ctx, Value>
    for HashInterner<Id, Value>
{
    type Id = Id;

    fn contains(&'ctx self, v: &Value) -> Option<Self::Id> {
        self.rev_map.get(v).map(|x| *x)
    }

    fn insert(&'ctx mut self, v: Value) -> Self::Id {
        if let Some(id) = self.contains(&v) {
            id
        } else {
            let res = Id::new(self.last_id);
            self.last_id += 1;
            self.rev_map.insert(v.clone(), res);
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

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

impl ConstructibleId for ScopeId {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

pub type SymbolInterner = HashInterner<Symbol, String>;
pub type StringInterner = HashInterner<StringLiteral, String>;
pub type ItemInterner = HashInterner<ItemId, NirItem>;
pub type ExprInterner = HashInterner<ExprId, NirExpr>;
pub type TypeInterner = HashInterner<TyId, TcTy>;

#[derive(Debug)]
pub struct ScopeInterner(Vec<Scope>);

impl ScopeInterner {
    fn new() -> Self {
        Self(Vec::new())
    }
}

impl<'ctx> Interner<'ctx, Scope> for ScopeInterner {
    type Id = ScopeId;

    fn contains(&'ctx self, _: &Scope) -> Option<Self::Id> {
        None
    }

    fn insert(&'ctx mut self, v: Scope) -> Self::Id {
        let id = ScopeId::new(self.0.len() as u32);
        self.0.push(v);
        id
    }

    fn get(&'ctx self, id: Self::Id) -> &'ctx Scope {
        self.0.get(id.0 as usize).unwrap()
    }

    fn get_mut(&'ctx mut self, id: Self::Id) -> &'ctx mut Scope {
        self.0.get_mut(id.0 as usize).unwrap()
    }
}

#[derive(Debug)]
pub struct GlobalInterner {
    pub symbol_interner: SymbolInterner,
    pub string_interner: StringInterner,
    pub item_interner: ItemInterner,
    pub expr_interner: ExprInterner,
    pub type_interner: TypeInterner,
    pub scope_interner: ScopeInterner,
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
}
