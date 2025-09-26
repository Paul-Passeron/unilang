use std::{collections::HashMap, fmt, hash::Hash};

pub trait Interner<'ctx, Value>
where
    Value: Eq,
{
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

impl ConstructibleId for Symbol {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringLiteral(u32);
impl ConstructibleId for StringLiteral {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

pub type SymbolInterner = HashInterner<Symbol, String>;
pub type StringInterner = HashInterner<StringLiteral, String>;
