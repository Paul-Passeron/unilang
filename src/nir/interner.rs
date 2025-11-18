use std::{
    collections::HashMap,
    fmt::{self, Debug},
    hash::Hash,
    marker::PhantomData,
};

use crate::common::global_interner::VariableId;

pub trait Interner<'ctx, Value> {
    type Id;
    fn contains(&'ctx self, v: &Value) -> Option<Self::Id>;
    fn insert(&'ctx mut self, v: Value) -> Self::Id;
    fn get(&'ctx self, id: Self::Id) -> &'ctx Value;
    fn get_mut(&'ctx mut self, id: Self::Id) -> &'ctx mut Value;
    fn len(&'ctx self) -> usize;
    fn clear(&mut self);
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

    fn clear(&mut self) {
        self.map.clear();
        self.last_id = 0;
    }
}

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
        let s = std::any::type_name::<T>();
        let name = if let Some(pos) = s.rfind("::") {
            // Take everything after the last ::
            s[pos + 2..].to_string()
        } else {
            // No :: found, return as is
            s.to_string()
        };
        write!(f, "{}Id({})", name, self.0)
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
    pub fn new() -> Self {
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

    fn clear(&mut self) {
        self.0.clear();
    }
}
