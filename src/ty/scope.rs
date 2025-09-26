use crate::{nir::interner::ScopeId, ty::DefId};

#[derive(Debug, Clone, Copy)]
pub enum ScopeKind {
    Global,
    Module(DefId),
    Class(DefId),
    Function(DefId),
    Loop,
    Condition,
}

#[derive(Debug, Clone)]
pub struct Scope {
    kind: ScopeKind,
    parent: Option<ScopeId>,
    children: Vec<ScopeId>,
}
