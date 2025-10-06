use crate::{
    nir::interner::{DefId, SCId, Symbol, TyId},
    ty::PrimitiveTy,
};
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TirExpr {}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TirInstr {}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ConcreteType {
    SpecializedClass(SCId),
    Primitive(PrimitiveTy),
    Ptr(TyId),
    Tuple(Vec<TyId>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SCField {
    pub name: Symbol,
    pub ty: TyId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Signature {
    pub name: Symbol,
    pub params: Vec<SCField>,
    pub return_ty: TyId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SCMethod {
    pub sig: Signature,
    pub body: Option<Vec<TirInstr>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SCCons {
    pub params: Vec<SCField>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct SpecializedClass {
    pub original: DefId,
    pub templates: TyId,
    pub fields: Vec<SCField>,
    pub methods: Vec<SCMethod>,
    pub constructors: Vec<SCCons>,
}
