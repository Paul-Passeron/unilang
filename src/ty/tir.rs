use std::collections::{HashMap, HashSet};

use crate::{
    nir::{
        global_interner::{DefId, FunId, SCId, StringLiteral, Symbol, TirExprId, TyId, VariableId},
        nir::{FieldAccessKind, NirBinOpKind, Visibility},
    },
    ty::PrimitiveTy,
};

pub struct TirCtx {
    pub methods: HashMap<TyId, Vec<TirMethod>>,
    pub protos: HashMap<FunId, Signature>,
    pub calculated: HashSet<TirExprId>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TypedIntLit {
    Ptr(TyId, usize),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    Bool(bool),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TirExpr {
    Arg(usize),
    TypedIntLit(TypedIntLit),
    Access(TirExprId, FieldAccessKind),
    VarExpr(VariableId),
    IntCast(TyId, TirExprId),
    PtrCast(TyId, TirExprId),
    Tuple(Vec<TirExprId>),
    BinOp {
        lhs: TirExprId,
        rhs: TirExprId,
        op: NirBinOpKind,
    },
    Funcall(FunId, Vec<TirExprId>),
    StringLiteral(StringLiteral),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TirInstr {
    Return(Option<TirExprId>),
    VarDecl(VariableId),
    Assign(VariableId, TirExprId),
    Calculate(TirExprId),
}
#[derive(Debug)]
pub enum TirItem {
    Fundef {
        sig: Signature,
        body: Option<Vec<TirInstr>>,
    },
}

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
    pub variadic: bool,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TirMethod {
    pub is_static: bool,
    pub vis: Visibility,
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
    pub constructors: Vec<SCCons>,
}
