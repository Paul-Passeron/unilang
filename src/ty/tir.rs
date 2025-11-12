use std::collections::HashMap;

use crate::{
    common::global_interner::{
        DefId, FunId, ImplBlockId, SCId, ScopeId, StringLiteral, Symbol, TirExprId, TyId,
        VariableId,
    },
    nir::nir::{FieldAccessKind, NirBinOpKind, Visibility},
    ty::{PrimitiveTy, tir_pass::SpecInfo},
};

pub struct TirCtx {
    pub methods: HashMap<TyId, HashMap<Symbol, FunId>>,
    pub protos: HashMap<FunId, Signature>,
    pub impls: Vec<ImplBlockId>,
    pub class_stack: Vec<SCId>,
    pub specs: HashMap<SpecInfo, TyId>,
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

    // like '.' in C
    Access(TirExprId, FieldAccessKind),

    // like '->' in C
    PtrAccess(TirExprId, FieldAccessKind),

    // Context: let var: type;

    // The value contained in var
    VarExpr(VariableId),

    // The ptr to var (&var) in C
    VarPtr(VariableId),

    // The value in ptr (*ptr) in C
    Deref(TirExprId),

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
    True,
    False,
    Minus(TirExprId),

    // Allocates a ptr to TyId
    Alloca(TyId),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TirInstr {
    Return(Option<TirExprId>),
    VarDecl(VariableId),
    VarAssign(VariableId, TirExprId),
    Assign(TirExprId, TirExprId),
    Calculate(TirExprId),
    If(ScopeId),
    While(ScopeId),
    Block(ScopeId),
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
pub struct SpecializedClass {
    pub original: DefId,
    pub name: Symbol,
    pub templates: Vec<TyId>,
    pub fields: Vec<SCField>,
    pub methods: Vec<FunId>,
    pub constructors: Vec<FunId>,
}
