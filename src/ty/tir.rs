use std::collections::{HashMap, HashSet};

use crate::{
    common::global_interner::{
        DefId, FunId, ImplBlockId, ItemId, SCId, ScopeId, StringLiteral, Symbol, TirExprId,
        TraitId, TyId, VariableId,
    },
    nir::nir::{FieldAccessKind, NirBinOpKind},
    ty::{PrimitiveTy, TyCtx, displays::Displayable, tir_pass::SpecInfo},
};

pub struct TirCtx {
    pub methods: HashMap<TyId, HashMap<Symbol, FunId>>,
    pub impl_methods: HashMap<TyId, Vec<(Vec<(Symbol, TyId)>, ItemId)>>,
    pub impl_checked: HashSet<TyId>,
    pub protos: HashMap<FunId, Signature>,
    pub impls: Vec<ImplBlockId>,
    pub class_stack: Vec<SCId>,
    pub specs: HashMap<SpecInfo, TyId>,
    pub sc_scopes: HashMap<SCId, ScopeId>,
    pub ty_implements: HashMap<TyId, HashSet<TraitId>>,
    pub check_impls: bool,
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

    // Allocates a stack ptr to TyId
    Alloca(TyId),
    // Allocates a heap ptr to TyId
    Malloc(TyId),

    Subscript {
        ptr: TirExprId,
        index: TirExprId,
    },
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
pub enum ArgsMatch {
    Perfect,
    Casts(Vec<Option<TyId>>),
    No,
}

impl Displayable for ArgsMatch {
    fn to_string(&self, ctx: &TyCtx) -> String {
        match self {
            ArgsMatch::Perfect => format!("Perfect"),
            ArgsMatch::Casts(ids) => format!(
                "Casts: {}",
                ids.iter()
                    .enumerate()
                    .filter(|x| x.1.is_some())
                    .map(|x| format!("{}: {}", x.0, x.1.unwrap().to_string(ctx)))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ArgsMatch::No => format!("No"),
        }
    }
}

impl Signature {
    pub fn get_match(
        &self,
        tir_ctx: &TirCtx,
        ctx: &TyCtx,
        args: &[TyId],
        has_self: bool,
    ) -> ArgsMatch {
        let to_skip = if has_self { 1 } else { 0 };
        let args_len = args.len() + to_skip;
        if args_len < self.params.len() || (args_len > self.params.len() && !self.variadic) {
            return ArgsMatch::No;
        }

        let mut casts = Vec::new();
        let mut perfect = true;
        for (dst, src) in self
            .params
            .iter()
            .skip(to_skip)
            .map(|x| x.ty)
            .zip(args.iter().copied())
        {
            if src == dst {
                casts.push(None)
            } else if src.is_coercible(tir_ctx, ctx, dst) {
                perfect = false;
                casts.push(Some(dst))
            } else {
                return ArgsMatch::No;
            }
        }
        if perfect {
            ArgsMatch::Perfect
        } else {
            ArgsMatch::Casts(casts)
        }
    }
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

impl<'ctx> TirExprId {
    pub fn get_tir(&self, ctx: &'ctx TyCtx<'ctx>) -> &'ctx TirExpr {
        ctx.ctx.interner.get_te(*self)
    }
}
