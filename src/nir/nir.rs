use std::hash::Hash;

use crate::{
    common::source_location::Span,
    nir::interner::{ConstructibleId, HashInterner, Interner, StringLiteral, Symbol},
    ty::TyId,
};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NirItem {
    Function(NirFunctionDef),
    Module(NirModuleDef),
    Class(NirClassDef),
    Trait(NirTraitDef),
    Impl(NirImplBlock),
    Method(NirMethod),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ScopeId(u32);

impl ConstructibleId for ScopeId {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

#[derive(Debug)]
pub enum ScopeKind {
    Global,
    Module(ItemId),
    Trait(ItemId),
    Class(ItemId),
    Function(ItemId),
    Block,
    Loop,
    Impl(ItemId),
}

#[derive(Debug)]
pub struct Scope {
    pub id: ScopeId,
    pub kind: ScopeKind,
    pub parent: Option<ScopeId>,
    pub children: Vec<ScopeId>,
}

impl PartialEq for Scope {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl Eq for Scope {}
#[derive(Debug)]
pub struct ScopeInterner {
    nodes: Vec<Scope>,
}

impl ScopeInterner {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }
}

impl<'ctx> Interner<'ctx, Scope> for ScopeInterner {
    type Id = ScopeId;

    fn contains(&'ctx self, _v: &Scope) -> Option<Self::Id> {
        None
    }

    fn insert(&'ctx mut self, v: Scope) -> Self::Id {
        let id = Self::Id::new(self.nodes.len() as u32);
        self.nodes.push(v);
        id
    }

    fn get(&'ctx self, id: Self::Id) -> &'ctx Scope {
        &self.nodes[id.0 as usize]
    }

    fn get_mut(&'ctx mut self, id: Self::Id) -> &'ctx mut Scope {
        &mut self.nodes[id.0 as usize]
    }
}

#[derive(Debug)]
pub struct ScopeManager {
    pub scope_stack: Vec<ScopeId>,
}

impl ScopeManager {
    pub fn new() -> Self {
        Self {
            scope_stack: Vec::new(),
        }
    }

    pub fn init(&mut self, interner: &mut ScopeInterner) {
        let scope = Scope {
            id: ScopeId(0),
            kind: ScopeKind::Global,
            parent: None,
            children: Vec::new(),
        };
        let scope_id = interner.insert(scope);
        self.scope_stack.push(scope_id);
        interner.get_mut(scope_id).id = scope_id;
        // println!("Inited !");
    }

    pub fn push_scope(&mut self, kind: ScopeKind, interner: &mut ScopeInterner) -> ScopeId {
        let scope = Scope {
            id: ScopeId(0),
            kind,
            parent: None,
            children: Vec::new(),
        };

        let actual_id = interner.insert(scope);

        self.scope_stack.push(actual_id);

        let parent = *self.scope_stack.last().unwrap();
        let mut_parent = interner.get_mut(parent);
        mut_parent.children.push(actual_id);

        let scope = interner.get_mut(actual_id);
        scope.parent = Some(parent);
        scope.id = actual_id;

        actual_id
    }

    pub fn pop_scope(&mut self) -> ScopeId {
        if self.scope_stack.len() < 1 {
            panic!("Compiler bug: Global scope popped");
        }

        let id = self.scope_stack.pop().unwrap();

        id
    }

    pub fn current_scope(&self) -> ScopeId {
        *self.scope_stack.last().unwrap()
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirImplBlock {
    pub implements: Option<NirTraitConstraint>,
    pub generic_args: Vec<NirGenericArg>,
    pub ty: NirType,
    pub types: Vec<NirTypeBound>,
    pub methods: Vec<ItemId>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirAssociatedType {
    pub name: Symbol,
    pub bounds: Vec<NirTraitConstraint>,
    pub default_value: Option<NirType>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirTypeBound {
    pub name: Vec<Symbol>,
    pub ty: NirType,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirTraitDef {
    pub name: Symbol,
    pub ty: NirGenericArg,
    pub types: Vec<NirAssociatedType>,
    pub methods: Vec<ItemId>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NirTypeKind {
    Resolved(TyId),
    Ptr(Box<NirType>),
    Named {
        name: Vec<Symbol>,
        generic_args: Vec<NirType>,
    },
    Tuple(Vec<NirType>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirType {
    pub kind: NirTypeKind,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirFunctionDef {
    pub name: Symbol,
    pub generic_args: Vec<NirGenericArg>,
    pub args: Vec<NirArgument>,
    pub return_ty: NirType,
    pub is_variadic: bool,
    pub body: Option<Vec<NirStmt>>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirArgument {
    pub name: Symbol,
    pub ty: NirType,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirGenericArg {
    pub name: Symbol,
    pub constraints: Vec<NirTraitConstraint>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirTraitConstraint {
    pub name: Symbol,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirModuleDef {
    pub name: Symbol,
    pub items: Vec<ItemId>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum SelfKind {
    ByPtr,
    None,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirMethod {
    pub name: Symbol,
    pub self_kind: SelfKind,
    pub generic_args: Vec<NirGenericArg>,
    pub return_ty: Option<NirType>,
    pub args: Vec<NirArgument>,
    pub body: Option<Vec<NirStmt>>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirClassDef {
    pub name: Symbol,
    pub generic_args: Vec<NirGenericArg>,
    pub methods: Vec<ItemId>, // Can grow, depending on trait resolution
    pub members: Vec<NirMember>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirVarDecl {
    pub pattern: NirPattern,
    pub ty: Option<NirType>,
    pub value: Option<NirExpr>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirMember {
    pub name: Symbol,
    pub ty: NirType,
    pub value: Option<NirExpr>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirStmt {
    pub kind: NirStmtKind,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NirStmtKind {
    Expr(NirExpr),

    Block(Vec<NirStmt>),

    If {
        cond: NirExpr,
        then_block: Box<NirStmt>,
        else_block: Option<Box<NirStmt>>,
    },

    While {
        cond: NirExpr,
        body: Box<NirStmt>,
    },

    For {
        var: NirPattern,
        iterator: NirExpr,
        body: Box<NirStmt>,
    },

    Let(NirVarDecl),

    Assign {
        assigned: NirExpr,
        value: NirExpr,
    },

    Return {
        value: Option<NirExpr>,
    },
    Break,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NirPatternKind {
    Wildcard,
    Symbol(Symbol),
    Tuple(Vec<NirPattern>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirPattern {
    pub kind: NirPatternKind,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone)]
pub struct MyFloat(f64);
pub type F64 = MyFloat;

impl Hash for MyFloat {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let as_int: u64 = self.0.to_bits();
        as_int.hash(state);
    }
}

impl PartialEq for MyFloat {
    fn eq(&self, other: &Self) -> bool {
        let x = self.0.to_bits();
        let y = other.0.to_bits();
        x == y
    }
}

impl Eq for MyFloat {}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NirLiteralKind {
    IntLiteral(i128),
    FloatLiteral(F64),
    StringLiteral(StringLiteral),
    CharLiteral(char),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirLiteral {
    pub kind: NirLiteralKind,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NirBinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Equ,
    Dif,
    LOr,
    LAnd,
    BOr,
    BAnd,
    BXor,
    Geq,
    Leq,
    Gt,
    Lt,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NirUnOpKind {
    Minus,
    LNot,
    BNot,
    Deref,
    AddrOf,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FieldAccess {
    pub kind: FieldAccessKind,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum FieldAccessKind {
    Symbol(Symbol),
    Index(u32),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirCalled {
    pub receiver: Option<Box<NirExpr>>,
    pub called: Symbol,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirCall {
    pub called: NirCalled,
    pub generic_args: Vec<NirType>,
    pub args: Vec<NirExpr>,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirBinOp {
    pub op: NirBinOpKind,
    pub left: Box<NirExpr>,
    pub right: Box<NirExpr>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct NirExpr {
    pub kind: NirExprKind,
    pub span: Span,
    pub scope: ScopeId,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum NirExprKind {
    Literal(NirLiteral),
    BinOp(NirBinOp),
    UnOp {
        op: NirUnOpKind,
        operand: Box<NirExpr>,
    },
    Call(NirCall),
    Subscript {
        value: Box<NirExpr>,
        index: Box<NirExpr>,
    },
    Access {
        from: Box<NirExpr>,
        field: FieldAccess,
    },
    Named(Symbol),
    PostIncr(Box<NirExpr>),
    PreIncr(Box<NirExpr>),
    PostDecr(Box<NirExpr>),
    PreDecr(Box<NirExpr>),
    AddrOf(Box<NirExpr>),
    Deref(Box<NirExpr>),
    SizeOf(NirType),
    StringOf(NirType),
    Minus(Box<NirExpr>),
    Not(Box<NirExpr>),
    New {
        ty: NirType,
        expr: Box<NirExpr>,
    },
    As {
        ty: NirType,
        expr: Box<NirExpr>,
    },
    Tuple(Vec<NirExpr>),
    Range {
        start: Box<NirExpr>,
        end: Box<NirExpr>,
    },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct ItemId(pub u32);

impl ConstructibleId for ItemId {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

pub type ItemInterner = HashInterner<ItemId, NirItem>;

pub struct NirProgram(pub Vec<ItemId>);
