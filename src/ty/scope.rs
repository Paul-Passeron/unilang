use std::collections::HashMap;

use crate::{
    common::{
        global_interner::{
            ClassId, DefId, FunId, ImplBlockId, ItemId, ModuleId, SCId, ScopeId, ScopeInterner,
            Symbol, TirExprId, TraitId, TyId, TypeExprId, UnresolvedId, VariableId,
        },
        source_location::Span,
    },
    nir::{interner::Interner, nir::NirPath},
    ty::{
        PrimitiveTy, TcFunProto, TcParam, TyCtx,
        displays::Displayable,
        tir::{Signature, TirCtx, TirInstr},
    },
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TemplateArgument {
    pub name: Symbol,
    pub constraints: Vec<DefId>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TypeExpr {
    Template(Symbol),
    Associated(usize),
    Instantiation {
        template: (DefId, NirPath),
        args: Vec<TypeExprId>,
    },
    Ptr(TypeExprId),
    Tuple(Vec<TypeExprId>),
    Primitive(PrimitiveTy),
    Concrete(TyId),
}

#[derive(Debug, Clone)]
pub struct ClassMember {
    pub name: Symbol,
    pub ty: TypeExprId,
}

#[derive(Debug, Clone)]
pub enum MethodKind {
    Method { return_type: TypeExprId },
    Constructor,
}

#[derive(Debug, Clone)]
pub struct Method {
    pub name: Symbol,
    pub kind: MethodKind,
    pub args: Vec<TcParam>,
    pub id: ItemId,
}

#[derive(Debug, Clone)]
pub struct Class {
    pub name: Symbol,
    pub templates: Vec<TemplateArgument>,
    pub members: Vec<ClassMember>,
    pub methods: Vec<Method>,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub name: Symbol,
    pub scope: ScopeId,
}

impl ModuleId {
    pub fn get_module<'ctx>(&self, ctx: &'ctx TyCtx<'ctx>) -> &'ctx Module {
        ctx.ctx.interner.get_module(*self)
    }
    pub fn get_name<'ctx>(&self, ctx: &'ctx TyCtx<'ctx>) -> String {
        self.get_module(ctx).name.to_string(ctx)
    }
}

#[derive(Debug, Clone, Hash)]
pub enum ScopeKind {
    Global,
    Module(ModuleId, ItemId),
    Class(ClassId, ItemId),
    Function(FunId, ItemId, Vec<TirInstr>),
    Trait(TraitId, ItemId),
    Block(Vec<TirInstr>),
    Impl(ImplBlockId, ItemId),

    If { cond: TirExprId },
    Then(Vec<TirInstr>),
    Else(Vec<TirInstr>),

    While,
    WhileCond(Vec<TirInstr>),
    WhileLoop(TirExprId, Vec<TirInstr>),

    Spec(SCId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarDecl {
    pub name: Symbol,
    pub ty: TyId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TraitType {
    pub name: Symbol,
    pub constraints: Vec<DefId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trait {
    pub name: Symbol,
    pub for_ty: TemplateArgument,
    pub methods: Vec<TcFunProto>,
    pub types: Vec<TraitType>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum UnresolvedKind {
    Symb(Symbol, Span),
    From(UnresolvedId, Symbol),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Unresolved {
    pub scope: ScopeId,
    pub kind: UnresolvedKind,
}

#[derive(Debug, Clone)]
pub enum ImplKind {
    WithTrait {
        impl_trait: DefId,
        types: HashMap<Symbol, TypeExprId>,
    },
    NoTrait,
}

#[derive(Debug, Clone)]
pub struct ImplBlock {
    pub for_ty: TypeExprId,
    pub templates: Vec<TemplateArgument>,
    pub methods: Vec<Method>,
    pub kind: ImplKind,
    pub types: HashMap<Symbol, TypeExprId>,
}

impl<'ctx> ImplBlockId {
    pub fn get_block(&self, ctx: &'ctx TyCtx<'ctx>) -> &'ctx ImplBlock {
        ctx.ctx.interner.get_imp(*self)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Definition {
    Class(ClassId),
    Function(FunId),
    Module(ModuleId),
    Trait(TraitId),
    Type(TypeExprId),
    Unresolved(UnresolvedId),
    Var(VariableId),
}

impl DefId {
    pub fn get_def<'ctx>(&self, ctx: &'ctx TyCtx<'ctx>) -> &'ctx Definition {
        ctx.ctx.interner.get_def(*self)
    }
}

#[derive(Debug, Clone, Hash)]
pub struct Scope {
    pub kind: ScopeKind,
    pub parent: Option<ScopeId>,
    pub children: Vec<ScopeId>,
    pub definitions: Vec<(Symbol, DefId)>,
}

impl PartialEq for ScopeKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ScopeKind::Function(id1, _, _), ScopeKind::Function(id2, _, _)) if id1 == id2 => true,
            (ScopeKind::Spec(id1), ScopeKind::Spec(id2)) if id1 == id2 => true,
            (ScopeKind::Class(id1, _), ScopeKind::Class(id2, _)) if id1 == id2 => true,
            _ => false,
        }
    }
}

impl PartialEq for Scope {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.parent == other.parent
            && self.children == other.children
            && self.definitions == other.definitions
    }
}

impl ScopeKind {
    pub fn as_int(&self) -> usize {
        match self {
            ScopeKind::Global => 0,
            ScopeKind::Module(_, _) => 1,
            ScopeKind::Class(_, _) => 2,
            ScopeKind::Function(_, _, _) => 2,
            ScopeKind::Trait(_, _) => 2,
            ScopeKind::Block(_) => 3,
            ScopeKind::Impl(_, _) => 2,
            ScopeKind::If { .. } => 3,
            ScopeKind::Then(_) => 3,
            ScopeKind::Else(_) => 3,
            ScopeKind::While => 3,
            ScopeKind::WhileCond(_) => 3,
            ScopeKind::WhileLoop(_, _) => 3,
            ScopeKind::Spec(_) => 2,
        }
    }
}

impl PartialOrd for ScopeKind {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_int().partial_cmp(&other.as_int())
    }
}

impl Eq for Scope {}

impl Scope {
    pub fn kind_matches(&self, kind: &ScopeKind) -> bool {
        self.kind.eq(kind)
    }

    pub fn get_definition_for_symbol(
        &self,
        symb: Symbol,
        interner: &ScopeInterner,
    ) -> Option<DefId> {
        // We want the last def first
        for (s, def) in self.definitions.iter().rev() {
            if *s == symb {
                return Some(def.clone());
            }
        }
        self.parent
            .map(|x| {
                let scope = interner.get(x);
                scope.get_definition_for_symbol(symb, interner)
            })
            .flatten()
    }
}

impl<'ctx> FunId {
    pub fn get_fun(&self, ctx: &'ctx TyCtx<'ctx>) -> &'ctx TcFunProto {
        ctx.ctx.interner.get_fun(*self)
    }

    pub fn return_type(&self, tir: &TirCtx) -> TyId {
        tir.protos[self].return_ty
    }

    pub fn sig(&self, tir: &'ctx TirCtx) -> &'ctx Signature {
        &tir.protos[self]
    }
}

impl<'ctx> VariableId {
    pub fn get_var(&self, ctx: &'ctx TyCtx<'ctx>) -> &'ctx VarDecl {
        ctx.ctx.interner.get_variable(*self)
    }
}
