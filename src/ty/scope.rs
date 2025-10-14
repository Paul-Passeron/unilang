use std::collections::HashMap;

use crate::{
    common::{
        global_interner::{
            ClassId, DefId, FunId, ImplBlockId, ItemId, ModuleId, SCId, ScopeId, ScopeInterner,
            Symbol, TirExprId, TraitId, TyId, TypeExprId, UnresolvedId, VariableId,
        },
        source_location::Span,
    },
    nir::interner::Interner,
    ty::{PrimitiveTy, TcFunProto, TcParam, tir::TirInstr},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TemplateArgument {
    pub name: Symbol,
    pub constraints: Vec<DefId>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TypeExpr {
    Template(usize),
    Associated(usize),
    Instantiation {
        template: DefId,
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

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Pattern {
    Wildcard,
    Symbol(Symbol),
    Tuple(Vec<Pattern>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VarExpr {
    Expr(Option<TirExprId>),
    Param(usize), // nth function parameter
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

#[derive(Debug, Clone)]
pub struct Scope {
    pub kind: ScopeKind,
    pub parent: Option<ScopeId>,
    pub children: Vec<ScopeId>,
    pub definitions: Vec<(Symbol, DefId)>,
}

impl Scope {
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
