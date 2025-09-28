use crate::{
    nir::interner::{
        ClassId, ExprId, FunId, Interner, ModuleId, ScopeId, ScopeInterner, Symbol, TraitId, TyId,
        VariableId,
    },
    ty::TcFunProto,
};

#[derive(Debug, Clone)]
pub struct TemplateArgument {
    pub name: Symbol,
    pub constraints: Vec<TraitId>,
}

#[derive(Debug, Clone)]
pub enum TypeExpr {
    Resolved(TyId),
    Template(usize),
    Instantiation {
        template: Definition,
        args: Vec<TypeExpr>,
    },
    Ptr(Box<TypeExpr>),
    Tuple(Vec<TypeExpr>),
}

#[derive(Debug, Clone)]
pub struct ClassMember {
    pub name: Symbol,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone)]
pub struct Class {
    pub name: Symbol,
    pub templates: Vec<TemplateArgument>,
    pub members: Vec<ClassMember>,
}

#[derive(Debug, Clone)]
pub struct Module {}

#[derive(Debug, Clone)]
pub enum ScopeKind {
    Global,
    Module(ModuleId),
    Class(ClassId),
    Function(FunId),
    Loop,
    Condition,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Pattern {
    Wildcard,
    Symbol(Symbol),
    Tuple(Vec<Pattern>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VarExpr {
    Expr(Option<ExprId>),
    Param(usize), // nth function parameter
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarDecl {
    pub name: Pattern,
    pub ty: TyId,
    pub expr: VarExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Trait {
    pub name: Symbol,
    pub methods: Vec<TcFunProto>,
}
#[derive(Debug, Clone, Copy)]
pub enum TypeKind {
    Resolved(TyId),
    Templated(usize),
}

#[derive(Debug, Clone, Copy)]
pub enum Definition {
    Class(ClassId),
    Function(FunId),
    Module(ModuleId),
    Variable(VariableId),
    Trait(TraitId),
    Type(TypeKind),
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub kind: ScopeKind,
    pub parent: Option<ScopeId>,
    pub children: Vec<ScopeId>,
    pub definitions: Vec<(Symbol, Definition)>,
}

impl Scope {
    pub fn get_definition_for_symbol(
        &self,
        symb: Symbol,
        interner: &ScopeInterner,
    ) -> Option<Definition> {
        for (s, def) in &self.definitions {
            if *s == symb {
                return Some(*def);
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
