use crate::{
    nir::interner::{
        ClassId, ExprId, FunId, Interner, ModuleId, ScopeId, ScopeInterner, Symbol, TyId,
        VariableId,
    },
    ty::DefId,
};

#[derive(Debug)]
pub struct TemplateArgument {
    pub name: Symbol,
    pub constraints: Vec<DefId>,
}

#[derive(Debug)]
pub struct Class {
    pub name: Symbol,
    pub templates: Vec<TemplateArgument>,
}

#[derive(Debug)]
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
pub struct VarDecl {
    pub name: Pattern,
    pub ty: TyId,
    pub expr: Option<ExprId>,
}

#[derive(Debug, Clone, Copy)]
pub enum Definition {
    Class(ClassId),
    Function(FunId),
    Module(ModuleId),
    Variable(VariableId),
    Builtin(TyId),
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
