use crate::{
    nir::{
        interner::{HashInterner, Interner, OneShotId, OneShotInterner},
        nir::{NirExpr, NirItem, StrLit},
    },
    ty::{
        TcFunProto,
        scope::{
            Class, Definition, ImplBlock, Module, Scope, Trait, TypeExpr, Unresolved, VarDecl,
        },
        tir::{ConcreteType, SpecializedClass},
    },
};

pub type Symbol = OneShotId<String>;
pub type SymbolInterner = HashInterner<Symbol, String>;

pub type StringLiteral = OneShotId<StrLit>;
pub type StringInterner = HashInterner<StringLiteral, StrLit>;

pub type ItemId = OneShotId<NirItem>;
pub type ItemInterner = HashInterner<ItemId, NirItem>;

pub type ExprId = OneShotId<NirExpr>;
pub type ExprInterner = HashInterner<ExprId, NirExpr>;

pub type ScopeInterner = OneShotInterner<Scope>;
pub type ScopeId = OneShotId<Scope>;

pub type ModuleInterner = OneShotInterner<Module>;
pub type ModuleId = OneShotId<Module>;

pub type ClassInterner = OneShotInterner<Class>;
pub type ClassId = OneShotId<Class>;

pub type FunInterner = OneShotInterner<TcFunProto>;
pub type FunId = OneShotId<TcFunProto>;

pub type VariableInterner = OneShotInterner<VarDecl>;
pub type VariableId = OneShotId<VarDecl>;

pub type TraitInterner = OneShotInterner<Trait>;
pub type TraitId = OneShotId<Trait>;

pub type UnresolvedInterner = HashInterner<UnresolvedId, Unresolved>;
pub type UnresolvedId = OneShotId<Unresolved>;

pub type ImplBlockInterner = OneShotInterner<ImplBlock>;
pub type ImplBlockId = OneShotId<ImplBlock>;

pub type TypeExprId = OneShotId<TypeExpr>;
pub type TypeExprInterner = HashInterner<TypeExprId, TypeExpr>;

pub type DefInterner = HashInterner<DefId, Definition>;
pub type DefId = OneShotId<Definition>;

pub type ConcreteTypeInterner = HashInterner<TyId, ConcreteType>;
pub type TyId = OneShotId<ConcreteType>;

pub type SCInterner = HashInterner<SCId, SpecializedClass>;
pub type SCId = OneShotId<SpecializedClass>;

#[derive(Debug, Clone)]
pub struct GlobalInterner {
    symbol: SymbolInterner,
    string: StringInterner,
    item: ItemInterner,
    expr: ExprInterner,
    scope: ScopeInterner,
    fun: FunInterner,
    class: ClassInterner,
    module: ModuleInterner,
    variable: VariableInterner,
    tr: TraitInterner,
    type_expr: TypeExprInterner,
    imp: ImplBlockInterner,
    def: DefInterner,
    unresolved: UnresolvedInterner,
}

impl GlobalInterner {
    pub fn new() -> Self {
        Self {
            symbol: SymbolInterner::new(),
            string: StringInterner::new(),
            item: ItemInterner::new(),
            expr: ExprInterner::new(),
            scope: ScopeInterner::new(),
            fun: FunInterner::new(),
            class: ClassInterner::new(),
            module: ModuleInterner::new(),
            variable: VariableInterner::new(),
            tr: TraitInterner::new(),
            type_expr: TypeExprInterner::new(),
            imp: ImplBlockInterner::new(),
            def: DefInterner::new(),
            unresolved: UnresolvedInterner::new(),
        }
    }

    pub fn insert_symbol(&mut self, value: &String) -> Symbol {
        if let Some(res) = self.symbol.contains(value) {
            res
        } else {
            self.symbol.insert(value.clone())
        }
    }
    pub fn insert_string(&mut self, value: &StrLit) -> StringLiteral {
        if let Some(res) = self.string.contains(value) {
            res
        } else {
            self.string.insert(value.clone())
        }
    }

    pub fn insert_item(&mut self, value: NirItem) -> ItemId {
        self.item.insert(value)
    }
    pub fn insert_expr(&mut self, value: NirExpr) -> ExprId {
        self.expr.insert(value)
    }
    pub fn insert_scope(&mut self, value: Scope) -> ScopeId {
        self.scope.insert(value)
    }
    pub fn insert_fun(&mut self, value: TcFunProto) -> FunId {
        self.fun.insert(value)
    }
    pub fn insert_class(&mut self, value: Class) -> ClassId {
        self.class.insert(value)
    }
    pub fn insert_module(&mut self, value: Module) -> ModuleId {
        self.module.insert(value)
    }
    pub fn insert_variable(&mut self, value: VarDecl) -> VariableId {
        self.variable.insert(value)
    }
    pub fn insert_tr(&mut self, value: Trait) -> TraitId {
        self.tr.insert(value)
    }
    pub fn insert_type_expr(&mut self, value: TypeExpr) -> TypeExprId {
        self.type_expr.insert(value)
    }
    pub fn insert_imp(&mut self, value: ImplBlock) -> ImplBlockId {
        self.imp.insert(value)
    }
    pub fn insert_def(&mut self, value: Definition) -> DefId {
        self.def.insert(value)
    }
    pub fn insert_unresolved(&mut self, value: Unresolved) -> UnresolvedId {
        self.unresolved.insert(value)
    }

    pub fn get_symbol(&self, id: Symbol) -> &String {
        self.symbol.get(id)
    }
    pub fn get_string(&self, id: StringLiteral) -> &StrLit {
        self.string.get(id)
    }
    pub fn get_item(&self, id: ItemId) -> &NirItem {
        self.item.get(id)
    }
    pub fn get_expr(&self, id: ExprId) -> &NirExpr {
        self.expr.get(id)
    }
    pub fn get_scope(&self, id: ScopeId) -> &Scope {
        self.scope.get(id)
    }
    pub fn get_fun(&self, id: FunId) -> &TcFunProto {
        self.fun.get(id)
    }
    pub fn get_class(&self, id: ClassId) -> &Class {
        self.class.get(id)
    }
    pub fn get_module(&self, id: ModuleId) -> &Module {
        self.module.get(id)
    }
    pub fn get_variable(&self, id: VariableId) -> &VarDecl {
        self.variable.get(id)
    }
    pub fn get_tr(&self, id: TraitId) -> &Trait {
        self.tr.get(id)
    }
    pub fn get_type_expr(&self, id: TypeExprId) -> &TypeExpr {
        self.type_expr.get(id)
    }
    pub fn get_imp(&self, id: ImplBlockId) -> &ImplBlock {
        self.imp.get(id)
    }
    pub fn get_def(&self, id: DefId) -> &Definition {
        self.def.get(id)
    }
    pub fn get_unresolved(&self, id: UnresolvedId) -> &Unresolved {
        self.unresolved.get(id)
    }

    pub fn get_symbol_mut(&mut self, id: Symbol) -> &mut String {
        self.symbol.get_mut(id)
    }
    pub fn get_string_mut(&mut self, id: StringLiteral) -> &mut StrLit {
        self.string.get_mut(id)
    }
    pub fn get_item_mut(&mut self, id: ItemId) -> &mut NirItem {
        self.item.get_mut(id)
    }
    pub fn get_expr_mut(&mut self, id: ExprId) -> &mut NirExpr {
        self.expr.get_mut(id)
    }
    pub fn get_scope_mut(&mut self, id: ScopeId) -> &mut Scope {
        self.scope.get_mut(id)
    }
    pub fn get_fun_mut(&mut self, id: FunId) -> &mut TcFunProto {
        self.fun.get_mut(id)
    }
    pub fn get_class_mut(&mut self, id: ClassId) -> &mut Class {
        self.class.get_mut(id)
    }
    pub fn get_module_mut(&mut self, id: ModuleId) -> &mut Module {
        self.module.get_mut(id)
    }
    pub fn get_variable_mut(&mut self, id: VariableId) -> &mut VarDecl {
        self.variable.get_mut(id)
    }
    pub fn get_tr_mut(&mut self, id: TraitId) -> &mut Trait {
        self.tr.get_mut(id)
    }
    pub fn get_type_expr_mut(&mut self, id: TypeExprId) -> &mut TypeExpr {
        self.type_expr.get_mut(id)
    }
    pub fn get_imp_mut(&mut self, id: ImplBlockId) -> &mut ImplBlock {
        self.imp.get_mut(id)
    }
    pub fn get_def_mut(&mut self, id: DefId) -> &mut Definition {
        self.def.get_mut(id)
    }
    pub fn get_unresolved_mut(&mut self, id: UnresolvedId) -> &mut Unresolved {
        self.unresolved.get_mut(id)
    }

    pub fn contains_item(&self, value: &NirItem) -> Option<ItemId> {
        self.item.contains(value)
    }
    pub fn contains_expr(&self, value: &NirExpr) -> Option<ExprId> {
        self.expr.contains(value)
    }
    pub fn contains_scope(&self, value: &Scope) -> Option<ScopeId> {
        self.scope.contains(value)
    }
    pub fn contains_fun(&self, value: &TcFunProto) -> Option<FunId> {
        self.fun.contains(value)
    }
    pub fn contains_class(&self, value: &Class) -> Option<ClassId> {
        self.class.contains(value)
    }
    pub fn contains_module(&self, value: &Module) -> Option<ModuleId> {
        self.module.contains(value)
    }
    pub fn contains_variable(&self, value: &VarDecl) -> Option<VariableId> {
        self.variable.contains(value)
    }
    pub fn contains_tr(&self, value: &Trait) -> Option<TraitId> {
        self.tr.contains(value)
    }
    pub fn contains_type_expr(&self, value: &TypeExpr) -> Option<TypeExprId> {
        self.type_expr.contains(value)
    }
    pub fn contains_imp(&self, value: &ImplBlock) -> Option<ImplBlockId> {
        self.imp.contains(value)
    }
    pub fn contains_def(&self, value: &Definition) -> Option<DefId> {
        self.def.contains(value)
    }
    pub fn contains_urnesolved(&self, value: &Unresolved) -> Option<UnresolvedId> {
        self.unresolved.contains(value)
    }

    pub fn clear_symbol(&mut self) {
        self.symbol.clear();
    }
    pub fn clear_string(&mut self) {
        self.string.clear();
    }
    pub fn clear_item(&mut self) {
        self.item.clear();
    }
    pub fn clear_expr(&mut self) {
        self.expr.clear();
    }
    pub fn clear_scope(&mut self) {
        self.scope.clear();
    }
    pub fn clear_fun(&mut self) {
        self.fun.clear();
    }
    pub fn clear_class(&mut self) {
        self.class.clear();
    }
    pub fn clear_module(&mut self) {
        self.module.clear();
    }
    pub fn clear_variable(&mut self) {
        self.variable.clear();
    }
    pub fn clear_tr(&mut self) {
        self.tr.clear();
    }
    pub fn clear_type_expr(&mut self) {
        self.type_expr.clear();
    }
    pub fn clear_imp(&mut self) {
        self.imp.clear();
    }
    pub fn clear_def(&mut self) {
        self.def.clear();
    }
    pub fn clear_unresolved(&mut self) {
        self.unresolved.clear();
    }

    pub fn debug_print(&self) {
        println!("symbol: {} items", self.symbol.len());
        println!("string: {} items", self.string.len());
        println!("item: {} items", self.item.len());
        println!("expr: {} items", self.expr.len());
        println!("scope: {} items", self.scope.len());
        println!("fun: {} items", self.fun.len());
        println!("class: {} items", self.class.len());
        println!("module: {} items", self.module.len());
        println!("variable: {} items", self.variable.len());
        println!("tr: {} items", self.tr.len());
        println!("type_expr: {} items", self.type_expr.len());
        println!("imp: {} items", self.imp.len());
        println!("def: {} items", self.def.len());
        println!("unresolved: {} items", self.unresolved.len());
    }

    pub fn get_symbol_for(&self, value: &String) -> Symbol {
        self.symbol.contains(value).unwrap()
    }

    pub fn scope_interner(&self) -> &OneShotInterner<Scope> {
        &self.scope
    }
}

impl Default for GlobalInterner {
    fn default() -> Self {
        Self::new()
    }
}
