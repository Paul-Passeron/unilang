use std::{path::PathBuf, process::exit, rc::Rc};

use crate::{
    common::{
        config::Config,
        errors::ParseError,
        source_location::{FileId, FileManager},
    },
    lexer::Lexer,
    nir::{
        include_resolver::IncludeResolver,
        interner::{Interner, StringInterner, StringLiteral, Symbol, SymbolInterner},
        nir::{ItemId, ItemInterner, NirItem, ScopeInterner, ScopeManager},
        visitor::NirVisitor,
    },
    parser::{ast::Program, parser::Parser},
    ty::TyCtx,
};

#[derive(Debug)]
pub struct GlobalInterner {
    pub symbol_interner: SymbolInterner,
    pub string_interner: StringInterner,
    pub item_interner: ItemInterner,
    pub scope_interner: ScopeInterner,
}

impl GlobalInterner {
    pub fn new() -> Self {
        Self {
            symbol_interner: SymbolInterner::new(),
            string_interner: StringInterner::new(),
            item_interner: ItemInterner::new(),
            scope_interner: ScopeInterner::new(),
        }
    }

    pub fn get_symbol<'ctx>(&'ctx self, id: Symbol) -> &'ctx String {
        self.symbol_interner.get(id)
    }

    pub fn get_string<'ctx>(&'ctx self, id: StringLiteral) -> &'ctx String {
        self.string_interner.get(id)
    }

    pub fn get_item<'ctx>(&'ctx self, id: ItemId) -> &'ctx NirItem {
        &self.item_interner.get(id)
    }

    pub fn get_mut_symbol<'ctx>(&'ctx mut self, id: Symbol) -> &'ctx mut String {
        self.symbol_interner.get_mut(id)
    }

    pub fn get_mut_string<'ctx>(&'ctx mut self, id: StringLiteral) -> &'ctx mut String {
        self.string_interner.get_mut(id)
    }

    pub fn get_mut_item<'ctx>(&'ctx mut self, id: ItemId) -> &'ctx mut NirItem {
        self.item_interner.get_mut(id)
    }

    pub fn insert_symbol<'ctx>(&'ctx mut self, val: &String) -> Symbol {
        if let Some(id) = self.symbol_interner.contains(val) {
            id
        } else {
            self.symbol_interner.insert(val.clone())
        }
    }

    pub fn get_symbol_for<'ctx>(&'ctx self, id: &str) -> Option<Symbol> {
        self.symbol_interner.contains(&id.to_string())
    }

    pub fn insert_string<'ctx>(&'ctx mut self, val: &String) -> StringLiteral {
        if let Some(id) = self.string_interner.contains(val) {
            id
        } else {
            self.string_interner.insert(val.clone())
        }
    }

    pub fn insert_item<'ctx>(&'ctx mut self, val: NirItem) -> ItemId {
        self.item_interner.insert(val)
    }

    pub fn scope_interner(&mut self) -> &mut ScopeInterner {
        &mut self.scope_interner
    }
}

#[derive(Debug)]
pub struct GlobalContext {
    pub file_manager: FileManager,
    pub interner: GlobalInterner,
    pub config: Config,
    pub include_resolver: IncludeResolver,
    pub scope_manager: ScopeManager,
}

impl GlobalContext {
    pub fn new(config: Config) -> Self {
        let std = config.std.as_ref().map_or_else(
            || {
                std::env::var("UL_STD_PATH")
                    .map_or(std::env::current_dir().unwrap(), |x| PathBuf::from(x))
            },
            |x| x.clone(),
        );

        let mut scope_manager = ScopeManager::new();

        let mut this = Self {
            interner: GlobalInterner::new(),
            file_manager: FileManager::new(),
            config,
            include_resolver: IncludeResolver { std },
            scope_manager: ScopeManager::new(),
        };

        scope_manager.init(&mut this.interner.scope_interner);

        this
    }

    pub fn parse_file(&mut self, file: FileId) -> Result<Program, ParseError> {
        Parser::new(Rc::from(
            &Lexer::new(&self.file_manager.files[&file])
                .into_iter()
                .collect::<Vec<_>>()[..],
        ))
        .parse_program()
    }

    pub fn compile(mut self) {
        let id = self.file_manager.add_file(&self.config.files).unwrap();
        let prgm = self.parse_file(id).unwrap();
        let nir = NirVisitor::new(&mut self, true).visit_program(&prgm);
        let nir = match nir {
            Ok(nir) => nir,
            Err(x) => {
                println!("Err: {:#?}", x);
                exit(1)
            }
        };

        let mut tc = TyCtx::new(&mut self);
        if let Err(_) = tc.visit_program(&nir, &mut self) {
            panic!();
        }
        todo!()
    }
}
