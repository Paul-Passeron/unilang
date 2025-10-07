use std::{collections::HashSet, process::exit, rc::Rc};

use crate::{
    common::{
        config::Config,
        errors::ParseError,
        source_location::{FileId, FileManager},
    },
    lexer::Lexer,
    nir::{
        global_interner::GlobalInterner, include_resolver::IncludeResolver, visitor::NirVisitor,
    },
    parser::{ast::Program, parser::Parser},
    ty::{TyCtx, pass::Pass, surface_resolution::SurfaceResolution, tir::TirCtx},
};
#[derive(Debug, Clone)]
pub struct GlobalContext {
    pub file_manager: FileManager,
    pub interner: GlobalInterner,
    pub config: Config,
    pub include_resolver: IncludeResolver,
}

impl GlobalContext {
    pub fn new(config: Config) -> Self {
        let std = config.std.clone();

        Self {
            interner: GlobalInterner::new(),
            file_manager: FileManager::new(),
            config,
            include_resolver: IncludeResolver::new(std),
        }
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
        let mut p = vec![];
        let mut ids = HashSet::new();

        for f in &self.config.files.clone() {
            let id = self.file_manager.add_file(f).unwrap();
            if ids.contains(&id) {
                continue;
            }
            ids.insert(id);
            let mut prgm = match self.parse_file(id) {
                Ok(x) => x,
                Err(err) => {
                    panic!(
                        "Parsing error ! {}",
                        err.span.start().to_string(&self.file_manager)
                    )
                }
            };
            p.append(&mut prgm.0);
        }

        let prgm = Program(p);

        let nir = NirVisitor::new(&mut self, true).visit_program(&prgm);

        let nir = match nir {
            Ok(nir) => nir,
            Err(x) => {
                println!("Err: {:#?}", x);
                exit(1)
            }
        };

        let mut tc = TyCtx::new(&mut self);

        let resolved = match SurfaceResolution::new().run(&mut tc, &nir) {
            Ok(resolved) => resolved,
            Err(err) => {
                tc.print_error(&err);
                panic!()
            }
        };

        let _tir = match TirCtx::new().run(&mut tc, resolved) {
            Ok(tir) => tir,
            Err(err) => {
                tc.print_error(&err);
                panic!()
            }
        };

        self.interner.debug_print();
        // println!("Successfully surface resolved!")
    }
}
