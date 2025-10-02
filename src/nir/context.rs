use std::{path::PathBuf, process::exit, rc::Rc};

use crate::{
    common::{
        config::Config,
        errors::ParseError,
        source_location::{FileId, FileManager},
    },
    lexer::Lexer,
    nir::{include_resolver::IncludeResolver, interner::GlobalInterner, visitor::NirVisitor},
    parser::{ast::Program, parser::Parser},
    ty::{TyCtx, pass::Pass, surface_resolution::SurfaceResolution},
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
        let std = config.std.as_ref().map_or_else(
            || {
                std::env::var("UL_STD_PATH")
                    .map_or(std::env::current_dir().unwrap(), |x| PathBuf::from(x))
            },
            |x| x.clone(),
        );

        Self {
            interner: GlobalInterner::new(),
            file_manager: FileManager::new(),
            config,
            include_resolver: IncludeResolver { std },
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

        let _resolved = match SurfaceResolution::new().run(&mut tc, &nir) {
            Ok(resolved) => resolved,
            Err(err) => {
                tc.print_error(&err);
                panic!()
            }
        };

        println!("Successfully surface resolved!")
    }
}
