use std::{collections::HashSet, process::exit, rc::Rc};

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
        let start = chrono::Local::now();
        let res = 100000.0;

        let mut p = vec![];
        let mut ids = HashSet::new();

        for f in &self.config.files.clone() {
            let id = self.file_manager.add_file(f).unwrap();
            if ids.contains(&id) {
                continue;
            }
            ids.insert(id);
            println!("{id:?}");
            let mut prgm = self.parse_file(id).unwrap();
            p.append(&mut prgm.0);
        }

        let prgm = Program(p);

        let parsing = chrono::Local::now().signed_duration_since(start);
        println!(
            "Finished parsing at {}",
            (parsing.as_seconds_f64() * res).round() / res
        );

        let nir = NirVisitor::new(&mut self, true).visit_program(&prgm);
        let nir_time = chrono::Local::now().signed_duration_since(start);
        println!(
            "Finished NIR at {} ({})s.",
            (nir_time.as_seconds_f64() * res).round() / res,
            ((nir_time.as_seconds_f64() - parsing.as_seconds_f64()) * res).round() / res
        );

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
        let tc_time = chrono::Local::now().signed_duration_since(start);
        println!(
            "Finished Surface Resolution at {} ({})s.",
            (tc_time.as_seconds_f64() * res).round() / res,
            ((tc_time.as_seconds_f64() - nir_time.as_seconds_f64()) * res).round() / res
        );

        self.interner.debug_print();
        // println!("Successfully surface resolved!")
    }
}
