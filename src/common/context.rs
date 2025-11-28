use std::{collections::HashSet, path::Path, process::Command, rc::Rc};

use inkwell::targets::{FileType, InitializationConfig, Target};

use crate::{
    common::{
        config::Config,
        errors::{CompilerError, ParseError},
        global_interner::GlobalInterner,
        pass::Pass,
        source_location::{FileId, FileManager},
    },
    lexer::Lexer,
    mono_ir::mono_ir_pass::MonoIRPass,
    nir::{include_resolver::IncludeResolver, visitor::NirVisitor},
    parser::{ast::Program, parser::Parser},
    ty::{TcError, TyCtx, surface_resolution::SurfaceResolution, tir::TirCtx},
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
        Parser::new(
            Rc::from(
                &Lexer::new(&self.file_manager.files[&file])
                    .into_iter()
                    .collect::<Vec<_>>()[..],
            ),
            &self.file_manager,
        )
        .parse_program()
    }

    pub fn compile(mut self) -> Result<(), CompilerError> {
        let mut p = vec![];
        let mut ids = HashSet::new();

        let std_core = vec!["alloc.ul", "iter.ul", "range_iter.ul"];
        for p in std_core {
            let mut f = self.config.std.clone();
            f.push("std/");
            f.push(p);
            let id = self.file_manager.add_file(&f).unwrap();
            ids.insert(id);
        }

        for f in &self.config.files.clone() {
            let id = self.file_manager.add_file(f).unwrap();
            if ids.contains(&id) {
                continue;
            }
            ids.insert(id);
        }

        for id in ids {
            let mut prgm = match self.parse_file(id) {
                Ok(x) => x,
                Err(err) => {
                    return Err(CompilerError::ParseError(err));
                }
            };
            p.append(&mut prgm.0);
        }

        let prgm = Program(p);

        let nir = NirVisitor::new(&mut self, true).visit_program(&prgm);

        let nir = match nir {
            Ok(nir) => nir,
            Err(x) => {
                return Err(CompilerError::TcError(TcError::Text(format!(
                    "{}: {:?}",
                    x.span.start().to_string(&self.file_manager),
                    x.error
                ))));
            }
        };

        let mut tc = TyCtx::new(&mut self);

        let resolved = match SurfaceResolution::new().run(&mut tc, &nir) {
            Ok(resolved) => resolved,
            Err(x) => return Err(CompilerError::TcError(x)),
        };
        let mut tir_ctx = TirCtx::new(&mut tc);
        if let Err(err) = tir_ctx.run(&mut tc, resolved) {
            return Err(CompilerError::TcError(err));
        }

        Target::initialize_native(&InitializationConfig::default()).unwrap();

        let ctx = inkwell::context::Context::create();

        let mut mono = MonoIRPass::new("main", &ctx, &mut tir_ctx);
        if let Err(err) = mono.run(&mut tc, ()) {
            return Err(CompilerError::TcError(err));
        }

        let target_machine = mono.target_machine;

        let obj_file = format!("{}.o", self.config.output.display());

        // Write to object file
        target_machine
            .write_to_file(&mono.module, FileType::Object, Path::new(obj_file.as_str()))
            .unwrap();

        let gcc = Command::new("gcc")
            .arg(obj_file.clone())
            .arg("-o")
            .arg(format!("{}", self.config.output.display()))
            .output()
            .unwrap();

        let mut estr = String::new();
        for c in gcc.stderr {
            estr.push(char::from_u32(c as u32).unwrap());
        }

        eprintln!("{}", estr);
        let _ = std::fs::remove_file(Path::new(obj_file.as_str()));
        Ok(())
    }
}
