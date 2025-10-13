use std::{collections::HashSet, path::Path, process::Command, rc::Rc};

use inkwell::{
    OptimizationLevel,
    targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target},
};

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
    ty::{TyCtx, surface_resolution::SurfaceResolution, tir::TirCtx},
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

    pub fn compile(mut self) -> Result<(), CompilerError> {
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
                    return Err(CompilerError::ParseError(err));
                }
            };
            p.append(&mut prgm.0);
        }

        let prgm = Program(p);

        let nir = NirVisitor::new(&mut self, true).visit_program(&prgm);

        let nir = match nir {
            Ok(nir) => nir,
            Err(x) => return Err(CompilerError::NirError(x)),
        };

        let mut tc = TyCtx::new(&mut self);

        let resolved = match SurfaceResolution::new().run(&mut tc, &nir) {
            Ok(resolved) => resolved,
            Err(x) => return Err(CompilerError::TcError(x)),
        };
        let mut tir_ctx = TirCtx::new();
        if let Err(err) = tir_ctx.run(&mut tc, resolved) {
            return Err(CompilerError::TcError(err));
        }

        Target::initialize_native(&InitializationConfig::default()).unwrap();

        let ctx = inkwell::context::Context::create();

        let mut mono = MonoIRPass::new("main", &ctx, &mut tir_ctx);
        if let Err(err) = mono.run(&mut tc, ()) {
            return Err(CompilerError::TcError(err));
        }

        let target = Target::from_triple(&mono.triple).unwrap();

        let target_machine = target
            .create_target_machine(
                &mono.triple,
                "generic", // CPU
                "",        // Features
                OptimizationLevel::Default,
                RelocMode::Default,
                CodeModel::Default,
            )
            .expect("Failed to create target machine");

        let obj_file = format!("{}.o", self.config.output.display());

        // Write to object file
        target_machine
            .write_to_file(&mono.module, FileType::Object, Path::new(obj_file.as_str()))
            .unwrap();

        Command::new("gcc")
            .arg(obj_file.clone())
            .arg("-o")
            .arg(format!("{}", self.config.output.display()))
            .output()
            .unwrap();

        // let _ = std::fs::remove_file(Path::new(obj_file.as_str()));

        Ok(())
    }
}
