// All error types consolidated

use std::path::PathBuf;

use crate::{
    common::source_location::Span,
    parser::parser::{ParseErrKind, ParseErrLevel},
};

#[derive(Clone, Debug)]
pub enum IncludeErrorKind {
    FileNotFound(PathBuf),
    ParserError(ParseErrKind),
    NoStdModule,
}

#[derive(Clone, Debug)]
pub enum CompilerError {
    IncludeError(IncludeError),
}

#[derive(Clone, Debug)]
pub struct CommonError<T> {
    pub kind: T,
    pub span: Span,
}

pub enum TypeErrorKind {
    NotAType {
        name: String,
    },
    UndefinedType(String),
    NotATemplatedType {
        name: String,
    },
    WrongTemplateArgsCount {
        expected_count: usize,
        type_name: String,
        found_count: u32,
    },
    ResolutionError {
        name: String,
    },
    CircularDependency {
        name: String,
    },
}

#[derive(Clone, Debug)]
pub enum AlreadyDefinedKind {
    Function,
    Interface,
    Type,
}

#[derive(Clone, Debug)]
pub enum CollectingErrorKind {
    UnsupportedFeature(String),
    UnresolvedInclude,
    AlreadyDefined(AlreadyDefinedKind, String, Span),
}

#[derive(Clone, Debug)]
pub enum SymbolErrorKind {}

#[derive(Clone, Debug)]
pub enum TemplateErrorKind {}

pub type TypeError = CommonError<TypeErrorKind>;
pub type TemplateError = CommonError<TemplateErrorKind>;
pub type IncludeError = CommonError<IncludeErrorKind>;
pub type ParseError = CommonError<(ParseErrKind, ParseErrLevel)>;
