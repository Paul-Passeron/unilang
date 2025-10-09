// All error types consolidated

use crate::{
    common::source_location::Span,
    nir::visitor::NirError,
    parser::parser::{ParseErrKind, ParseErrLevel},
    ty::TcError,
};

#[derive(Clone, Debug)]
pub struct CommonError<T> {
    pub kind: T,
    pub span: Span,
}

pub type ParseError = CommonError<(ParseErrKind, ParseErrLevel)>;

#[derive(Clone, Debug)]
pub enum CompilerError {
    ParseError(ParseError),
    NirError(NirError),
    TcError(TcError),
}
