// All error types consolidated

use crate::{
    common::source_location::{FileManager, Span},
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

impl ParseError {
    pub fn to_string(&self, fm: &FileManager) -> String {
        match &self.kind.0 {
            ParseErrKind::ExpectedIden => format!("Expected identifier"),
            ParseErrKind::ExpectedArrow => format!("Expected '=>'"),
            ParseErrKind::UnexpectedEOF => format!("Unexpected end of input"),
            ParseErrKind::ExpectedIncludeDir => {
                format!("Expected include directive `@include <path::to::file>'")
            }
            ParseErrKind::NoIdenAfterLet => format!("Expected pattern after 'let' keyword"),
            ParseErrKind::ExpectedColonBeforeType => format!("Expected ':' before type"),
            ParseErrKind::BadTypeInLet => format!("Type is ill-formed in let declaration"),
            ParseErrKind::BadTypeInTemplate => format!("Type is ill-formed in template"),
            ParseErrKind::ExpectedValueInLet => {
                format!("Expected expression after '=>' in let declaration")
            }
            ParseErrKind::BadStartToken => format!("Unknown token in this context"),
            ParseErrKind::ExpectedIdentForType => {
                format!("Expected identifier at this point in type")
            }
            ParseErrKind::UnclosedTempArgs(location) => format!(
                "The template argument list was not properly closed (missing '>').\n'<' was declared here: {}",
                location.to_string(fm)
            ),
            ParseErrKind::ExpectedArrowInLet => format!("Expected '=>' in let declaration"),
            ParseErrKind::BadTopLevel => format!("Unrecognized top level definition"),
            ParseErrKind::ExpectedOpenParInFundef => {
                format!("Expected '(' in function declaration")
            }
            ParseErrKind::BadCharLiteral(_) => {
                format!("Unrecognized char literal. (Unilang only supports ASCII characters")
            }
            ParseErrKind::UnclosedParen(location) => format!(
                "The previous '(' was not properly closed (missing ')').\n'(' was declared here: {}",
                location.to_string(fm)
            ),
            ParseErrKind::UnsupportedDir(d) => format!("The directive '{d:}' does not exist"),
            ParseErrKind::BadTypeInDir => format!("The type in the directive is ill-formed"),
            ParseErrKind::BadExprInDir => format!("The expression in the directive is ill-formed"),
            ParseErrKind::BadPostfixStart => {
                format!("This does not look like a postfix expression")
            }
            ParseErrKind::BadArgInFuncall => format!("This funcall argument is ill-formed"),
            ParseErrKind::BadSubscript => todo!(),
            ParseErrKind::Todo => todo!(),
            ParseErrKind::ExpectedSemicol => todo!(),
            ParseErrKind::BadExprInPrefix => todo!(),
            ParseErrKind::UnclosedSqr(_) => todo!(),
            ParseErrKind::ExpectedTemplName => todo!(),
            ParseErrKind::ExpectedInterfaceName => todo!(),
            ParseErrKind::ExpectedArrowInClass => todo!(),
            ParseErrKind::ExpectedOpenBraInClass => todo!(),
            ParseErrKind::UnclosedBra(_) => todo!(),
            ParseErrKind::ExpectedClassName => todo!(),
            ParseErrKind::ExpectedArgName => todo!(),
            ParseErrKind::ExpectedAccessSpec => todo!(),
            ParseErrKind::ExpectedOpenBraInFundef => todo!(),
            ParseErrKind::ExpectedArrowInIf => todo!(),
            ParseErrKind::ExpectedInInFor => todo!(),
            ParseErrKind::ExpectedArrowInFor => todo!(),
            ParseErrKind::LexerError(_) => todo!(),
        }
    }
}
