#![allow(dead_code)]
#![allow(unused_variables)]

use std::fmt;

use crate::common::source_location::Span;

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    Identifier(String),
    IntLit(i32),
    CharLit(String),
    StrLit(String),
    Directive(String),

    // Keywords
    Let,
    If,
    Else,
    While,
    Return,
    Class,
    Defer,
    Impl,
    Module,
    Interface,
    For,
    In,
    Type,
    Break,
    Use,
    Static,

    // Operators
    Plus,
    Minus,
    Mult,
    Div,
    Modulo,
    Geq,
    Gt,
    Leq,
    Lt,
    Access,
    Eq,
    Diff,
    And,
    BitAnd,
    Or,
    BitOr,
    BitXor,
    Not,
    Deref,

    // Delimeters
    Colon,
    Semicolon,
    Comma,
    BigArrow,
    SmallArrow,
    OpenPar,
    ClosePar,
    OpenSqr,
    CloseSqr,
    OpenBra,
    CloseBra,
    DotDot,
    Dot,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Identifier(name) => write!(f, "{}", name),
            TokenKind::IntLit(value) => write!(f, "{}", value),
            TokenKind::CharLit(c) => write!(f, "{}", c),
            TokenKind::StrLit(s) => write!(f, "\"{}\"", s),
            TokenKind::Directive(d) => write!(f, "@{}", d),
            TokenKind::Let => write!(f, "let"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::While => write!(f, "while"),
            TokenKind::Return => write!(f, "return"),
            TokenKind::Class => write!(f, "class"),
            TokenKind::Defer => write!(f, "defer"),
            TokenKind::Impl => write!(f, "impl"),
            TokenKind::Module => write!(f, "module"),
            TokenKind::Interface => write!(f, "interface"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Mult => write!(f, "*"),
            TokenKind::Div => write!(f, "/"),
            TokenKind::Modulo => write!(f, "%"),
            TokenKind::Geq => write!(f, ">="),
            TokenKind::Gt => write!(f, ">"),
            TokenKind::Leq => write!(f, "<="),
            TokenKind::Lt => write!(f, "<"),
            TokenKind::Access => write!(f, "::"),
            TokenKind::Eq => write!(f, "=="),
            TokenKind::Diff => write!(f, "!="),
            TokenKind::And => write!(f, "&&"),
            TokenKind::BitAnd => write!(f, "&"),
            TokenKind::Or => write!(f, "||"),
            TokenKind::BitOr => write!(f, "|"),
            TokenKind::BitXor => write!(f, "^"),
            TokenKind::Not => write!(f, "!"),
            TokenKind::Deref => write!(f, "*"),
            TokenKind::Colon => write!(f, ":"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::BigArrow => write!(f, "=>"),
            TokenKind::SmallArrow => write!(f, "->"),
            TokenKind::OpenPar => write!(f, "("),
            TokenKind::ClosePar => write!(f, ")"),
            TokenKind::OpenSqr => write!(f, "["),
            TokenKind::CloseSqr => write!(f, "]"),
            TokenKind::OpenBra => write!(f, "{{"),
            TokenKind::CloseBra => write!(f, "}}"),
            TokenKind::Dot => write!(f, "."),
            TokenKind::DotDot => write!(f, ".."),
            TokenKind::For => write!(f, "for"),
            TokenKind::In => write!(f, "in"),
            TokenKind::Type => write!(f, "type"),
            TokenKind::Break => write!(f, "break"),
            TokenKind::Use => write!(f, "use"),
            TokenKind::Static => write!(f, "static"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub location: Span,
    pub kind: TokenKind,
}
