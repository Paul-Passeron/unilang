use super::Error;
use super::Token;
use super::TokenKind;
use crate::common::source_location::Span;
use regex::Regex;

macro_rules! get_simple_rule {
    ($regex: literal, $kind: expr) => {
        (
            Regex::new($regex).unwrap(),
            |_: &str, location: Span| -> Result<Token, Error> {
                Ok(super::Token {
                    location,
                    kind: $kind,
                })
            },
        )
    };
}

pub fn get_skip_rules() -> Vec<Regex> {
    vec![
        Regex::new(r"\n").unwrap(),
        Regex::new("[ \n\t\r]+").unwrap(),
        Regex::new(r"//[^\n]*").unwrap(),
        Regex::new(r"(?s)/\*.*?\*/").unwrap(),
    ]
}

pub fn get_token_rules() -> Vec<(Regex, fn(&str, Span) -> Result<Token, Error>)> {
    vec![
        get_simple_rule!("::", TokenKind::Access),
        get_simple_rule!(":", TokenKind::Colon),
        get_simple_rule!(",", TokenKind::Comma),
        get_simple_rule!("\\(", TokenKind::OpenPar),
        get_simple_rule!("\\)", TokenKind::ClosePar),
        get_simple_rule!("\\[", TokenKind::OpenSqr),
        get_simple_rule!("\\]", TokenKind::CloseSqr),
        get_simple_rule!("\\{", TokenKind::OpenBra),
        get_simple_rule!("\\}", TokenKind::CloseBra),
        get_simple_rule!("=>", TokenKind::BigArrow),
        get_simple_rule!("->", TokenKind::SmallArrow),
        get_simple_rule!("\\*", TokenKind::Mult),
        get_simple_rule!("/", TokenKind::Div),
        get_simple_rule!("\\+", TokenKind::Plus),
        get_simple_rule!("-", TokenKind::Minus),
        get_simple_rule!(";", TokenKind::Semicolon),
        get_simple_rule!("<=", TokenKind::Leq),
        get_simple_rule!(">=", TokenKind::Geq),
        get_simple_rule!(">", TokenKind::Gt),
        get_simple_rule!("<", TokenKind::Lt),
        get_simple_rule!("!=", TokenKind::Diff),
        get_simple_rule!("=", TokenKind::Eq),
        get_simple_rule!("%", TokenKind::Modulo),
        get_simple_rule!(r"\|\|", TokenKind::Or),
        get_simple_rule!(r"\|", TokenKind::BitOr),
        get_simple_rule!("\\^", TokenKind::BitXor),
        get_simple_rule!("&&", TokenKind::And),
        get_simple_rule!("&", TokenKind::BitAnd),
        get_simple_rule!("$", TokenKind::Deref),
        get_simple_rule!("\\.\\.", TokenKind::DotDot),
        get_simple_rule!("!", TokenKind::Not),
        (
            Regex::new("@[A-Za-z_][A-Za-z0-9_]*").unwrap(),
            |lexeme: &str, location: Span| {
                Ok(Token {
                    location,
                    kind: TokenKind::Directive(String::from(&lexeme[1..])),
                })
            },
        ),
        (
            Regex::new("[A-Za-z_][A-Za-z0-9_]*").unwrap(),
            |lexeme: &str, location: Span| {
                Ok(Token {
                    location,
                    kind: match lexeme {
                        "let" => TokenKind::Let,
                        "module" => TokenKind::Module,
                        "impl" => TokenKind::Impl,
                        "if" => TokenKind::If,
                        "else" => TokenKind::Else,
                        "type" => TokenKind::Type,
                        "while" => TokenKind::While,
                        "return" => TokenKind::Return,
                        "defer" => TokenKind::Defer,
                        "class" => TokenKind::Class,
                        "interface" => TokenKind::Interface,
                        "in" => TokenKind::In,
                        "for" => TokenKind::For,
                        "break" => TokenKind::Break,
                        "use" => TokenKind::Use,
                        "static" => TokenKind::Static,
                        "true" => TokenKind::True,
                        "false" => TokenKind::False,
                        _ => TokenKind::Identifier(String::from(lexeme)),
                    },
                })
            },
        ),
        (
            Regex::new(r#""(\\.|[^"\\])*""#).unwrap(),
            |lexeme: &str, location: Span| {
                let len = lexeme.len();
                Ok(Token {
                    location,
                    kind: TokenKind::StrLit(String::from(&lexeme[1..len - 1])),
                })
            },
        ),
        (
            Regex::new(r#"'(\\.|[^'\\])*'"#).unwrap(),
            |lexeme: &str, location: Span| {
                let len = lexeme.len();
                Ok(Token {
                    location,
                    kind: TokenKind::CharLit(String::from(&lexeme[1..len - 1])),
                })
            },
        ),
        (
            Regex::new("[0-9]+").unwrap(),
            |lexeme: &str, location: Span| {
                Ok(Token {
                    location,
                    kind: TokenKind::IntLit(i64::from_str_radix(lexeme, 10).unwrap() as i32),
                })
            },
        ),
    ]
}
