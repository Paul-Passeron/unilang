#![allow(dead_code)]
#![allow(unused_variables)]

use escape_string::escape;
use nonempty::NonEmpty;

// use super::parser::ParseResult;
use crate::{common::source_location::Span, lexer::TokenKind};

use std::{
    fmt::{self, Display, Formatter, FormattingOptions},
    rc::Rc,
};

const TAB_SPACE: &'static str = "    ";

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Literal {
    Int(i32),
    Char(char),
    String(String),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Ast<T> {
    data: Rc<T>,
    loc: Span,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum BinOp {
    Plus,
    Minus,
    Mult,
    Div,
    Mod,
    Eq,
    Neq,
    Gt,
    Geq,
    Lt,
    Leq,
    And,
    Or,
    BitOr,
    BitAnd,
    BitXor,
    Access,
    Range,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PostfixExprKind {
    Incr,
    Decr,
    Subscript(Ast<Expr>),
    Call(Vec<Ast<Expr>>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum PrefixExprKind {
    Incr,
    Decr,
    Address,
    Deref,
    Minus,
    Not,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Expr {
    Literal(Ast<Literal>),
    Identifier(Ast<String>),
    Tuple(Vec<Ast<Expr>>),
    BinOp {
        left: Ast<Expr>,
        op: BinOp,
        right: Ast<Expr>,
    },
    Prefix {
        expr: Ast<Expr>,
        op: PrefixExprKind,
    },
    Postfix {
        expr: Ast<Expr>,
        op: PostfixExprKind,
    },
    AsDir {
        ty: Ast<Ty>,
        expr: Ast<Expr>,
    },
    NewDir {
        ty: Ast<Ty>,
        expr: Ast<Expr>,
    },
    SizeDir(Ast<Ty>),
    StrDir(Ast<Ty>),
    TodoDir,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TypeName {
    pub path: NonEmpty<Ast<String>>,
}
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Ty {
    Named {
        name: Ast<TypeName>,
        templates: Vec<Ast<Ty>>,
    },
    Ptr(Ast<Ty>),
    Tuple(NonEmpty<Ast<Ty>>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LetDecl {
    pub lhs: Ast<Expr>,
    pub ty: Option<Ast<Ty>>,
    pub value: Option<Ast<Expr>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TemplateDecl {
    pub ty_name: Ast<String>,
    pub interface: Option<Ast<String>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FundefProto {
    pub name: Ast<String>,
    pub template_decls: Vec<Ast<TemplateDecl>>,
    pub args: Vec<(Ast<String>, Ast<Ty>)>,
    pub return_ty: Option<Ast<Ty>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum AccessSpec {
    Public,
    Private,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Class {
    pub name: Ast<String>,
    pub template_decls: Vec<Ast<TemplateDecl>>,
    pub methods: Vec<(Ast<AccessSpec>, Ast<Fundef>)>,
    pub members: Vec<(Ast<AccessSpec>, Ast<LetDecl>)>,
    pub type_aliases: Vec<(Ast<String>, Ast<Ty>)>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct TySpec {
    pub name: Ast<String>,
    pub implements: Option<Ast<String>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Interface {
    pub name: Ast<String>,
    pub constrained_ty: ConstrainedType,
    pub protos: Vec<Ast<FundefProto>>,
    pub ty_specs: Vec<Ast<TySpec>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ConstrainedType {
    pub ty: Ast<Ty>,
    pub constraint: Option<Ast<String>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Implementation {
    pub templates: Vec<Ast<TemplateDecl>>,
    pub trait_name: Ast<Ty>,
    pub for_type: Ast<Ty>,
    pub body: Vec<(Ast<AccessSpec>, Ast<TopLevel>)>,
    pub type_aliases: Vec<(Ast<String>, Ast<Ty>)>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Fundef {
    pub proto: Ast<FundefProto>,
    pub body: Vec<Ast<Stmt>>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TopLevel {
    LetDecl(Ast<LetDecl>),
    IncludeDir(Vec<Ast<String>>),
    ExternDir(Ast<FundefProto>, Ast<bool>),
    Fundef(Ast<Fundef>),
    Interface(Ast<Interface>),
    Class(Ast<Class>),
    Module(Ast<String>, Vec<Ast<TopLevel>>),
    NameAlias(Ast<String>, Ast<Ty>),
    Implementation(Ast<Implementation>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Stmt {
    Let(Ast<LetDecl>),

    Return(Option<Ast<Expr>>),

    ExprStmt(Ast<Expr>),

    If {
        cond: Ast<Expr>,
        then_branch: Ast<Stmt>,
        else_branch: Option<Ast<Stmt>>,
    },

    While {
        cond: Ast<Expr>,
        body: Ast<Stmt>,
    },

    Assign {
        lhs: Ast<Expr>,
        rhs: Ast<Expr>,
    },

    For {
        var: Ast<Expr>,
        iterator: Ast<Expr>,
        body: Ast<Stmt>,
    },

    Block(Vec<Ast<Stmt>>),

    Break,
}

pub struct Program(pub Vec<Ast<TopLevel>>);

impl BinOp {
    pub fn from_token(kind: &TokenKind) -> Option<Self> {
        match kind {
            TokenKind::Plus => Some(Self::Plus),
            TokenKind::Minus => Some(Self::Minus),
            TokenKind::Mult => Some(Self::Mult),
            TokenKind::Div => Some(Self::Div),
            TokenKind::Modulo => Some(Self::Mod),
            TokenKind::Geq => Some(Self::Geq),
            TokenKind::Gt => Some(Self::Gt),
            TokenKind::Leq => Some(Self::Leq),
            TokenKind::Lt => Some(Self::Lt),
            TokenKind::Access => Some(Self::Access),
            TokenKind::Eq => Some(Self::Eq),
            TokenKind::Diff => Some(Self::Neq),
            TokenKind::And => Some(Self::And),
            TokenKind::BitAnd => Some(Self::BitAnd),
            TokenKind::Or => Some(Self::Or),
            TokenKind::BitOr => Some(Self::BitOr),
            TokenKind::BitXor => Some(Self::BitXor),
            TokenKind::DotDot => Some(Self::Range),
            _ => None,
        }
    }
}

pub trait PrettyPrint {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result;
}

impl<T: PrettyPrint> Display for Ast<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_indent(f, 0)
    }
}

impl<T: PrettyPrint> PrettyPrint for Ast<T> {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        self.data.fmt_with_indent(f, indent_level)
    }
}

impl PrettyPrint for Literal {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        match self {
            Literal::Int(x) => write!(f, "{}", x),
            Literal::Char(c) => write!(f, "\'{}\'", escape(&c.to_string())),
            Literal::String(s) => write!(f, "\"{}\"", s),
        }
    }
}

impl PrettyPrint for BinOp {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        match self {
            BinOp::Plus => write!(f, "+"),
            BinOp::Minus => write!(f, "-"),
            BinOp::Mult => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "%"),
            BinOp::Eq => write!(f, "="),
            BinOp::Neq => write!(f, "!="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Geq => write!(f, ">="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Leq => write!(f, "<="),
            BinOp::And => write!(f, "&&"),
            BinOp::Or => write!(f, "||"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitXor => write!(f, "^"),
            BinOp::Access => write!(f, "::"),
            BinOp::Range => write!(f, ".."),
        }
    }
}

impl PrettyPrint for PostfixExprKind {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        match self {
            PostfixExprKind::Incr => write!(f, "++"),
            PostfixExprKind::Decr => write!(f, "--"),
            PostfixExprKind::Subscript(parse_result) => {
                write!(f, "[{}]", parse_result)
            }
            PostfixExprKind::Call(parse_results) => {
                let elems: Vec<String> = parse_results
                    .into_iter()
                    .map(|x| format!("{}", x))
                    .collect();
                write!(f, "({})", elems.join(", "))
            }
        }
    }
}

impl PrettyPrint for String {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        write!(f, "{}{}", TAB_SPACE.repeat(indent_level), self)
    }
}

impl PrettyPrint for Expr {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        match self {
            Expr::Literal(literal) => write!(f, "{}", literal),
            Expr::Identifier(s) => {
                write!(f, "{}", s)
            }
            Expr::Tuple(parse_results) => {
                let elems: Vec<String> = parse_results
                    .into_iter()
                    .map(|x| format!("{}", x))
                    .collect();
                write!(f, "({})", elems.join(", "))
            }
            Expr::BinOp { left, op, right } => {
                write!(f, "({} ", left)?;
                op.fmt_with_indent(f, 0)?;
                write!(f, " {})", right)
            }
            Expr::Prefix { expr, op } => {
                op.fmt_with_indent(f, 0)?;
                write!(f, " {}", expr)
            }
            Expr::Postfix { expr, op } => {
                write!(f, "{} ", expr)?;
                op.fmt_with_indent(f, 0)
            }
            Expr::AsDir { ty, expr } => {
                write!(f, "(@as {} {})", ty, expr)
            }
            Expr::NewDir { ty, expr } => write!(f, "@new {} {}", ty, expr),
            Expr::SizeDir(parse_result) => {
                write!(f, "@size {}", parse_result)
            }
            Expr::StrDir(ast) => todo!(),
            Expr::TodoDir => {
                write!(f, "@todo")
            }
        }
    }
}

impl PrettyPrint for TypeName {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, _indent_level: usize) -> fmt::Result {
        write!(
            f,
            "{}",
            self.path
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join("::")
        )
    }
}

impl PrettyPrint for Ty {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        match self {
            Ty::Named { name, templates } => {
                write!(f, "{}", name)?;
                if !templates.is_empty() {
                    write!(f, "<{}>", {
                        let elems: Vec<String> =
                            templates.iter().map(|x| format!("{}", x)).collect();
                        elems.join(", ")
                    })
                } else {
                    Ok(())
                }
            }
            Ty::Ptr(ty) => {
                ty.as_ref().fmt_with_indent(f, 0)?;
                write!(f, "*")
            }
            Ty::Tuple(non_empty) => {
                write!(f, "({})", {
                    let elems: Vec<String> = non_empty
                        .into_iter()
                        .map(|x| {
                            let mut buffer: String = String::new();
                            x.fmt_with_indent(
                                &mut fmt::Formatter::new(&mut buffer, FormattingOptions::new()),
                                0,
                            )
                            .unwrap();
                            buffer
                        })
                        .collect();
                    elems.join(", ")
                })
            }
        }
    }
}

impl<T> Ast<T> {
    pub fn new(data: T, loc: Span) -> Self {
        Self {
            data: Rc::new(data),
            loc,
        }
    }
    pub fn data(&self) -> &Rc<T> {
        &self.data
    }

    pub fn loc(&self) -> &Span {
        &self.loc
    }
}

impl PrettyPrint for PrefixExprKind {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        match self {
            PrefixExprKind::Incr => write!(f, "++"),
            PrefixExprKind::Decr => write!(f, "--"),
            PrefixExprKind::Address => write!(f, "&"),
            PrefixExprKind::Deref => write!(f, "*"),
            PrefixExprKind::Minus => write!(f, "-"),
            PrefixExprKind::Not => write!(f, "!"),
        }
    }
}

impl PrettyPrint for Stmt {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        write!(f, "{}", TAB_SPACE.repeat(indent_level))?;
        match self {
            Stmt::Break => write!(f, "break;"),
            Stmt::Let(parse_result) => write!(f, "let {};", parse_result),
            Stmt::Return(parse_result) => {
                let string = parse_result.as_ref().map_or_else(
                    || format!(""),
                    |x| {
                        let mut to_print: String = String::from(" ");
                        to_print.push_str(format!("{}", x).as_str());
                        to_print
                    },
                );
                write!(f, "return{};", string)
            }
            Stmt::ExprStmt(parse_result) => write!(f, "{};", parse_result),
            Stmt::If {
                cond,
                then_branch,
                else_branch,
            } => {
                write!(f, "if {} =>\n", cond)?;
                then_branch.fmt_with_indent(f, indent_level + 1)?;
                if let Some(e) = else_branch {
                    write!(f, "{}else", TAB_SPACE.repeat(indent_level))?;
                    e.clone().fmt_with_indent(f, indent_level + 1)?;
                }
                write!(f, "")
            }
            Stmt::While { cond, body } => {
                write!(f, "while {} =>\n", cond)?;
                body.clone().fmt_with_indent(f, indent_level + 1)
            }
            Stmt::Assign { lhs, rhs } => write!(f, "{} => {};", lhs, rhs),
            Stmt::Block(parse_results) => {
                write!(f, "{{\n")?;
                for res in parse_results.into_iter() {
                    res.clone().fmt_with_indent(f, indent_level + 1)?;
                    write!(f, "\n")?;
                }
                write!(f, "{}}}\n", TAB_SPACE.repeat(indent_level))
            }
            Stmt::For {
                var,
                iterator,
                body,
            } => todo!(),
        }
    }
}

impl PrettyPrint for LetDecl {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        write!(f, "{}", self.lhs)?;
        if let Some(ref t) = self.ty {
            write!(f, ": {}", t)?;
        }
        if let Some(ref e) = self.value {
            write!(f, " => {}", e)?;
        }
        write!(f, ";")
    }
}

impl PrettyPrint for FundefProto {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        let args = self
            .args
            .iter()
            .map(|(name, ty)| format!("{}: {}", name, ty))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{})", args)?;

        if let Some(ret_ty) = &self.return_ty {
            write!(f, " -> {}", ret_ty)?;
        }
        Ok(())
    }
}

impl PrettyPrint for Fundef {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        self.proto.fmt_with_indent(f, indent_level)?;
        write!(f, " => {{\n")?;
        for stmt in &self.body {
            stmt.fmt_with_indent(f, indent_level + 1)?;
            write!(f, "\n")?;
        }
        write!(f, "{}}}", TAB_SPACE.repeat(indent_level))
    }
}

impl PrettyPrint for TopLevel {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        match self {
            TopLevel::LetDecl(decl) => decl.clone().fmt_with_indent(f, indent_level),
            TopLevel::IncludeDir(paths) => {
                write!(f, "@include ")?;
                let paths_str = paths
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join("::");
                write!(f, "{}", paths_str)
            }
            TopLevel::Fundef(fundef) => fundef.data().as_ref().fmt_with_indent(f, indent_level),
            TopLevel::Interface(interface) => interface.fmt_with_indent(f, indent_level),
            TopLevel::Class(class) => class.clone().fmt_with_indent(f, indent_level),
            TopLevel::Module(name, parse_results) => {
                write!(f, "module ")?;
                name.fmt_with_indent(f, indent_level)?;
                writeln!(f, " {{")?;
                parse_results.iter().fold(Ok(()), |err, x| {
                    x.fmt_with_indent(f, indent_level + 1)?;
                    writeln!(f)
                })?;
                writeln!(f, "{}}}", TAB_SPACE.repeat(indent_level))
            }
            TopLevel::ExternDir(ast, is_var_arg) => todo!(),
            TopLevel::NameAlias(ast, ast1) => todo!(),
            TopLevel::Implementation(ast) => {
                let data = ast.as_ref();
                write!(
                    f,
                    "{}impl {}{} for {} => {{",
                    TAB_SPACE.repeat(indent_level),
                    if data.templates.len() == 0 {
                        String::new()
                    } else {
                        format!(
                            "<{}> ",
                            data.templates
                                .iter()
                                .map(|x| format!("{}", x))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    },
                    data.trait_name,
                    data.for_type
                )?;

                for (access, func) in &data.body {
                    write!(
                        f,
                        "\n{} {} ",
                        TAB_SPACE.repeat(indent_level + 1),
                        match access.as_ref() {
                            AccessSpec::Public => "public",
                            AccessSpec::Private => "private",
                        }
                    )?;

                    func.fmt_with_indent(f, indent_level + 1)?;
                }
                if !data.body.is_empty() {
                    write!(f, "\n{}", TAB_SPACE.repeat(indent_level))?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl PrettyPrint for ConstrainedType {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        for i in 1..indent_level {
            write!(f, " ")?;
        }
        write!(f, "{}", self.ty)?;
        if let Some(ref x) = self.constraint {
            write!(f, ": {}", x)?;
        }
        fmt::Result::Ok(())
    }
}

impl Display for ConstrainedType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.fmt_with_indent(f, 0)
    }
}

impl PrettyPrint for Interface {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        let txt = self.constrained_ty.to_string();
        write!(f, "interface {} {} => {{", self.name, txt)?;
        for proto in &self.protos {
            write!(f, "{}", TAB_SPACE.repeat(indent_level + 1))?;
            proto.fmt_with_indent(f, indent_level + 1)?;
            write!(f, ";\n")?;
        }
        write!(f, "{}}}", TAB_SPACE.repeat(indent_level))
    }
}

impl PrettyPrint for Class {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        write!(f, "class")?;
        if !self.template_decls.is_empty() {
            write!(
                f,
                "<{}>",
                self.template_decls
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        write!(f, " {} => {{\n", self.name)?;

        for (access, member) in &self.members {
            write!(
                f,
                "{}{} ",
                TAB_SPACE.repeat(indent_level + 1),
                match access.data().as_ref() {
                    AccessSpec::Public => "public",
                    AccessSpec::Private => "private",
                }
            )?;
            let mut s = String::new();
            let mut f2 = Formatter::new(&mut s, FormattingOptions::new());
            member.fmt_with_indent(&mut f2, indent_level + 1)?;
            s = s.trim().to_string();
            write!(f, "{}", s)?;
            write!(f, "\n")?;
        }

        for (access, method) in &self.methods {
            write!(
                f,
                "{}{} ",
                TAB_SPACE.repeat(indent_level + 1),
                match access.data().as_ref() {
                    AccessSpec::Public => "public",
                    AccessSpec::Private => "private",
                }
            )?;
            let mut s = String::new();
            let mut f2 = Formatter::new(&mut s, FormattingOptions::new());
            method.fmt_with_indent(&mut f2, indent_level + 1)?;
            s = s.trim().to_string();
            write!(f, "{}", s)?;
            write!(f, "\n")?;
        }

        write!(f, "{}}}", TAB_SPACE.repeat(indent_level))
    }
}

impl PrettyPrint for TemplateDecl {
    fn fmt_with_indent(&self, f: &mut fmt::Formatter<'_>, indent_level: usize) -> fmt::Result {
        write!(f, "{}", self.ty_name)?;
        if let Some(interface) = &self.interface {
            write!(f, ": {}", interface)?;
        }
        Ok(())
    }
}

impl<T> Ast<T> {
    pub fn as_ref(&self) -> &T {
        self.data().as_ref()
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for x in &self.0 {
            writeln!(f, "{}", x)?
        }
        fmt::Result::Ok(())
    }
}
