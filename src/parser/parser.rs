#![allow(dead_code)]
#![allow(unused_variables)]

use std::rc::Rc;

use nonempty::NonEmpty;
use rustc_literal_escaper::unescape_char;

use super::ast::{
    AccessSpec, Ast, BinOp, ClassAst, Expr, Fundef, FundefProto, Interface, LetDecl, Literal,
    PrefixExprKind, Program, Stmt, TopLevel, Ty,
};
use crate::{
    common::{
        errors::ParseError,
        source_location::{Location, Span},
    },
    lexer::{Token, TokenKind},
    parser::ast::{
        CMem, CMeth, ConstrainedType, Implementation, PostfixExprKind, TemplateDecl, TySpec,
        TypeName,
    },
};

#[derive(Clone, Debug)]
pub struct Parser {
    pub position: usize,
    pub tokens: Rc<[Token]>,
    pub last_location: Option<Location>,
}

#[derive(Clone, Debug)]
pub enum ParseErrLevel {
    Skip,
    Abort,
}

#[derive(Clone, Debug)]
pub enum ParseErrKind {
    ExpectedIden,
    ExpectedArrow,
    UnexpectedEOF,
    ExpectedIncludeDir,
    NoIdenAfterLet,
    ExpectedColonBeforeType,
    BadTypeInLet,
    BadTypeInTemplate,
    ExpectedValueInLet,
    BadStartToken,
    ExpectedIdentForType,
    UnclosedTempArgs(Location),
    ExpectedArrowInLet,
    BadTopLevel,
    ExpectedOpenParInFundef,
    BadCharLiteral(String),
    UnclosedParen(Location),
    UnsupportedDir(String),
    BadTypeInDir,
    BadExprInDir,
    BadPostfixStart,
    BadArgInFuncall,
    BadSubscript,
    Todo,
    ExpectedSemicol,
    BadExprInPrefix,
    UnclosedSqr(Location),
    ExpectedTemplName,
    ExpectedInterfaceName,
    ExpectedArrowInClass,
    ExpectedOpenBraInClass,
    UnclosedBra(Location),
    ExpectedClassName,
    ExpectedArgName,
    ExpectedAccessSpec,
    ExpectedOpenBraInFundef,
    ExpectedArrowInIf,
    ExpectedInInFor,
    ExpectedArrowInFor,
    LexerError(String),
}

fn get_prefix_precedence(op: &PrefixExprKind) -> u8 {
    14
}

fn get_precedence(op: &BinOp) -> u8 {
    match op {
        BinOp::Access => 15,
        BinOp::Range => 13,
        BinOp::Mult | BinOp::Div | BinOp::Mod => 12,
        BinOp::Plus | BinOp::Minus => 11,
        BinOp::Gt | BinOp::Lt | BinOp::Geq | BinOp::Leq => 8,
        BinOp::Eq | BinOp::Neq => 7,
        BinOp::BitAnd => 6,
        BinOp::BitXor => 5,
        BinOp::BitOr => 4,
        BinOp::And => 3,
        BinOp::Or => 2,
    }
}

fn get_postfix_precedence(op: &TokenKind) -> u8 {
    match op {
        TokenKind::OpenSqr | TokenKind::OpenPar => 14,
        _ => todo!(),
    }
}
impl Parser {
    pub fn new(vec: Rc<[Token]>) -> Self {
        Self {
            position: 0,
            tokens: vec,
            last_location: None,
        }
    }

    fn next(&mut self) -> Option<Token> {
        if self.position >= self.tokens.len() {
            None
        } else {
            let res = &self.tokens[self.position];
            self.position += 1;
            let loc = res.location.end();
            self.last_location = Some(loc);
            Some(res.clone())
        }
    }

    fn peek(&self) -> Option<Token> {
        self.clone().next()
    }

    fn peek_n(&self, i: usize) -> Option<Token> {
        let mut x = self.clone();
        x.next();
        x.next()
    }

    fn match_tokenkind(&self, k: TokenKind) -> bool {
        if self.position >= self.tokens.len() {
            return false;
        }
        matches!(self.peek().unwrap().kind, kind if k == kind)
    }

    fn parse_identifier_as_string(&mut self) -> Result<Ast<String>, ParseError> {
        if self.tokens.len() <= self.position {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }
        self.peek()
            .map(|tok| {
                if let TokenKind::Identifier(ref s) = tok.kind {
                    self.next();
                    Ok(Ast::new(s.clone(), tok.location))
                } else {
                    self.emit_error(ParseErrKind::ExpectedIden)
                }
            })
            .unwrap()
    }

    fn parse_assign(&mut self) -> Result<Ast<Stmt>, ParseError> {
        if self.is_done() {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }
        let lhs = self.parse_expr()?;
        let start = lhs.loc().start();
        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        self.next();
        let rhs = self.parse_expr()?;
        let end = rhs.loc().end();
        let ass = Stmt::Assign { lhs, rhs };
        if !self.match_tokenkind(TokenKind::Semicolon) {
            return self.emit_error(ParseErrKind::ExpectedSemicol);
        }
        self.next();
        Ok(Ast::new(ass, start.span_to(&end)))
    }

    fn parse_if(&mut self) -> Result<Ast<Stmt>, ParseError> {
        if !self.match_tokenkind(TokenKind::If) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let loc = self.next().unwrap().location.start();
        let condition = self.parse_expr()?;

        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_error(ParseErrKind::ExpectedArrowInIf);
        }
        self.next();

        let stmt = self.parse_stmt()?;
        let mut end = stmt.loc().end();

        let mut else_stmt = None;
        if self.match_tokenkind(TokenKind::Else) {
            self.next();
            let s = self.parse_stmt()?;
            end = s.loc().end();
            else_stmt = Some(s);
        }

        let span = loc.span_to(&end);

        Ok(Ast::new(
            Stmt::If {
                cond: condition,
                then_branch: stmt,
                else_branch: else_stmt,
            },
            span,
        ))
    }

    fn parse_compound(&mut self) -> Result<Ast<Stmt>, ParseError> {
        if !self.match_tokenkind(TokenKind::OpenBra) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let start = self.next().unwrap().location.start();
        let mut stmts = Vec::new();

        while !self.match_tokenkind(TokenKind::CloseBra) {
            let stmt = self.parse_stmt()?;
            stmts.push(stmt);
        }
        if !self.match_tokenkind(TokenKind::CloseBra) {
            return self.emit_error(ParseErrKind::UnclosedBra(start));
        }
        let end = self.next().unwrap().location.end();

        Ok(Ast::new(Stmt::Block(stmts), start.span_to(&end)))
    }

    fn parse_while(&mut self) -> Result<Ast<Stmt>, ParseError> {
        if !self.match_tokenkind(TokenKind::While) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let start = self.next().unwrap().location.start();
        let cond = self.parse_expr()?;

        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_error(ParseErrKind::ExpectedArrow);
        }
        self.next();
        let body = self.parse_stmt()?;

        let end = body.loc().end();

        Ok(Ast::new(Stmt::While { cond, body }, start.span_to(&end)))
    }

    pub fn parse_break_stmt(&mut self) -> Result<Ast<Stmt>, ParseError> {
        if !self.match_tokenkind(TokenKind::Break) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let start = self.next().unwrap().location.start();
        if !self.match_tokenkind(TokenKind::Semicolon) {
            return self.emit_abort(ParseErrKind::ExpectedSemicol);
        }
        let end = self.next().unwrap().location.end();
        return Ok(Ast::new(Stmt::Break, start.span_to(&end)));
    }

    fn parse_stmt(&mut self) -> Result<Ast<Stmt>, ParseError> {
        self.try_parse_any(vec![
            Self::parse_compound,
            Self::parse_let_stmt,
            Self::parse_return_stmt,
            Self::parse_defer_stmt,
            Self::parse_break_stmt,
            Self::parse_assign,
            Self::parse_if,
            Self::parse_while,
            Self::parse_for_stmt,
            Self::parse_expr_stmt,
        ])
    }

    fn parse_for_stmt(&mut self) -> Result<Ast<Stmt>, ParseError> {
        if !self.match_tokenkind(TokenKind::For) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }

        let start = self.next().unwrap().location.start();

        // Because in the future, we'll have tuples and other deconstructed types
        let var = self.parse_expr()?;

        if !self.match_tokenkind(TokenKind::In) {
            return self.emit_abort(ParseErrKind::ExpectedInInFor);
        }

        self.next();

        let iterator = self.parse_expr()?;

        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_abort(ParseErrKind::ExpectedArrowInFor);
        }

        self.next();

        let body = self.parse_stmt()?;

        let end = body.loc().end();

        Ok(Ast::new(
            Stmt::For {
                var,
                iterator,
                body,
            },
            start.span_to(&end),
        ))
    }

    fn parse_expr_stmt(&mut self) -> Result<Ast<Stmt>, ParseError> {
        let expr = self.parse_expr()?;
        if !self.match_tokenkind(TokenKind::Semicolon) {
            return self.emit_abort(ParseErrKind::ExpectedSemicol);
        }
        let end = self.next().unwrap().location.end();
        let span = expr.loc().start().span_to(&end);
        Ok(Ast::new(Stmt::ExprStmt(expr), span))
    }

    fn parse_include_path(&mut self) -> Result<Vec<Ast<String>>, ParseError> {
        let mut res = Vec::new();
        if self.tokens.len() <= self.position {
            return self.emit_error(ParseErrKind::ExpectedIncludeDir);
        }
        loop {
            let iden = self.parse_identifier_as_string()?;
            res.push(iden);
            if self.tokens.len() <= self.position {
                break;
            }
            if !matches!(self.peek().unwrap().kind, TokenKind::Access) {
                break;
            }
            self.next();
        }
        Ok(res)
    }

    pub fn parse_include_dir(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        if self.tokens.len() <= self.position {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }
        let tok = self.peek().unwrap();
        let start = tok.location.start();
        match tok.kind {
            TokenKind::Directive(ref s) => {
                if s.as_str() == "include" {
                    self.next();
                    let v = self.parse_include_path()?;
                    let span = start.span_to(&v.last().unwrap().loc().end());
                    Ok(Ast::new(TopLevel::IncludeDir(v), span))
                } else {
                    self.next();
                    self.emit_error(ParseErrKind::UnsupportedDir(s.to_owned()))
                }
            }
            _ => self.emit_error(ParseErrKind::ExpectedIncludeDir),
        }
    }

    pub fn parse_type_expr(&mut self) -> Result<Ast<TypeName>, ParseError> {
        // not ideal
        let original = self.position;
        let mut ne = NonEmpty::new({
            if let Some(tok) = self.peek()
                && let TokenKind::Identifier(symb) = tok.kind
            {
                let iden = self.parse_identifier_as_string()?;
                iden
            } else {
                panic!("{:?}", self.peek())
            }
        });
        while self.match_tokenkind(TokenKind::Access) {
            self.next();
            let next = if let Some(tok) = self.peek()
                && let TokenKind::Identifier(symb) = tok.kind
            {
                self.parse_identifier_as_string()?
            } else {
                return self.emit_abort(ParseErrKind::ExpectedIden);
            };
            let span = ne.last().loc().start().span_to(&next.loc().end());
            ne.push(next);
        }
        let span = ne.first().loc().start().span_to(&ne.last().loc().end());
        Ok(Ast::new(TypeName { path: ne }, span))
    }

    pub fn parse_base_type(&mut self) -> Result<Ast<Ty>, ParseError> {
        // Juste name < templated args>
        let original = self.position;
        if self.match_tokenkind(TokenKind::OpenPar) {
            let mut tys = Vec::new();
            let start = self.next().unwrap().location.start();
            while !self.match_tokenkind(TokenKind::ClosePar) {
                tys.push(self.parse_type()?);
                if !self.match_tokenkind(TokenKind::Comma) {
                    break;
                }
                self.next();
            }
            if !self.match_tokenkind(TokenKind::ClosePar) {
                return self.emit_abort(ParseErrKind::UnclosedParen(start));
            }
            let end = self.next().unwrap().location.end();

            return Ok(Ast::new(
                Ty::Tuple(NonEmpty::from_vec(tys).unwrap()),
                start.span_to(&end),
            ));
        } else {
            let name = self.parse_type_expr()?;
            let start = name.loc().start();
            let mut end = name.loc().end();
            if self.tokens.len() <= self.position {
                return self.emit_error(ParseErrKind::UnexpectedEOF);
            }
            let mut temps = Vec::new();
            if self.match_tokenkind(TokenKind::Lt) {
                let first = self.next().unwrap();
                loop {
                    if self.tokens.len() <= self.position {
                        return self.emit_error(ParseErrKind::UnexpectedEOF);
                    }
                    if matches!(self.peek().unwrap().kind, TokenKind::Gt) {
                        break;
                    }
                    let ty = self.parse_type()?;
                    temps.push(ty);
                    if !self.match_tokenkind(TokenKind::Comma) {
                        break;
                    }
                    self.next();
                }
                if !self.match_tokenkind(TokenKind::Gt) {
                    return self.emit_error(ParseErrKind::UnclosedTempArgs(first.location.start()));
                }
                end = self.next().unwrap().location.end();
            }
            let span = start.span_to(&end);

            Ok(Ast::new(
                Ty::Named {
                    name: name,
                    templates: temps,
                },
                span,
            ))
        }
    }

    pub fn parse_type(&mut self) -> Result<Ast<Ty>, ParseError> {
        let mut ty = self.parse_base_type()?;
        let start = ty.loc().start();
        while matches!(
            self.peek().map(|x| x.kind).unwrap_or(TokenKind::Plus),
            TokenKind::Mult
        ) {
            let end = self.next().unwrap().location.end();
            ty = Ast::new(Ty::Ptr(ty), start.span_to(&end));
        }
        Ok(ty)
    }

    pub fn emit_error_only(&self, kind: ParseErrKind) -> ParseError {
        let span = if self.is_done() {
            let l = self.last_location.unwrap();
            l.span_to(&l)
        } else {
            self.peek().unwrap().location
        };
        ParseError {
            kind: (kind, ParseErrLevel::Skip),
            span,
        }
    }

    pub fn emit_error_only_at(&self, kind: ParseErrKind, span: Span) -> ParseError {
        let mut res = self.emit_error_only(kind);
        res.span = span;
        res
    }

    pub fn emit_abort_only(&self, kind: ParseErrKind) -> ParseError {
        let mut res = self.emit_error_only(kind);
        res.kind.1 = ParseErrLevel::Abort;
        res
    }
    pub fn emit_abort_only_at(&self, kind: ParseErrKind, span: Span) -> ParseError {
        let mut res = self.emit_error_only_at(kind, span);
        res.kind.1 = ParseErrLevel::Abort;
        res
    }

    pub fn emit_error<T>(&self, kind: ParseErrKind) -> Result<T, ParseError> {
        Err(self.emit_error_only(kind))
    }

    pub fn emit_error_at<T>(&self, kind: ParseErrKind, span: Span) -> Result<T, ParseError> {
        Err(self.emit_error_only_at(kind, span))
    }

    pub fn emit_abort<T>(&self, kind: ParseErrKind) -> Result<T, ParseError> {
        Err(self.emit_abort_only(kind))
    }

    pub fn emit_abort_at<T>(&self, kind: ParseErrKind, loc: Span) -> Result<T, ParseError> {
        Err(self.emit_abort_only_at(kind, loc))
    }

    fn parse_binop_rhs(
        &mut self,
        min_prec: u8,
        mut left: Ast<Expr>,
    ) -> Result<Ast<Expr>, ParseError> {
        let start = left.loc().start();
        loop {
            // First handle postfix operators with higher precedence than min_prec
            while !self.is_done() {
                if let Some(tok) = self.peek() {
                    if matches!(tok.kind, TokenKind::OpenPar | TokenKind::OpenSqr) {
                        let postfix_prec = get_postfix_precedence(&tok.kind);
                        if postfix_prec >= min_prec {
                            left = self.parse_postfix(left)?;
                            continue;
                        }
                    }
                }
                break;
            }

            // Then handle binary operators
            if self.is_done() {
                break;
            }

            let tok = self.peek().unwrap();
            let op_opt = BinOp::from_token(&tok.kind);
            if op_opt.is_none() {
                break;
            }
            let op = op_opt.unwrap();
            let prec = get_precedence(&op);
            if prec < min_prec {
                break;
            }

            self.next();

            let mut right = self.parse_primary()?;

            // Handle right-associative operators and postfix on right operand
            right = self.parse_binop_rhs(prec + 1, right)?;
            let span = start.span_to(&right.loc().end());
            left = Ast::new(
                Expr::BinOp {
                    left: left.clone(),
                    op,
                    right,
                },
                span,
            );
        }

        Ok(left)
    }

    pub fn parse_expr(&mut self) -> Result<Ast<Expr>, ParseError> {
        let primary_expr = self.parse_primary()?;
        self.parse_binop_rhs(0, primary_expr)
    }

    pub fn parse_letless_var(&mut self, l: Location) -> Result<Ast<LetDecl>, ParseError> {
        let original = self.position;
        let matched = self.parse_expr()?;
        let mut t = None;
        let mut end = matched.loc().end();
        if self.match_tokenkind(TokenKind::Colon) {
            self.next();
            let ty = self.parse_type()?;
            end = ty.loc().end();
            t = Some(ty);
        }

        let mut value = None;
        if !self.match_tokenkind(TokenKind::Semicolon) {
            if !self.match_tokenkind(TokenKind::BigArrow) {
                return self.emit_error(ParseErrKind::ExpectedArrowInLet);
            }
            self.next();
            let e = self.parse_expr()?;
            end = e.loc().end();
            value = Some(e);
        }
        Ok(Ast::new(
            LetDecl {
                lhs: matched,
                ty: t,
                value,
            },
            l.span_to(&end),
        ))
    }

    pub fn is_done(&self) -> bool {
        self.tokens.is_empty() || self.position >= self.tokens.len()
    }

    pub fn parse_let_decl(&mut self) -> Result<Ast<LetDecl>, ParseError> {
        if self.is_done() {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }
        if !self.match_tokenkind(TokenKind::Let) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let t = self.next().unwrap();
        let res = self.parse_letless_var(t.location.start());
        if !self.match_tokenkind(TokenKind::Semicolon) {
            return self.emit_error(ParseErrKind::ExpectedSemicol);
        }
        self.next();
        res
    }

    pub fn parse_template_arg(&mut self) -> Result<Ast<TemplateDecl>, ParseError> {
        let t_name = self.parse_identifier_as_string();
        if t_name.is_err() {
            return self.emit_error(ParseErrKind::ExpectedTemplName);
        }
        let t_name = t_name.unwrap();
        let start = t_name.loc().start();
        let mut end = t_name.loc().end();
        let mut templated = None;
        if self.match_tokenkind(TokenKind::Impl) {
            self.next();
            let interface = self.parse_type_expr();
            if interface.is_err() {
                return self.emit_error(ParseErrKind::ExpectedInterfaceName);
            }
            let interface = interface.unwrap();
            end = interface.loc().end();
            templated = Some(interface);
        }
        Ok(Ast::new(
            TemplateDecl {
                ty_name: t_name,
                interface: templated,
            },
            start.span_to(&end),
        ))
    }

    pub fn parse_fundef_proto_gen(
        &mut self,
        have_ret_type: bool,
    ) -> Result<Ast<FundefProto>, ParseError> {
        if self.is_done() {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }

        let mut template_decls = Vec::new();
        let mut args = Vec::new();
        let first = self.peek().unwrap();
        let start = first.location.start();
        if self.match_tokenkind(TokenKind::Lt) {
            let first = self.next().unwrap();

            while !self.match_tokenkind(TokenKind::Gt) {
                if self.is_done() {
                    break;
                }
                let templ = self.parse_template_arg()?;
                template_decls.push(templ);
                if !self.match_tokenkind(TokenKind::Comma) {
                    break;
                }
                self.next();
            }
            if !self.match_tokenkind(TokenKind::Gt) {
                return self.emit_error(ParseErrKind::UnclosedTempArgs(first.location.start()));
            }
            self.next();
        }
        let name = self.parse_identifier_as_string()?;

        if !self.match_tokenkind(TokenKind::OpenPar) {
            return self.emit_error(ParseErrKind::ExpectedOpenParInFundef);
        }
        let par = self.next().unwrap();
        while !self.match_tokenkind(TokenKind::ClosePar) {
            if self.is_done() {
                break;
            }
            let e = self.parse_identifier_as_string()?;

            if !self.match_tokenkind(TokenKind::Colon) {
                return self.emit_error(ParseErrKind::ExpectedColonBeforeType);
            }
            self.next();
            let ty = self.parse_type()?;

            args.push((e, ty));
            if !self.match_tokenkind(TokenKind::Comma) {
                break;
            }
            self.next();
        }
        if !self.match_tokenkind(TokenKind::ClosePar) {
            return self.emit_error(ParseErrKind::UnclosedParen(par.location.start()));
        }
        let mut end = self.next().unwrap().location.end();
        let mut ty = None;
        if have_ret_type {
            if !self.match_tokenkind(TokenKind::Colon) {
                return self.emit_error(ParseErrKind::ExpectedColonBeforeType);
            }
            self.next();
            let t = self.parse_type()?;
            end = t.loc().end();
            ty = Some(t);
        }
        Ok(Ast::new(
            FundefProto {
                name,
                template_decls,
                args,
                return_ty: ty,
            },
            start.span_to(&end),
        ))
    }

    pub fn parse_fundef_proto(&mut self) -> Result<Ast<FundefProto>, ParseError> {
        self.parse_fundef_proto_gen(true)
    }

    pub fn parse_fundef(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        if !self.match_tokenkind(TokenKind::Let) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let first = self.next().unwrap();
        let start = first.location.start();

        let proto = self.parse_fundef_proto()?;

        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_error(ParseErrKind::Todo);
        }
        self.next();

        if !self.match_tokenkind(TokenKind::OpenBra) {
            return self.emit_error(ParseErrKind::Todo);
        }
        let bra = self.next().unwrap().location;
        let mut stmts = Vec::new();

        while !self.match_tokenkind(TokenKind::CloseBra) {
            let stmt = self.parse_stmt();
            if stmt.is_err() {
                let mut err = stmt.err().unwrap();
                err.kind.1 = ParseErrLevel::Abort;
                return Err(err);
            }
            stmts.push(stmt?);
        }
        if !self.match_tokenkind(TokenKind::CloseBra) {
            return self.emit_error(ParseErrKind::UnclosedBra(bra.start()));
        }
        let end = self.next().unwrap().location.end();
        let span = start.span_to(&end);
        Ok(Ast::new(
            TopLevel::Fundef(Ast::new(
                Fundef {
                    proto: proto,
                    body: stmts,
                },
                span.clone(),
            )),
            span,
        ))
    }

    pub fn parse_name_alias(
        &mut self,
    ) -> Result<((Option<Ast<String>>, Ast<Ty>), Span), ParseError> {
        if !self.match_tokenkind(TokenKind::Use) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }

        let start = self.next().unwrap().location.start();

        let name = if let Some(arr) = self.peek_n(2)
            && matches!(arr.kind, TokenKind::BigArrow)
        {
            let name = self.parse_identifier_as_string()?;

            if !self.match_tokenkind(TokenKind::BigArrow) {
                return self.emit_abort(ParseErrKind::ExpectedArrow);
            }

            self.next();
            Some(name)
        } else {
            None
        };
        let ty = self.parse_type()?;

        if !self.match_tokenkind(TokenKind::Semicolon) {
            return self.emit_abort(ParseErrKind::ExpectedSemicol);
        }

        let end = self.next().unwrap().location.end();

        Ok(((name, ty), start.span_to(&end)))
    }

    pub fn parse_type_alias(&mut self) -> Result<((Ast<String>, Ast<Ty>), Span), ParseError> {
        if !self.match_tokenkind(TokenKind::Type) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }

        let start = self.next().unwrap().location.start();
        let name = self.parse_identifier_as_string()?;

        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_abort(ParseErrKind::ExpectedArrow);
        }

        self.next();

        let ty = self.parse_type()?;

        if !self.match_tokenkind(TokenKind::Semicolon) {
            return self.emit_abort(ParseErrKind::ExpectedSemicol);
        }

        let end = self.next().unwrap().location.end();

        Ok(((name, ty), start.span_to(&end)))
    }

    pub fn parse_interface(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        if !self.match_tokenkind(TokenKind::Interface) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let start = self.next().unwrap().location.start();

        let name = self.parse_identifier_as_string()?;

        if self.is_done() {
            return self.emit_abort(ParseErrKind::UnexpectedEOF);
        }
        let ty = self.parse_type_expr()?;

        let constraint = if self.peek().unwrap().kind == TokenKind::Colon {
            self.next();
            Some(self.parse_identifier_as_string()?)
        } else {
            None
        };

        self.next();

        if !self.match_tokenkind(TokenKind::OpenBra) {
            return self.emit_abort(ParseErrKind::Todo);
        }

        let bra = self.next().unwrap().location;

        let mut protos = Vec::new();

        let mut ty_specs = Vec::new();

        loop {
            if self.match_tokenkind(TokenKind::CloseBra) {
                break;
            }
            if self.is_done() {
                return self.emit_abort(ParseErrKind::UnexpectedEOF);
            }

            if self.match_tokenkind(TokenKind::Type) {
                let start = self.next().unwrap().location.start();
                let name = self.parse_identifier_as_string()?;
                let implements = if self.match_tokenkind(TokenKind::Impl) {
                    self.next();
                    let interface_name = self.parse_type_expr()?;
                    Some(interface_name)
                } else {
                    None
                };

                let ty_spec = TySpec {
                    name,
                    implements: implements,
                };

                if !self.match_tokenkind(TokenKind::Semicolon) {
                    return self.emit_abort(ParseErrKind::ExpectedSemicol);
                }

                let end = self.next().unwrap().location.end();
                let span = start.span_to(&end);
                ty_specs.push(Ast::new(ty_spec, span));
            } else {
                let is_static = if self.match_tokenkind(TokenKind::Static) {
                    self.next();
                    true
                } else {
                    false
                };

                let proto = self.parse_fundef_proto()?;
                if self.is_done() {
                    return self.emit_abort(ParseErrKind::UnexpectedEOF);
                }
                if !self.match_tokenkind(TokenKind::Semicolon) {
                    return self.emit_abort(ParseErrKind::ExpectedSemicol);
                }
                self.next();
                protos.push((is_static, proto));
            }
        }

        if !self.match_tokenkind(TokenKind::CloseBra) {
            return self.emit_abort(ParseErrKind::UnclosedBra(bra.start()));
        }

        let end = self.next().unwrap().location.end();
        let span = ty.loc().clone();
        let constrained_ty = ConstrainedType {
            ty: Ast::new(
                Ty::Named {
                    name: ty,
                    templates: vec![],
                },
                span,
            ),
            constraint,
        };

        let interface = Ast::new(
            Interface {
                name,
                constrained_ty,
                protos,
                ty_specs,
            },
            start.span_to(&end),
        );

        Ok(Ast::new(
            TopLevel::Interface(interface),
            start.span_to(&end),
        ))
    }

    fn parse_primary(&mut self) -> Result<Ast<Expr>, ParseError> {
        if self.is_done() {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }

        let tok = self.peek().unwrap();
        let start = tok.location.start();
        match tok.kind {
            // Handle prefixes
            TokenKind::Minus
            | TokenKind::Not
            | TokenKind::Mult
            | TokenKind::Deref
            | TokenKind::BitAnd => {
                let op = match tok.kind {
                    TokenKind::Minus => PrefixExprKind::Minus,
                    TokenKind::Not => PrefixExprKind::Not,
                    TokenKind::Mult => PrefixExprKind::Deref,
                    TokenKind::Deref => PrefixExprKind::Deref,
                    TokenKind::BitAnd => PrefixExprKind::Address,
                    _ => unreachable!(),
                };
                self.next();
                let prec = get_prefix_precedence(&op);
                let mut left = self.parse_primary()?;

                left = self.parse_binop_rhs(prec, left)?;
                let end = left.loc().end();
                let span = start.span_to(&end);

                Ok(Ast::new(Expr::Prefix { op, expr: left }, span))
            }
            TokenKind::Identifier(s) => {
                let span = self.next().unwrap().location.clone();
                Ok(Ast::new(Expr::Identifier(Ast::new(s, span.clone())), span))
            }
            TokenKind::IntLit(n) => {
                let span = self.next().unwrap().location;
                Ok(Ast::new(
                    Expr::Literal(Ast::new(Literal::Int(n), span.clone())),
                    span,
                ))
            }
            TokenKind::CharLit(s) => {
                let l = self.next().unwrap().location;
                match unescape_char(&s[..]) {
                    Ok(e) => Ok(Ast::new(
                        Expr::Literal(Ast::new(Literal::Char(e), l.clone())),
                        l,
                    )),
                    Err(_) => self.emit_error(ParseErrKind::BadCharLiteral(s)),
                }
            }
            TokenKind::StrLit(s) => {
                let l = self.next().unwrap().location;
                Ok(Ast::new(
                    Expr::Literal(Ast::new(Literal::String(s), l.clone())),
                    l.clone(),
                ))
            }
            TokenKind::OpenPar => {
                let start = self.next().unwrap().location.start();
                if self.match_tokenkind(TokenKind::ClosePar) {
                    let end = self.next().unwrap().location.end();

                    return Ok(Ast::new(Expr::Tuple(vec![]), start.span_to(&end)));
                }
                let p = self.parse_expr()?;

                if !self.match_tokenkind(TokenKind::ClosePar) {
                    let mut v = vec![p];

                    while !self.match_tokenkind(TokenKind::ClosePar) {
                        if !self.match_tokenkind(TokenKind::Comma) {
                            break;
                        }
                        self.next();
                        let expr = self.parse_expr()?;

                        v.push(expr);
                    }
                    if !self.match_tokenkind(TokenKind::ClosePar) {
                        return self.emit_error(ParseErrKind::UnclosedParen(start));
                    }
                    let end = self.next().unwrap().location.end();
                    Ok(Ast::new(Expr::Tuple(v), start.span_to(&end)))
                } else {
                    self.next();
                    Ok(p)
                }
            }
            TokenKind::Directive(s) => {
                let loc = self.next().unwrap().location;
                let start = loc.start();
                let end = loc.end();
                match s.as_str() {
                    "as" => {
                        let t = self.parse_type()?;
                        let e = self.parse_expr()?;
                        let end = e.loc().end();
                        Ok(Ast::new(
                            Expr::AsDir { ty: t, expr: e },
                            start.span_to(&end),
                        ))
                    }
                    "new" => {
                        let t = self.parse_type()?;
                        let e = self.parse_expr()?;
                        let end = e.loc().end();

                        Ok(Ast::new(
                            Expr::AsDir { ty: t, expr: e },
                            start.span_to(&end),
                        ))
                    }
                    "size" => {
                        let e = self.parse_type()?;
                        let end = e.loc().end();
                        Ok(Ast::new(Expr::SizeDir(e), start.span_to(&end)))
                    }
                    "str" => {
                        let e = self.parse_type()?;
                        let end = e.loc().end();
                        Ok(Ast::new(Expr::StrDir(e), start.span_to(&end)))
                    }
                    "todo" => Ok(Ast::new(Expr::TodoDir, start.span_to(&end))),
                    _ => {
                        self.next();
                        self.emit_abort(ParseErrKind::UnsupportedDir(s))
                    }
                }
            }

            _ => return self.emit_error(ParseErrKind::BadStartToken),
        }
    }

    fn parse_postfix(&mut self, mut expr: Ast<Expr>) -> Result<Ast<Expr>, ParseError> {
        if self.is_done() {
            return Ok(expr);
        }

        let start = expr.loc().start();

        let peek_tok = self.peek().unwrap();
        match peek_tok.kind {
            TokenKind::OpenPar => {
                let mut args = Vec::new();
                self.next();
                while !self.match_tokenkind(TokenKind::ClosePar) {
                    if self.is_done() {
                        return self
                            .emit_error(ParseErrKind::UnclosedParen(peek_tok.location.start()));
                    }
                    let arg = self.parse_expr()?;

                    args.push(arg);
                    if !self.match_tokenkind(TokenKind::Comma) {
                        break;
                    }
                    self.next();
                }
                if !self.match_tokenkind(TokenKind::ClosePar) {
                    return self.emit_error(ParseErrKind::UnclosedParen(peek_tok.location.start()));
                }
                let end = self.next().unwrap().location.end();
                expr = Ast::new(
                    Expr::Postfix {
                        expr,
                        op: PostfixExprKind::Call(args),
                    },
                    start.span_to(&end),
                );
            }
            TokenKind::OpenSqr => {
                let t = self.next().unwrap();
                let e = self.parse_expr()?;

                if !self.match_tokenkind(TokenKind::CloseSqr) {
                    return self.emit_error(ParseErrKind::UnclosedSqr(t.location.start()));
                }
                let end = self.next().unwrap().location.end();
                expr = Ast::new(
                    Expr::Postfix {
                        expr,
                        op: PostfixExprKind::Subscript(e),
                    },
                    start.span_to(&end),
                );
            }
            _ => {}
        }
        Ok(expr)
    }

    fn parse_member(&mut self) -> Result<CMem, ParseError> {
        let access_spec = self.parse_identifier_as_string();
        if access_spec.is_err() {
            return self.emit_error(ParseErrKind::ExpectedAccessSpec);
        }
        let access_spec = access_spec.unwrap();
        let acc_loc = access_spec.loc();
        let start = acc_loc.start();
        let actual_as = Ast::new(
            match access_spec.as_ref().as_str() {
                "public" => AccessSpec::Public,
                "private" => AccessSpec::Private,
                _ => return self.emit_error(ParseErrKind::ExpectedAccessSpec),
            },
            acc_loc.clone(),
        );

        let is_static = if self.match_tokenkind(TokenKind::Static) {
            self.next();
            true
        } else {
            false
        };

        let decl = self.parse_letless_var(start.clone())?;

        if !self.match_tokenkind(TokenKind::Semicolon) {
            return self.emit_abort(ParseErrKind::ExpectedSemicol);
        }
        let end = self.next().unwrap().location.end();
        Ok(CMem {
            access_spec: actual_as,
            is_static,
            decl,
        })
    }

    fn parse_method(&mut self) -> Result<CMeth, ParseError> {
        let access_spec = self.parse_identifier_as_string();
        if access_spec.is_err() {
            return self.emit_error(ParseErrKind::ExpectedAccessSpec);
        }
        let access_spec = access_spec.unwrap();
        let acc_loc = access_spec.loc();
        let actual_as = Ast::new(
            match access_spec.as_ref().as_str() {
                "public" => AccessSpec::Public,
                "private" => AccessSpec::Private,
                _ => return self.emit_error(ParseErrKind::ExpectedAccessSpec),
            },
            acc_loc.clone(),
        );

        let is_static = if self.match_tokenkind(TokenKind::Static) {
            self.next();
            true
        } else {
            false
        };

        let position = self.position;
        let mut proto = self.parse_fundef_proto_gen(true);
        if proto.is_err() {
            // TODO
            self.position = position;
            proto = self.parse_fundef_proto_gen(false);
        }

        let proto = proto?;
        let start = proto.loc().start();

        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_error(ParseErrKind::ExpectedArrowInLet);
        }
        self.next();
        if !self.match_tokenkind(TokenKind::OpenBra) {
            return self.emit_error(ParseErrKind::ExpectedOpenBraInFundef);
        }
        if self.is_done() {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }
        let bra = self.next().unwrap();
        let mut body = Vec::new();
        while !self.match_tokenkind(TokenKind::CloseBra) {
            if self.is_done() {
                break;
            }
            let stmt = self.parse_stmt()?;

            body.push(stmt);
        }
        if !self.match_tokenkind(TokenKind::CloseBra) {
            return self.emit_error(ParseErrKind::UnclosedBra(bra.location.start()));
        }
        let end = self.next().unwrap().location.end();
        Ok(CMeth {
            access_spec: actual_as,
            is_static,
            fundef: Ast::new(Fundef { proto, body }, start.span_to(&end)),
        })
    }

    fn parse_class(&mut self) -> Result<Ast<ClassAst>, ParseError> {
        if !self.match_tokenkind(TokenKind::Class) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let t = self.next().unwrap();
        let start = t.location.start();
        let mut template_decls = Vec::new();
        if self.match_tokenkind(TokenKind::Lt) {
            let first = self.next().unwrap();
            while !self.match_tokenkind(TokenKind::Gt) {
                if self.is_done() {
                    break;
                }
                let decl = self.parse_template_arg()?;
                template_decls.push(decl);
                if self.match_tokenkind(TokenKind::Comma) {
                    self.next();
                } else {
                    break;
                }
            }

            if !self.match_tokenkind(TokenKind::Gt) {
                return self.emit_error(ParseErrKind::UnclosedTempArgs(first.location.start()));
            }
            self.next();
        }
        let name = self.parse_identifier_as_string();
        if name.is_err() {
            return self.emit_error(ParseErrKind::ExpectedClassName);
        }
        let name = name?;
        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_error(ParseErrKind::ExpectedArrowInClass);
        }
        self.next();
        if !self.match_tokenkind(TokenKind::OpenBra) {
            return self.emit_error(ParseErrKind::ExpectedOpenBraInClass);
        }
        let bra = self.next().unwrap();
        let mut methods = Vec::new();
        let mut members = Vec::new();
        while !self.match_tokenkind(TokenKind::CloseBra) {
            if self.is_done() {
                break;
            }
            let position_before_method = self.position;

            let method = self.parse_method();
            if method.is_err() {
                let pos = self.position;
                self.position = position_before_method;
                let x = method.clone().err().unwrap();
                let err = self.emit_abort_at(x.kind.0, x.span);
                let member = self.parse_member();
                if member.is_err() {
                    if pos > self.position {
                        return err;
                    } else {
                        member.clone()?;
                    }
                }
                let member = member.unwrap();
                members.push(member);
            } else {
                let method = method.unwrap();
                methods.push(method);
            }
        }
        if !self.match_tokenkind(TokenKind::CloseBra) {
            return self.emit_error(ParseErrKind::UnclosedBra(bra.location.start()));
        }

        let end = self.next().unwrap().location.end();
        Ok(Ast::new(
            ClassAst {
                name,
                template_decls,
                methods,
                members,
            },
            start.span_to(&end),
        ))
    }

    fn parse_class_top_level(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        let c = self.parse_class()?;
        let span = c.loc().clone();
        Ok(Ast::new(TopLevel::Class(c), span))
    }

    fn try_parse_any<Ret, F>(&mut self, parse_fns: Vec<F>) -> Result<Ast<Ret>, ParseError>
    where
        F: Fn(&mut Parser) -> Result<Ast<Ret>, ParseError>,
    {
        let mut result = None;
        let mut positions: Vec<usize> = Vec::new();
        let mut errors: Vec<ParseError> = Vec::new();
        let original = self.position;
        if self.is_done() {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }
        for f in parse_fns {
            let res = f(self);
            if let Ok(value) = res {
                result = Some(Ok(value));
                break;
            } else {
                positions.push(self.position);
                self.position = original;
                let e = res.err().unwrap();
                if matches!(e.kind.1, ParseErrLevel::Abort) {
                    return Err(e);
                }
                errors.push(e);
            }
        }
        let max_idx = positions
            .iter()
            .enumerate()
            .max_by_key(|&(_, val)| val)
            .map(|(i, _)| i);
        result.unwrap_or_else(|| {
            self.position = original;
            Err(errors[max_idx.unwrap()].clone())
        })
    }

    pub fn parse_let_stmt(&mut self) -> Result<Ast<Stmt>, ParseError> {
        let res = self.parse_let_decl()?;
        let span = res.loc().clone();
        Ok(Ast::new(Stmt::Let(res), span))
    }

    fn parse_impl(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        // Skip 'impl' token
        //
        if !self.match_tokenkind(TokenKind::Impl) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let start = self.next().unwrap().location.start();

        let mut templates = Vec::new();

        // Parse optional template parameters <T, U, ...>
        if self.match_tokenkind(TokenKind::Lt) {
            let temp_loc = self.next().unwrap().location;
            loop {
                let template = self.parse_template_arg()?;
                templates.push(template);

                if self.match_tokenkind(TokenKind::Comma) {
                    self.next();
                    continue;
                } else if self.match_tokenkind(TokenKind::Gt) {
                    self.next();
                    break;
                } else {
                    return self.emit_error(ParseErrKind::UnclosedTempArgs(temp_loc.start()));
                }
            }
        }

        // Parse trait name
        let mut trait_name = Some(self.parse_type()?);

        // Expect 'for' keyword
        let for_type = if self.match_tokenkind(TokenKind::For) {
            self.next();

            // Parse type being implemented for
            let for_type = self.parse_type()?;
            for_type
        } else {
            let for_type = trait_name.unwrap();
            trait_name = None;
            for_type
        };

        // Expect '=>'
        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_abort(ParseErrKind::ExpectedArrow);
        }

        self.next();

        // Expect '{'
        if !self.match_tokenkind(TokenKind::OpenBra) {
            return self.emit_abort(ParseErrKind::ExpectedOpenBraInClass);
        }

        let bra_loc = self.next().unwrap().location;

        // Parse method implementations
        let mut body = Vec::new();
        let mut type_aliases = Vec::new();

        while !self.match_tokenkind(TokenKind::CloseBra) {
            if self.is_done() {
                return self.emit_error(ParseErrKind::UnclosedBra(bra_loc.start()));
            }

            if self.match_tokenkind(TokenKind::Type) {
                self.next();

                let ty_name = self.parse_identifier_as_string()?;

                if !self.match_tokenkind(TokenKind::BigArrow) {
                    return self.emit_abort(ParseErrKind::ExpectedArrow);
                }

                self.next();

                let ty = self.parse_type()?;

                if self.match_tokenkind(TokenKind::Impl) {
                    self.next();
                    todo!()
                }

                if !self.match_tokenkind(TokenKind::Semicolon) {
                    return self.emit_abort(ParseErrKind::ExpectedSemicol);
                }

                self.next();

                let entry = (ty_name, ty);
                type_aliases.push(entry);
            } else {
                body.push(self.parse_method()?);
            }
        }

        let end = self.next().unwrap().location.end();

        Ok(Ast::new(
            TopLevel::Implementation(Ast::new(
                Implementation {
                    templates,
                    trait_name,
                    for_type,
                    body,
                    type_aliases,
                },
                start.span_to(&end),
            )),
            start.span_to(&end),
        ))
    }

    pub fn parse_top_level_let(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        let res = self.parse_let_decl()?;
        let span = res.loc().clone();
        Ok(Ast::new(TopLevel::LetDecl(res), span))
    }

    pub fn parse_defer_stmt(&mut self) -> Result<Ast<Stmt>, ParseError> {
        if !self.match_tokenkind(TokenKind::Defer) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let tok = self.next().unwrap();
        let start = &tok.location.start();
        let e = self.parse_stmt()?;
        let end = e.loc().end();
        Ok(Ast::new(Stmt::Defer(e), start.span_to(&end)))
    }

    pub fn parse_return_stmt(&mut self) -> Result<Ast<Stmt>, ParseError> {
        if self.is_done() {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }
        let tok = self.peek().unwrap();
        let start = &tok.location.start();
        if !matches!(tok.kind, TokenKind::Return) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let end = self.next().unwrap().location;
        if self.match_tokenkind(TokenKind::Semicolon) {
            let end = self.next().unwrap().location;
            return Ok(Ast::new(Stmt::Return(None), tok.location));
        }
        let e = self.parse_expr()?;
        if !self.match_tokenkind(TokenKind::Semicolon) {
            return self.emit_error(ParseErrKind::ExpectedSemicol);
        }
        let end = self.next().unwrap().location.end();
        Ok(Ast::new(Stmt::Return(Some(e)), start.span_to(&end)))
    }

    pub fn parse_module(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        if self.match_tokenkind(TokenKind::Module) {
            return self.emit_error(ParseErrKind::BadStartToken);
        }
        let start = self.next().unwrap().location.start();
        let name = self.parse_identifier_as_string()?;

        if !self.match_tokenkind(TokenKind::BigArrow) {
            return self.emit_abort(ParseErrKind::ExpectedArrow);
        }
        self.next();

        if !self.match_tokenkind(TokenKind::OpenBra) {
            return self.emit_abort(ParseErrKind::Todo);
        }
        let bra = self.next().unwrap().location;

        let mut toplevels = Vec::new();
        while !self.match_tokenkind(TokenKind::CloseBra) {
            let t = self.parse_top_level()?;
            toplevels.push(t);
        }
        let end = self.next().unwrap().location.end();
        Ok(Ast::new(
            TopLevel::Module(name, toplevels),
            start.span_to(&end),
        ))
    }

    pub fn parse_extern_dir(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        if self.tokens.len() <= self.position {
            return self.emit_error(ParseErrKind::UnexpectedEOF);
        }
        let tok = self.peek().unwrap();
        match tok.kind {
            TokenKind::Directive(ref s) => {
                if s.as_str() == "extern" {
                    let start = self.next().unwrap().location.start();
                    let mut vararg = false;
                    let mut loc_vararg = start.span_to(&start);
                    if self.match_tokenkind(TokenKind::Plus) {
                        vararg = true;
                        loc_vararg = self.next().unwrap().location;
                    }
                    let proto = self.parse_fundef_proto()?;
                    if !self.match_tokenkind(TokenKind::Semicolon) {
                        return self.emit_error(ParseErrKind::ExpectedSemicol);
                    }
                    let end = self.next().unwrap().location.end();
                    return Ok(Ast::new(
                        TopLevel::ExternDir(proto, Ast::new(vararg, loc_vararg)),
                        start.span_to(&end),
                    ));
                } else {
                    return self.emit_error(ParseErrKind::BadStartToken);
                }
            }
            _ => return self.emit_error(ParseErrKind::BadStartToken),
        }
    }

    pub fn parse_top_level_name_alias(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        let (res, span) = self.parse_name_alias()?;
        return Ok(Ast::new(TopLevel::Use(res.0, res.1), span));
    }

    pub fn parse_top_level(&mut self) -> Result<Ast<TopLevel>, ParseError> {
        let res = self.try_parse_any(vec![
            Self::parse_include_dir,
            Self::parse_extern_dir,
            Self::parse_top_level_let,
            Self::parse_fundef,
            Self::parse_top_level_name_alias,
            Self::parse_interface,
            Self::parse_impl,
            Self::parse_class_top_level,
            Self::parse_module,
        ]);
        res
    }

    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut res = Vec::new();
        while self.position < self.tokens.len() {
            if self.is_done() {
                break;
            }
            let tl = self.parse_top_level()?;
            res.push(tl);
        }
        Ok(Program(res))
    }
}
