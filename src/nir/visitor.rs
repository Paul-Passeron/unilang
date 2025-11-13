use nonempty::NonEmpty;

use crate::{
    common::{
        context::GlobalContext,
        errors::ParseError,
        global_interner::{ExprId, ItemId, Symbol},
        source_location::Span,
    },
    nir::{
        interner::Interner,
        nir::{
            FieldAccess, FieldAccessKind, NirArgument, NirAssociatedType, NirBinOp, NirBinOpKind,
            NirCall, NirCalled, NirClassDef, NirExpr, NirExprKind, NirFunctionDef, NirGenericArg,
            NirImplBlock, NirItem, NirLiteral, NirMember, NirMethod, NirModuleDef, NirPath,
            NirPattern, NirPatternKind, NirProgram, NirStmtKind, NirTraitConstraint, NirTraitDef,
            NirType, NirTypeBound, NirTypeKind, NirVarDecl, SelfKind, StrLit, Visibility,
        },
    },
    parser::ast::{
        AccessSpec, Ast, BinOp, CMem, CMeth, ClassAst, Expr, Fundef, FundefProto, Implementation,
        LetDecl, Literal, PostfixExprKind, PrefixExprKind, Program, Stmt, TemplateDecl, TopLevel,
        Ty, TySpec, TypeName,
    },
};

use super::nir::NirStmt;

#[derive(Debug, Clone)]
pub enum NirErrorKind {
    UnsupportedExprInLHSPattern,
    BadFieldAccess,
    ExpectedIdentifierForMemberDecl,
    NeedTypeForMemberDecl,
    ExpectedExplicitReturnTypeInFDef,
    ExpectedSymbolForMethodNameInCall,
    UnresolvedInclude,
    ParseErrorInInclude(ParseError),
}

#[derive(Debug, Clone)]
pub struct NirError {
    pub span: Span,
    pub error: NirErrorKind,
}

pub struct NirVisitor<'ctx> {
    pub ctx: &'ctx mut GlobalContext,
    full: bool,
}

impl<'ctx> NirVisitor<'ctx> {
    pub fn new(ctx: &'ctx mut GlobalContext, full: bool) -> Self {
        Self { ctx, full }
    }

    pub fn as_symbol(&mut self, iden: &Ast<String>) -> Symbol {
        self.ctx.interner.insert_symbol(iden.as_ref())
    }

    pub fn visit_program(&mut self, program: &Program) -> Result<NirProgram, NirError> {
        let res = program
            .0
            .iter()
            .map(|item| self.visit_item(item))
            .collect::<Result<Vec<Vec<_>>, _>>();
        if let Err(err) = res {
            return Err(err);
        }
        Ok(NirProgram(res.unwrap().into_iter().flatten().collect()))
    }

    fn single_elem_path(&mut self, elem: &Ast<String>) -> NirPath {
        NirPath {
            path: NonEmpty::new((self.as_symbol(elem), *elem.loc())),
        }
    }

    fn visit_template_decl(&mut self, decl: &Ast<TemplateDecl>) -> Result<NirGenericArg, NirError> {
        let d = decl.as_ref();

        let name = self.as_symbol(&d.ty_name);
        let constraints = d
            .interface
            .iter()
            .map(|x| NirTraitConstraint {
                name: self.to_path(x),
                span: *x.loc(),
            })
            .collect();

        let span = *decl.loc();

        Ok(NirGenericArg {
            name,
            constraints,
            span,
        })
    }

    fn to_path(&mut self, tn: &Ast<TypeName>) -> NirPath {
        NirPath {
            path: tn
                .as_ref()
                .path
                .as_ref()
                .map(|x| (self.as_symbol(x), *x.loc()))
                .into(),
        }
    }

    fn visit_ty(&mut self, ty: &Ast<Ty>) -> Result<NirType, NirError> {
        let span = *ty.loc();
        Ok(NirType {
            kind: match ty.as_ref() {
                Ty::Named { templates, name } => NirTypeKind::Named {
                    name: self.to_path(name),
                    generic_args: templates
                        .iter()
                        .map(|x| self.visit_ty(x))
                        .collect::<Result<Vec<_>, _>>()?,
                },

                Ty::Ptr(ast) => NirTypeKind::Ptr({
                    let ty = self.visit_ty(ast)?;
                    Box::new(ty)
                }),
                Ty::Tuple(non_empty) => NirTypeKind::Tuple(
                    non_empty
                        .iter()
                        .map(|x| self.visit_ty(x))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
            },
            span,
        })
    }

    fn visit_args(&mut self, arg: &(Ast<String>, Ast<Ty>)) -> Result<NirArgument, NirError> {
        let name = self.as_symbol(&arg.0);
        let ty = self.visit_ty(&arg.1)?;

        let span = Span::from(&arg.0.loc().start(), &arg.1.loc().end()).unwrap();
        Ok(NirArgument { name, ty, span })
    }

    fn visit_class(&mut self, class: &Ast<ClassAst>) -> Result<ItemId, NirError> {
        let cdef = class.as_ref();
        let name = self.as_symbol(&cdef.name);

        let generic_args = cdef
            .template_decls
            .iter()
            .map(|x| self.visit_template_decl(x))
            .collect::<Result<Vec<_>, _>>()?;

        let methods = cdef
            .methods
            .iter()
            .map(
                |CMeth {
                     access_spec,
                     is_static,
                     fundef,
                 }| {
                    self.visit_method_decl(
                        match access_spec.as_ref() {
                            AccessSpec::Public => Visibility::Public,
                            AccessSpec::Private => Visibility::Private,
                        },
                        *is_static,
                        fundef,
                    )
                },
            )
            .collect::<Result<Vec<_>, _>>()?;

        let members = cdef
            .members
            .iter()
            .map(
                |CMem {
                     access_spec,
                     is_static,
                     decl,
                 }| {
                    self.visit_member(
                        match access_spec.as_ref() {
                            AccessSpec::Public => Visibility::Public,
                            AccessSpec::Private => Visibility::Private,
                        },
                        *is_static,
                        decl,
                    )
                },
            )
            .collect::<Result<Vec<_>, _>>()?;

        let span = *class.loc();
        let def = NirClassDef {
            name,
            generic_args,
            methods,
            members,
            span,
        };

        let node_id = self.ctx.interner.insert_item(NirItem::Class(def));

        Ok(node_id)
    }

    fn visit_method_decl(
        &mut self,
        visibility: Visibility,
        is_static: bool,
        method: &Ast<Fundef>,
    ) -> Result<ItemId, NirError> {
        let mdef = method.as_ref();

        let name = self.as_symbol(&mdef.proto.as_ref().name);

        let generic_args = mdef
            .proto
            .as_ref()
            .template_decls
            .iter()
            .map(|x| self.visit_template_decl(x))
            .collect::<Result<Vec<_>, _>>()?;

        let args = mdef
            .proto
            .as_ref()
            .args
            .iter()
            .map(|x| self.visit_args(x))
            .collect::<Result<Vec<_>, _>>()?;

        let body = self.full.then_some(
            mdef.body
                .iter()
                .map(|x| self.visit_stmt(x))
                .collect::<Result<Vec<_>, _>>()?,
        );

        let return_ty = match mdef
            .proto
            .as_ref()
            .return_ty
            .as_ref()
            .map(|x| self.visit_ty(x))
        {
            Some(Ok(x)) => Some(x),
            None => None,
            Some(Err(x)) => {
                return Err(x);
            }
        };

        let def = NirMethod {
            visibility,
            is_static,
            name,
            self_kind: SelfKind::ByPtr,
            generic_args,
            return_ty,
            args,
            body,
            span: *method.loc(),
        };

        let node_id = self.ctx.interner.insert_item(NirItem::Method(def));

        Ok(node_id)
    }

    fn visit_member(
        &mut self,
        visibility: Visibility,
        is_static: bool,
        member: &Ast<LetDecl>,
    ) -> Result<NirMember, NirError> {
        let mdef = member.as_ref();

        let name = match mdef.lhs.as_ref() {
            Expr::Identifier(ast) => self.as_symbol(ast),
            _ => {
                return Err(NirError {
                    span: *member.loc(),
                    error: NirErrorKind::ExpectedIdentifierForMemberDecl,
                });
            }
        };

        let ty = match mdef.ty.as_ref().map(|x| self.visit_ty(x)) {
            Some(Ok(x)) => x,
            Some(Err(x)) => {
                return Err(x);
            }
            None => {
                return Err(NirError {
                    span: *member.loc(),
                    error: NirErrorKind::NeedTypeForMemberDecl,
                });
            }
        };

        let value = match mdef.value.as_ref().map(|x| self.visit_expr(x)) {
            Some(Ok(x)) => Some(x),
            Some(Err(x)) => {
                return Err(x);
            }
            None => None,
        };

        let span = *member.loc();

        Ok(NirMember {
            visibility,
            is_static,
            name,
            ty,
            value,
            span,
        })
    }

    fn visit_fundef(&mut self, fundef: &Ast<Fundef>) -> Result<ItemId, NirError> {
        let fdef = fundef.as_ref();

        let name = self.as_symbol(&fdef.proto.as_ref().name);

        let generic_args = fdef
            .proto
            .as_ref()
            .template_decls
            .iter()
            .map(|x| self.visit_template_decl(x))
            .collect::<Result<Vec<_>, _>>()?;

        let args = fdef
            .proto
            .as_ref()
            .args
            .iter()
            .map(|x| self.visit_args(x))
            .collect::<Result<Vec<_>, _>>()?;

        let fdef_ty = match fdef.proto.as_ref().return_ty.as_ref() {
            Some(x) => x,
            None => {
                return Err(NirError {
                    span: *fdef.proto.loc(),
                    error: NirErrorKind::ExpectedExplicitReturnTypeInFDef,
                });
            }
        };

        let return_ty = self.visit_ty(fdef_ty)?;

        let body = Some(
            fdef.body
                .iter()
                .map(|x| self.visit_stmt(x))
                .collect::<Result<Vec<_>, _>>()?,
        );

        let span = *fundef.loc();

        let def = NirFunctionDef {
            name,
            generic_args,
            args,
            is_variadic: false,
            return_ty,
            body,
            span,
        };

        let node_id = self.ctx.interner.insert_item(NirItem::Function(def));

        Ok(node_id)
    }

    fn visit_proto_as_method(
        &mut self,
        visibility: Visibility,
        is_static: bool,
        fdef: &Ast<FundefProto>,
    ) -> Result<ItemId, NirError> {
        let name = self.as_symbol(&fdef.as_ref().name);

        let generic_args = fdef
            .as_ref()
            .template_decls
            .iter()
            .map(|x| self.visit_template_decl(x))
            .collect::<Result<Vec<_>, _>>()?;

        let args = fdef
            .as_ref()
            .args
            .iter()
            .map(|x| self.visit_args(x))
            .collect::<Result<Vec<_>, _>>()?;

        let return_ty = match fdef.as_ref().return_ty.as_ref().map(|x| self.visit_ty(x)) {
            Some(Ok(x)) => Some(x),
            None => None,
            Some(Err(x)) => {
                return Err(x);
            }
        };

        let span = *fdef.loc();

        let def = NirMethod {
            visibility,
            is_static,
            name,
            self_kind: SelfKind::ByPtr,
            generic_args,
            return_ty,
            args,
            span,
            body: None,
        };

        let node_id = self.ctx.interner.insert_item(NirItem::Method(def));

        Ok(node_id)
    }

    fn visit_ty_spec(&mut self, ty_spec: &Ast<TySpec>) -> Result<NirAssociatedType, NirError> {
        let tdef = ty_spec.as_ref();

        let name = self.as_symbol(&tdef.name);

        let bounds = tdef
            .implements
            .iter()
            .map(|x| NirTraitConstraint {
                name: self.to_path(x),
                span: *x.loc(),
            })
            .collect::<Vec<_>>();

        let default_value = None;

        let span = *ty_spec.loc();

        Ok(NirAssociatedType {
            name,
            bounds,
            default_value,
            span,
        })
    }

    fn visit_proto(&mut self, proto: &Ast<FundefProto>) -> Result<ItemId, NirError> {
        let name = self.as_symbol(&proto.as_ref().name);

        let generic_args = proto
            .as_ref()
            .template_decls
            .iter()
            .map(|x| self.visit_template_decl(x))
            .collect::<Result<Vec<_>, _>>()?;

        let args = proto
            .as_ref()
            .args
            .iter()
            .map(|x| self.visit_args(x))
            .collect::<Result<Vec<_>, _>>()?;

        let return_ty = self.visit_ty(proto.as_ref().return_ty.as_ref().unwrap())?;

        let span = *proto.loc();

        let def = NirFunctionDef {
            name,
            generic_args,
            return_ty,
            args,
            is_variadic: false,
            body: None,
            span,
        };

        let node_id = self.ctx.interner.insert_item(NirItem::Function(def));

        Ok(node_id)
    }

    fn visit_implementation(&mut self, implem: &Ast<Implementation>) -> Result<ItemId, NirError> {
        let idef = implem.as_ref();
        let implements = match idef.trait_name.as_ref().map(|trait_name| {
            self.visit_ty(trait_name).map(|x| {
                let name = match x.kind {
                    NirTypeKind::Named { name, generic_args } => {
                        assert!(generic_args.len() == 0);
                        name
                    }
                    _ => unreachable!(),
                };
                Some(NirTraitConstraint {
                    name,
                    span: *trait_name.loc(),
                })
            })
        }) {
            Some(Ok(x)) => Some(x),
            Some(Err(x)) => {
                return Err(x);
            }
            None => None,
        }
        .flatten();

        let generic_args = idef
            .templates
            .iter()
            .map(|x| self.visit_template_decl(x))
            .collect::<Result<Vec<_>, _>>()?;

        let ty = self.visit_ty(&idef.for_type)?;

        let types = idef
            .type_aliases
            .iter()
            .map(|(name, ty)| {
                let span = {
                    let start = name.loc().start();
                    let end = name.loc().end();
                    Span::from(&start, &end).unwrap()
                };
                self.visit_ty(ty).map(|t| NirTypeBound {
                    name: self.as_symbol(name),
                    ty: t,
                    span,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let methods = idef
            .body
            .iter()
            .map(
                |CMeth {
                     access_spec,
                     is_static,
                     fundef,
                 }| {
                    self.visit_proto_as_method(
                        match access_spec.as_ref() {
                            AccessSpec::Public => Visibility::Public,
                            AccessSpec::Private => Visibility::Private,
                        },
                        *is_static,
                        &fundef.as_ref().proto,
                    )
                },
            )
            .collect::<Result<Vec<_>, _>>()?;

        let span = *implem.loc();

        let def = NirImplBlock {
            implements,
            generic_args,
            ty,
            types,
            methods,
            span,
        };

        let node_id = self.ctx.interner.insert_item(NirItem::Impl(def));

        Ok(node_id)
    }

    fn visit_item(&mut self, item: &Ast<TopLevel>) -> Result<Vec<ItemId>, NirError> {
        match item.as_ref() {
            TopLevel::LetDecl(_ast) => todo!(),
            TopLevel::IncludeDir(_) => self.visit_include(item),
            TopLevel::ExternDir(ast, ast1) => {
                let is_variadic = *ast1.as_ref();
                let proto_id = self.visit_proto(ast)?;
                let proto = self.ctx.interner.get_item_mut(proto_id);
                let proto = match proto {
                    NirItem::Function(x) => x,
                    _ => unreachable!(),
                };
                proto.is_variadic = is_variadic;
                Ok(vec![proto_id])
            }
            TopLevel::Fundef(ast) => {
                let nir = self.visit_fundef(ast)?;
                Ok(vec![nir])
            }
            TopLevel::Interface(ast) => {
                let idef = ast.as_ref();
                let name = self.as_symbol(&idef.name);
                let ty = {
                    let cons = &idef.constrained_ty;
                    NirGenericArg {
                        name: match cons.ty.as_ref() {
                            Ty::Named { name, templates } if templates.is_empty() => {
                                if name.as_ref().path.len() > 1 {
                                    unreachable!()
                                } else {
                                    self.as_symbol(name.as_ref().path.first())
                                }
                            }
                            _ => unreachable!(),
                        },
                        constraints: cons
                            .constraint
                            .iter()
                            .map(|x| NirTraitConstraint {
                                name: self.single_elem_path(x),
                                span: *x.loc(),
                            })
                            .collect(),
                        span: *cons.ty.loc(),
                    }
                };

                let methods = idef
                    .protos
                    .iter()
                    .map(|(is_static, x)| {
                        self.visit_proto_as_method(Visibility::Public, *is_static, x)
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let types = idef
                    .ty_specs
                    .iter()
                    .map(|x| self.visit_ty_spec(x))
                    .collect::<Result<Vec<_>, _>>()?;

                let span = *item.loc();

                let def = NirTraitDef {
                    name,
                    ty: ty,
                    methods,
                    types,
                    span,
                };

                let node_id = self.ctx.interner.insert_item(NirItem::Trait(def));

                Ok(vec![node_id])
            }
            TopLevel::Class(ast) => {
                let nir = self.visit_class(ast)?;
                Ok(vec![nir])
            }
            TopLevel::Module(name, items) => {
                let end = items.last().map_or(name.loc().end(), |x| x.loc().end());

                let def = NirModuleDef {
                    name: self.as_symbol(name),
                    items: items
                        .iter()
                        .map(|x| self.visit_item(x))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                    span: name.loc().start().span_to(&end),
                };

                let nir = self.ctx.interner.insert_item(NirItem::Module(def));

                Ok(vec![nir])
            }
            TopLevel::Use(Some(name), aliased) => {
                let name = self.as_symbol(name);
                let ty = self.visit_ty(aliased)?;
                let nir = self.ctx.interner.insert_item(NirItem::Alias(name, ty));
                Ok(vec![nir])
            }
            TopLevel::Use(None, aliased) => {
                let ty = self.visit_ty(aliased)?;
                let (name, ty) = match ty.kind {
                    NirTypeKind::Named { name, generic_args } if generic_args.len() == 0 => {
                        if name.path.len() == 1 {
                            let n = name.path[0];
                            (
                                n,
                                NirType {
                                    kind: NirTypeKind::Named {
                                        name: name.clone(),
                                        generic_args: vec![],
                                    },
                                    span: n.1,
                                },
                            )
                        } else {
                            let last = name.path.last().clone();
                            (
                                last,
                                NirType {
                                    kind: NirTypeKind::Named {
                                        name: name,
                                        generic_args: vec![],
                                    },
                                    span: aliased.loc().clone(),
                                },
                            )
                        }
                    }
                    _ => unreachable!(),
                };
                let nir = self.ctx.interner.insert_item(NirItem::Alias(name.0, ty));
                Ok(vec![nir])
            }
            TopLevel::Implementation(ast) => {
                let nir = self.visit_implementation(ast)?;
                Ok(vec![nir])
            }
        }
    }

    fn as_field_access(&mut self, expr: &Ast<Expr>) -> Result<FieldAccess, NirError> {
        let err = Err(NirError {
            span: *expr.loc(),
            error: NirErrorKind::BadFieldAccess,
        });

        let span = *expr.loc();

        let kind = match expr.as_ref() {
            Expr::Literal(ast) => match ast.as_ref() {
                Literal::Int(x) => {
                    if *x >= 0 {
                        FieldAccessKind::Index(*x as u32)
                    } else {
                        return err;
                    }
                }
                _ => {
                    return err;
                }
            },
            Expr::Identifier(ast) => FieldAccessKind::Symbol(self.as_symbol(ast)),
            _ => {
                return err;
            }
        };
        Ok(FieldAccess { kind, span })
    }
    fn visit_pattern(&mut self, expr: &Ast<Expr>) -> Result<NirPattern, NirError> {
        let span = *expr.loc();
        match expr.as_ref() {
            Expr::Identifier(ast) => Ok(NirPattern {
                kind: if ast.as_ref() == "_" {
                    NirPatternKind::Wildcard
                } else {
                    NirPatternKind::Symbol(self.as_symbol(ast))
                },
                span,
            }),
            Expr::Tuple(asts) => Ok(NirPattern {
                kind: NirPatternKind::Tuple(
                    asts.iter()
                        .map(|x| self.visit_pattern(x))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                span,
            }),
            _ => Err(NirError {
                span: *expr.loc(),
                error: NirErrorKind::UnsupportedExprInLHSPattern,
            }),
        }
    }

    fn visit_binop(&mut self, expr: &Ast<Expr>) -> Result<NirExpr, NirError> {
        match expr.as_ref() {
            Expr::BinOp { left, op, right } => Ok(NirExpr {
                kind: match op {
                    BinOp::Plus => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Add,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Minus => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Sub,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Mult => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Mul,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Div => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Div,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Mod => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Mod,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Eq => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Equ,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Neq => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Dif,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Gt => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Gt,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Geq => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Geq,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Lt => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Lt,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Leq => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::Leq,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::And => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::LAnd,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Or => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::LOr,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::BitOr => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::BOr,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::BitAnd => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::BAnd,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::BitXor => NirExprKind::BinOp(NirBinOp {
                        op: NirBinOpKind::BXor,
                        left: self.visit_expr(left)?,
                        right: self.visit_expr(right)?,
                    }),
                    BinOp::Range => NirExprKind::Range {
                        start: self.visit_expr(left)?,
                        end: self.visit_expr(right)?,
                    },
                    BinOp::Access => NirExprKind::Access {
                        from: self.visit_expr(left)?,
                        field: self.as_field_access(right)?,
                    },
                },
                span: *expr.loc(),
            }),
            _ => unreachable!(),
        }
    }

    fn visit_literal(&mut self, lit: &Ast<Literal>) -> Result<NirLiteral, NirError> {
        Ok(match lit.as_ref() {
            Literal::Int(x) => NirLiteral::IntLiteral(*x as i128),
            Literal::Char(x) => NirLiteral::CharLiteral(*x),
            Literal::String(x) => {
                // Should not clone here
                NirLiteral::StringLiteral(self.ctx.interner.insert_string(&StrLit(x.clone())))
            }
        })
    }

    fn visit_called(&mut self, expr: &Ast<Expr>) -> Result<NirCalled, NirError> {
        let span = *expr.loc();
        let (receiver, called) = match expr.as_ref() {
            Expr::BinOp {
                op: BinOp::Access,
                left,
                right,
            } => {
                let receiver = Some(self.visit_expr(left)?);

                let called = match right.as_ref() {
                    Expr::Identifier(ast) => self.as_symbol(ast),
                    _ => {
                        return Err(NirError {
                            span: *right.loc(),
                            error: NirErrorKind::ExpectedSymbolForMethodNameInCall,
                        });
                    }
                };
                (receiver, called)
            }
            Expr::Identifier(ast) => {
                let called = self.as_symbol(ast);
                (None, called)
            }
            x => unreachable!("{:?}", x),
        };
        Ok(NirCalled {
            span,
            receiver,
            called,
        })
    }

    fn visit_prefix(&mut self, expr: &Ast<Expr>, op: &PrefixExprKind) -> Result<NirExpr, NirError> {
        let span = *expr.loc();
        let expr = self.visit_expr(expr)?;
        Ok(NirExpr {
            kind: match op {
                PrefixExprKind::Incr => NirExprKind::PreIncr(expr),
                PrefixExprKind::Decr => NirExprKind::PreDecr(expr),
                PrefixExprKind::Address => NirExprKind::AddrOf(expr),
                PrefixExprKind::Deref => NirExprKind::Deref(expr),
                PrefixExprKind::Minus => NirExprKind::Minus(expr),
                PrefixExprKind::Not => NirExprKind::Not(expr),
            },
            span,
        })
    }

    fn visit_postfix(
        &mut self,
        expr: &Ast<Expr>,
        op: &PostfixExprKind,
        span: Span,
    ) -> Result<NirExpr, NirError> {
        Ok(NirExpr {
            kind: match op {
                PostfixExprKind::Incr => NirExprKind::PostIncr(self.visit_expr(expr)?),
                PostfixExprKind::Decr => NirExprKind::PostDecr(self.visit_expr(expr)?),
                PostfixExprKind::Subscript(ast) => {
                    let value = self.visit_expr(expr)?;
                    let index = self.visit_expr(ast)?;
                    NirExprKind::Subscript { value, index }
                }
                PostfixExprKind::Call(asts) => {
                    let called = self.visit_called(expr)?;

                    let args = asts
                        .iter()
                        .map(|x| self.visit_expr(x))
                        .collect::<Result<Vec<_>, _>>()?;

                    NirExprKind::Call(NirCall {
                        called,
                        // TODO: no way of specifying them in function call
                        generic_args: vec![],
                        args,
                        span,
                    })
                }
            },
            span,
        })
    }

    fn visit_expr(&mut self, expr: &Ast<Expr>) -> Result<ExprId, NirError> {
        let span = *expr.loc();
        let expr = match expr.as_ref() {
            Expr::Literal(ast) => Ok(NirExpr {
                kind: NirExprKind::Literal(self.visit_literal(ast)?),
                span,
            }),
            Expr::Identifier(ast) => Ok(NirExpr {
                kind: NirExprKind::Named(self.as_symbol(ast)),
                span,
            }),
            Expr::Tuple(asts) => Ok(NirExpr {
                kind: NirExprKind::Tuple(
                    asts.iter()
                        .map(|x| self.visit_expr(x))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                span,
            }),
            Expr::BinOp { .. } => self.visit_binop(expr),
            Expr::Prefix { expr, op } => self.visit_prefix(expr, op),
            Expr::Postfix { expr, op } => self.visit_postfix(expr, op, span),
            Expr::AsDir { ty, expr } => {
                let ty = self.visit_ty(ty)?;

                let expr = self.visit_expr(expr)?;
                Ok(NirExpr {
                    kind: NirExprKind::As { ty, expr },
                    span,
                })
            }
            Expr::NewDir { ty, expr } => {
                let ty = self.visit_ty(ty)?;
                let expr = self.visit_expr(expr)?;
                Ok(NirExpr {
                    kind: NirExprKind::New { ty, expr },
                    span,
                })
            }
            Expr::SizeDir(ast) => {
                let ty = self.visit_ty(ast)?;
                Ok(NirExpr {
                    kind: NirExprKind::SizeOf(ty),
                    span,
                })
            }
            Expr::StrDir(ast) => {
                let ty = self.visit_ty(ast)?;
                Ok(NirExpr {
                    kind: NirExprKind::StringOf(ty),
                    span,
                })
            }
            Expr::TodoDir => Ok(NirExpr {
                kind: NirExprKind::TodoDir,
                span,
            }),
        };
        expr.map(|x| self.ctx.interner.insert_expr(x))
    }

    fn visit_let(&mut self, l: &Ast<LetDecl>) -> Result<NirStmt, NirError> {
        let let_decl = l.as_ref();

        let pattern = self.visit_pattern(&let_decl.lhs)?;

        let ty = match let_decl.ty.as_ref().map(|x| self.visit_ty(x)) {
            Some(Ok(x)) => Some(x),
            Some(Err(x)) => {
                return Err(x);
            }
            None => None,
        };

        let value = match let_decl.value.as_ref().map(|x| self.visit_expr(x)) {
            Some(Ok(x)) => Some(x),
            Some(Err(x)) => {
                return Err(x);
            }
            None => None,
        };

        let span = *l.loc();

        Ok(NirStmt {
            kind: NirStmtKind::Let(NirVarDecl {
                pattern,
                ty,
                value,
                span,
            }),
            span,
        })
    }

    fn visit_include(&mut self, item: &Ast<TopLevel>) -> Result<Vec<ItemId>, NirError> {
        match item.as_ref() {
            TopLevel::IncludeDir(asts) => {
                let v = asts.iter().map(|x| x.as_ref()).collect();

                let path = self.ctx.include_resolver.get_path(v);

                if path.is_none() {
                    return Err(NirError {
                        span: *item.loc(),
                        error: NirErrorKind::UnresolvedInclude,
                    });
                }

                let path = path.unwrap();

                if !path.exists() || self.ctx.file_manager.paths.contains(&path).is_some() {
                    return Ok(vec![]);
                }

                let id = self.ctx.file_manager.add_file(&path).unwrap();

                let prgm = self.ctx.parse_file(id);

                let mut include_visitor = NirVisitor::new(self.ctx, true);

                if let Err(x) = prgm {
                    return Err(NirError {
                        span: *item.loc(),
                        error: NirErrorKind::ParseErrorInInclude(x),
                    });
                }

                let prgm = prgm.unwrap();

                let nir = match include_visitor.visit_program(&prgm) {
                    Ok(x) => x,
                    Err(y) => return Err(y),
                }
                .0;
                Ok(nir)
            }
            _ => unreachable!(),
        }
    }

    fn visit_if(&mut self, stmt: &Ast<Stmt>) -> Result<NirStmt, NirError> {
        let (cond_def, then_branch_def, else_branch_def) = match stmt.as_ref() {
            Stmt::If {
                cond,
                then_branch,
                else_branch,
            } => (cond, then_branch, else_branch),
            _ => unreachable!(),
        };

        let cond = self.visit_expr(cond_def)?;

        let then_block = self.visit_stmt(then_branch_def)?;
        let then_block = Box::new(then_block);

        let else_block = match else_branch_def.as_ref().map(|x| self.visit_stmt(x)) {
            Some(Err(x)) => {
                return Err(x);
            }
            Some(Ok(x)) => Some(x),
            None => None,
        };
        let else_block = else_block.map(Box::new);

        Ok(NirStmt {
            kind: NirStmtKind::If {
                cond,
                then_block,
                else_block,
            },
            span: *stmt.loc(),
        })
    }

    fn visit_for(&mut self, stmt: &Ast<Stmt>) -> Result<NirStmt, NirError> {
        let (var_def, iterator_def, body_def) = match stmt.as_ref() {
            Stmt::For {
                var,
                iterator,
                body,
            } => (var, iterator, body),
            _ => unreachable!(),
        };

        let var = self.visit_pattern(var_def)?;

        let iterator = self.visit_expr(iterator_def)?;

        let body = Box::new(self.visit_stmt(body_def)?);

        let span = *stmt.loc();

        Ok(NirStmt {
            kind: NirStmtKind::For {
                var,
                iterator,
                body,
            },
            span,
        })
    }

    fn visit_stmt(&mut self, stmt: &Ast<Stmt>) -> Result<NirStmt, NirError> {
        let span = *stmt.loc();
        Ok(match stmt.as_ref() {
            Stmt::Let(ast) => self.visit_let(ast)?,
            Stmt::Return(ast) => NirStmt {
                kind: NirStmtKind::Return {
                    value: match ast.as_ref().map(|x| self.visit_expr(x)) {
                        Some(Ok(x)) => Some(x),
                        Some(Err(y)) => {
                            return Err(y);
                        }
                        None => None,
                    },
                },
                span,
            },
            Stmt::ExprStmt(ast) => NirStmt {
                kind: NirStmtKind::Expr(self.visit_expr(ast)?),
                span,
            },
            Stmt::If { .. } => self.visit_if(stmt)?,
            Stmt::While { cond, body } => {
                let cond = self.visit_expr(cond)?;

                let body = Box::new(self.visit_stmt(body)?);

                NirStmt {
                    kind: NirStmtKind::While { cond, body },
                    span,
                }
            }
            Stmt::Assign { lhs, rhs } => {
                let assigned = self.visit_expr(lhs)?;

                let value = self.visit_expr(rhs)?;

                NirStmt {
                    kind: NirStmtKind::Assign { assigned, value },
                    span,
                }
            }
            Stmt::For { .. } => self.visit_for(stmt)?,
            Stmt::Block(asts) => NirStmt {
                kind: NirStmtKind::Block(
                    asts.iter()
                        .map(|x| self.visit_stmt(x))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                span,
            },
            Stmt::Break => NirStmt {
                kind: NirStmtKind::Break,
                span,
            },
            Stmt::Defer(ast) => NirStmt {
                kind: NirStmtKind::Defer(Box::new(self.visit_stmt(ast)?)),
                span,
            },
        })
    }
}
