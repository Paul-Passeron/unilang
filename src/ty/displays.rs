use std::fmt;

use crate::{
    common::global_interner::{DefId, SCId, Symbol, TyId, TypeExprId},
    ty::{
        PrimitiveTy, TyCtx,
        scope::TypeExpr,
        tir::{ConcreteType, Signature},
    },
};

use super::scope::Definition;

pub trait Displayable {
    fn to_string(&self, ctx: &TyCtx) -> String;
}

impl Displayable for Symbol {
    fn to_string(&self, ctx: &TyCtx) -> String {
        ctx.ctx.interner.get_symbol(*self).clone()
    }
}

// pub struct VecDispHelper<'a, T: Displayable>(&'a Vec<T>);

// pub fn vdisp<'a, T: Displayable>(v: &'a Vec<T>) -> VecDispHelper<'a, T> {
//     VecDispHelper(v)
// }

impl<'a, T, X> Displayable for T
where
    T: Iterator<Item = &'a X> + Clone,
    X: Displayable + 'a,
{
    fn to_string(&self, ctx: &TyCtx) -> String {
        format!(
            "{}",
            self.clone()
                .map(|x| x.to_string(ctx))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl Displayable for SCId {
    fn to_string(&self, ctx: &TyCtx) -> String {
        let sc = self.as_spec_class(ctx);
        format!(
            "{}{}",
            sc.name.to_string(ctx),
            if sc.templates.is_empty() {
                String::new()
            } else {
                format!("<{}>", sc.templates.iter().to_string(ctx))
            }
        )
    }
}

impl fmt::Display for PrimitiveTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                PrimitiveTy::Void => "void",
                PrimitiveTy::I8 => "i8",
                PrimitiveTy::I16 => "i16",
                PrimitiveTy::I32 => "i32",
                PrimitiveTy::I64 => "i64",
                PrimitiveTy::U8 => "u8",
                PrimitiveTy::U16 => "u16",
                PrimitiveTy::U32 => "u32",
                PrimitiveTy::U64 => "u64",
                PrimitiveTy::Bool => "bool",
            }
        )
    }
}

impl Displayable for TyId {
    fn to_string(&self, ctx: &TyCtx) -> String {
        match self.as_concrete(ctx) {
            ConcreteType::SpecializedClass(id) => id.to_string(ctx),
            ConcreteType::Primitive(ty) => ty.to_string(),
            ConcreteType::Ptr(inner) => {
                let inner_str = inner.to_string(ctx);
                let spacing = if let Some('*') = inner_str.chars().last() {
                    ""
                } else {
                    " "
                };
                format!("{}{}*", inner_str, spacing)
            }
            ConcreteType::Tuple(ids) => {
                format!("({})", ids.iter().to_string(ctx))
            }
        }
    }
}

impl Displayable for Signature {
    fn to_string(&self, ctx: &TyCtx) -> String {
        format!(
            "{}({}) -> {}",
            self.name.to_string(ctx),
            self.params.iter().map(|x| &x.ty).to_string(ctx),
            self.return_ty.to_string(ctx)
        )
    }
}

impl Displayable for TypeExprId {
    fn to_string(&self, ctx: &TyCtx) -> String {
        match ctx.ctx.interner.get_type_expr(*self) {
            TypeExpr::Primitive(ty) => ty.to_string(),
            TypeExpr::Ptr(inner) => {
                let inner_str = inner.to_string(ctx);
                let spacing = if let Some('*') = inner_str.chars().last() {
                    ""
                } else {
                    " "
                };
                format!("{}{}*", inner_str, spacing)
            }
            TypeExpr::Tuple(ids) => {
                format!("({})", ids.iter().to_string(ctx))
            }
            TypeExpr::Template(name) => format!("{}", name.to_string(ctx)),
            TypeExpr::Associated(id) => format!("assoc({})", id),
            TypeExpr::Instantiation {
                template: (_, path),
                args,
            } => {
                format!(
                    "{}<{}>",
                    path.path
                        .iter()
                        .map(|x| x.0.to_string(ctx))
                        .collect::<Vec<_>>()
                        .join("::"),
                    args.iter().to_string(ctx),
                )
            }
            TypeExpr::Concrete(ty_id) => ty_id.to_string(ctx),
        }
    }
}

impl Displayable for DefId {
    fn to_string(&self, ctx: &TyCtx) -> String {
        match self.get_def(ctx) {
            Definition::Class(id) => ctx.ctx.interner.get_class(*id).name.to_string(ctx),
            Definition::Function(id) => id.get_fun(ctx).name.to_string(ctx),
            Definition::Module(id) => ctx.ctx.interner.get_module(*id).name.to_string(ctx),
            Definition::Trait(id) => ctx.ctx.interner.get_tr(*id).name.to_string(ctx),
            Definition::Type(id) => id.to_string(ctx),
            Definition::Unresolved(id) => format!("unresolved({})", id.0),
            Definition::Var(id) => id.get_var(ctx).name.to_string(ctx),
        }
    }
}
