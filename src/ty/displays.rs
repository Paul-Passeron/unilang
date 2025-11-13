use std::fmt;

use crate::{
    common::global_interner::{SCId, Symbol, TyId},
    ty::{PrimitiveTy, TyCtx, tir::ConcreteType},
};

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
