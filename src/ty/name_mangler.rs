use crate::{
    common::global_interner::TyId,
    ty::{TyCtx, displays::Displayable},
};

use super::tir::ConcreteType;

pub struct NameMangler;

impl NameMangler {
    pub fn mangle_type_name(ctx: &TyCtx, ty: TyId) -> String {
        match ty.as_concrete(ctx) {
            ConcreteType::SpecializedClass(sc_id) => {
                let sc = sc_id.as_spec_class(ctx);
                let templates = sc
                    .templates
                    .iter()
                    .map(|x| Self::mangle_type_name(ctx, *x))
                    .collect::<Vec<_>>()
                    .join("!");
                format!(
                    "@C{}{}",
                    sc.name.to_string(ctx),
                    if templates.is_empty() {
                        "".to_string()
                    } else {
                        format!("@A{}{}", templates.len(), templates)
                    }
                )
            }
            ConcreteType::Primitive(primitive_ty) => {
                let prim = primitive_ty.to_string();
                format!("@B{}{}", prim.len(), prim)
            }
            ConcreteType::Ptr(inner) => {
                let inner = Self::mangle_type_name(ctx, *inner);
                format!("@P{}{}", inner.len(), inner)
            }
            ConcreteType::Tuple(ids) => {
                let ids_str = ids
                    .iter()
                    .map(|x| Self::mangle_type_name(ctx, *x))
                    .collect::<Vec<_>>()
                    .join("!");
                format!("@T{}{}", ids.len(), ids_str)
            }
        }
    }
}
