use std::collections::{HashMap, HashSet};

use crate::{
    common::global_interner::{SCId, Symbol, TyId, TypeExprId},
    ty::{
        PrimitiveTy, TcError, TyCtx,
        displays::Displayable,
        scope::{Definition, TemplateArgument, TypeExpr},
        tir::{ConcreteType, TirCtx},
        type_checker::TypeChecker,
    },
};

impl TyId {
    pub fn as_concrete<'ctx>(&self, ctx: &'ctx TyCtx) -> &'ctx ConcreteType {
        ctx.ctx.interner.get_conc_type(*self)
    }

    pub fn as_mut_concrete<'ctx>(&self, ctx: &'ctx mut TyCtx) -> &'ctx mut ConcreteType {
        ctx.ctx.interner.get_conc_type_mut(*self)
    }

    pub fn as_ptr(&self, ctx: &TyCtx) -> Option<TyId> {
        match self.as_concrete(ctx) {
            ConcreteType::Ptr(inner) => Some(*inner),
            _ => None,
        }
    }

    pub fn as_sc(&self, ctx: &TyCtx) -> Option<SCId> {
        match self.as_concrete(ctx) {
            ConcreteType::SpecializedClass(id) => Some(*id),
            _ => None,
        }
    }

    pub fn as_primitive(&self, ctx: &TyCtx) -> Option<PrimitiveTy> {
        match self.as_concrete(ctx) {
            ConcreteType::Primitive(p) => Some(*p),
            _ => None,
        }
    }

    pub fn as_tuple(&self, ctx: &TyCtx) -> Option<Vec<TyId>> {
        match self.as_concrete(ctx) {
            ConcreteType::Tuple(ids) => Some(ids.clone()),
            _ => None,
        }
    }

    pub fn get_named_field(&self, ctx: &TyCtx, name: Symbol) -> Option<TyId> {
        self.as_sc(ctx)?
            .as_spec_class(ctx)
            .fields
            .iter()
            .find(|x| x.name == name)
            .map(|x| x.ty)
    }

    pub fn get_nth_tuple_field(&self, ctx: &TyCtx, n: usize) -> Option<TyId> {
        self.as_tuple(ctx)?.get(n).copied()
    }

    pub fn is_integer(&self, ctx: &TyCtx) -> bool {
        match self.as_concrete(ctx) {
            ConcreteType::Primitive(PrimitiveTy::Void) => false,
            ConcreteType::Primitive(_) => true,
            _ => false,
        }
    }

    pub fn unfold(&self, ctx: &TyCtx) -> Vec<TyId> {
        match self.as_concrete(ctx) {
            ConcreteType::Tuple(ids) => ids.clone(),
            _ => vec![*self],
        }
    }

    pub fn get_size(&self, ctx: &TyCtx) -> usize {
        let t = self.as_concrete(ctx);
        let alignement = 4;

        match t {
            ConcreteType::SpecializedClass(sc_id) => {
                let sc = sc_id.as_spec_class(ctx);
                sc.fields.iter().fold(0, |acc, ty| {
                    let res = acc + ty.ty.get_size(ctx);
                    let x = res % alignement;
                    res + if x != 0 { alignement - x } else { 0 }
                })
            }
            ConcreteType::Primitive(p) => p.size(),
            ConcreteType::Ptr(_) => 4,
            ConcreteType::Tuple(ids) => ids.iter().fold(0, |acc, ty| {
                let res = acc + ty.get_size(ctx);
                let x = res % alignement;
                res + if x != 0 { alignement - x } else { 0 }
            }),
        }
    }

    pub fn is_coercible(&self, tir_ctx: &TirCtx, ctx: &TyCtx, target: TyId) -> bool {
        if *self == target {
            return true;
        }
        if self.is_integer(ctx) && target.is_integer(ctx) {
            return true;
        }

        if self.as_ptr(ctx).is_some() && target.as_ptr(ctx).is_some() {
            return true;
        }

        if let Some(sc_id) = target.as_sc(ctx) {
            let args = &self.unfold(ctx)[..];
            return sc_id.get_matching_constructor(tir_ctx, ctx, args).is_some();
        }

        todo!()
    }

    // returns None, if no match and Some(vec of bindings) for the templates if yes
    pub fn matches_expr(
        &self,
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: TypeExprId,
        templates: Vec<TemplateArgument>,
    ) -> Option<Vec<TyId>> {
        if templates.len() == 0 {
            return tir
                .visit_type(ctx, expr)
                .map_or(None, |x| (x == *self).then_some(vec![]));
        }

        let mut m = HashMap::new();
        let mut temp_m = HashSet::new();

        for t in &templates {
            temp_m.insert(t.name);
        }

        if !self.matches_expr_aux(tir, ctx, expr, &templates, &temp_m, &mut m) {
            return None;
        }

        for (temp, id) in &m {
            let constraints = &templates
                .iter()
                .find(|x| x.name == *temp)
                .unwrap()
                .constraints;
            for c in constraints {
                let tr = match c.get_def(ctx) {
                    Definition::Trait(tr) => *tr,
                    _ => unreachable!(),
                };
                TypeChecker::type_impl_trait(tir, ctx, tr, *id).ok()?;
            }
        }

        let res = templates
            .iter()
            .map(|x| {
                m.get(&x.name)
                    .ok_or(TcError::Text(format!(
                        "Could not find match for template argument {}.",
                        x.name.to_string(ctx)
                    )))
                    .map(|x| *x)
            })
            .collect::<Result<Vec<_>, _>>()
            .ok();

        res
    }

    pub fn matches_expr_aux(
        &self,
        tir: &mut TirCtx,
        ctx: &mut TyCtx,
        expr: TypeExprId,
        templates: &Vec<TemplateArgument>,
        temp_map: &HashSet<Symbol>,
        map: &mut HashMap<Symbol, TyId>,
    ) -> bool {
        assert!(templates.len() > 0);

        match ctx.ctx.interner.get_type_expr(expr) {
            TypeExpr::Template(name) => {
                if !temp_map.contains(name) {
                    unreachable!("{} is not in {:?}", name.to_string(ctx), temp_map)
                }
                if let Some(other_ty) = map.get(name) {
                    other_ty == self
                } else {
                    map.insert(*name, *self);
                    true
                }
            }
            TypeExpr::Associated(_) => unreachable!(),
            TypeExpr::Instantiation {
                template: (template, t_expr),
                args,
            } if args.len() == 0 => match template.get_def(ctx) {
                Definition::Type(_) => todo!(),
                _ => unreachable!(),
            },
            TypeExpr::Instantiation {
                template: (def, _),
                args,
            } => {
                if let Some(sc_id) = self.as_sc(ctx) {
                    if sc_id.as_spec_class(ctx).original != *def {
                        return false;
                    }
                    let templates_for_ty = sc_id.as_spec_class(ctx).templates.clone();
                    args.clone()
                        .iter()
                        .zip(templates_for_ty)
                        .all(|(a, t)| t.matches_expr_aux(tir, ctx, *a, templates, temp_map, map))
                } else {
                    false
                }
            }
            TypeExpr::Ptr(inner) => {
                if let Some(other_inner) = self.as_ptr(ctx) {
                    other_inner.matches_expr_aux(tir, ctx, *inner, templates, temp_map, map)
                } else {
                    false
                }
            }
            TypeExpr::Tuple(ids) => {
                if let Some(other_ids) = self.as_tuple(ctx)
                    && ids.len() == other_ids.len()
                {
                    ids.clone()
                        .iter()
                        .zip(other_ids)
                        .all(|(i, o)| o.matches_expr_aux(tir, ctx, *i, templates, temp_map, map))
                } else {
                    false
                }
            }
            TypeExpr::Primitive(ty) => tir.get_primitive_type(ctx, *ty) == *self,
            TypeExpr::Concrete(id) => id == self,
        }
    }
}
