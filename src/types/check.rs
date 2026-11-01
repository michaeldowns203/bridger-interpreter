//! The type checker — YOUR file.  \[student\]  (Milestone M5, growing after)
//!
//! [`check_expr`](Checker::check_expr) is to the typing rules what `eval_expr`
//! is to the evaluation rules: one arm per rule, over the same `Expr`. It is
//! **bidirectional**. With an `expected` type the arm *checks* `e` against it
//! (the mode a lambda needs, where the parameter types come from the expected
//! function type); with `None` it *infers* the type from `e` alone. Either way
//! it returns `e`'s type and records it with [`Checker::record`].
//!
//! Every arm is a milestone-tagged hole. The checker arrives at M5 with the
//! expression language of M1–M4; each later milestone's forms get their typing
//! rules when the milestone lands. To list a milestone's holes:
//!
//! ```text
//! grep -rn 'todo_m5!' src
//! ```
//!
//! Where a rule needs two types to agree, call [`Checker::unify`] rather than
//! comparing with `==`: an unannotated `let`, a lambda parameter, an empty
//! list, or `deref` of a not-yet-known reference gets a
//! [`TyKind::Meta`](TyKind::Meta), and the same `unify` call that
//! compares two known types solves it.
//!
//! A few choices the checker makes cannot be recovered at run time, so it hands
//! them to the evaluator through `Checker::record_conversion`, keyed by an
//! expression's span: the `from` a `?` converts through when the error types
//! differ, and the impl chosen when a method call's receiver leaves it
//! ambiguous (both M8). Record at the same span the evaluator looks up, or the
//! choice is silently lost.

use super::{contains_meta, Checker, Ctx, TyError, MAX_NESTING};
use crate::ast::{BinOp, Decl, Expr, Lit, Rule, Span, Stmt, Ty, TyKind, UnOp};
use std::collections::{HashSet};

impl Checker {
    /// The type of `e` in context `ctx`, checked against `expected` when one
    /// is given. Records the result at `e`'s span.
    pub fn check_expr(
        &mut self,
        e: &Expr,
        ctx: &Ctx,
        expected: Option<&Ty>,
    ) -> Result<Ty, TyError> {
        if self.depth >= MAX_NESTING {
            return Err(TyError::TooDeep {
                limit: MAX_NESTING,
                span: e.span(),
            });
        }
        self.depth += 1;
        let result = self.check_expr_inner(e, ctx, expected);
        self.depth -= 1;
        result
    }

    /// Check the expression’s inferred type against the type required by its context, then resolve and record it.
    fn finish_expr(&mut self, ty: Ty, expected: Option<&Ty>, span: Span) -> Result<Ty, TyError> {
        if let Some(exp) = expected {
            self.unify(&ty, exp, span)?;
        }
        let ty = self.resolve(&ty);
        self.record(span, ty.clone());
        Ok(ty)
    }

    fn check_expr_inner(
        &mut self,
        e: &Expr,
        ctx: &Ctx,
        expected: Option<&Ty>,
    ) -> Result<Ty, TyError> {
        match e {
            // ---- M5: the checker over M1–M4's expressions ----
            Expr::Lit(lit, span) => {
                let ty = match lit {
                    Lit::Int(_) => Ty::int(),
                    Lit::Bool(_) => Ty::bool(),
                    Lit::Str(_) => Ty::str(),
                    Lit::Unit => Ty::unit(),
                };
                self.finish_expr(ty, expected, *span)
            }
            Expr::Var(name, span) => {
                let ty = if let Some(ty) = ctx.lookup(name) {
                    ty
                } else if let Some(Decl::Fn(generics, params, ret, _)) = self.decl(name) {
                    let generics = generics.clone();
                    let sig = Ty::func(
                        params.iter().map(|param| param.ty.clone()).collect(),
                        ret.clone(),
                    );
                    let sub = generics
                        .params
                        .iter()
                        .map(|param| (param.name.clone(), self.fresh_meta()))
                        .collect();
                    for param in &generics.params {
                        if let Some(bound) = &param.bound {
                            let mut bound = bound.clone();
                            bound.args =
                                bound.args.iter().map(|arg| arg.substitute(&sub)).collect();
                            self.require_trait(bound, sub[&param.name].clone(), *span);
                        }
                    }
                    sig.substitute(&sub)
                } else if let Some(ty) = self.global_type(name) {
                    ty?
                } else if let Some(ty) = self.native_fn_type(name, *span) {
                    ty
                } else {
                    return Err(TyError::UnboundVariable {
                        name: name.clone(),
                        span: *span,
                    });
                };
                self.finish_expr(ty, expected, *span)
            }
            Expr::Unary(op, e, span) => {
                let ty = match op {
                    UnOp::Neg => {
                        self.check_expr(e, ctx, Some(&Ty::int()))?;
                        Ty::int()
                    }
                    UnOp::Not => {
                        self.check_expr(e, ctx, Some(&Ty::bool()))?;
                        Ty::bool()
                    }
                    UnOp::Ref => {
                        let t = self.check_expr(e, ctx, None)?;
                        Ty::reference(t)
                    }
                    UnOp::Deref => {
                        let t = self.fresh_meta();
                        self.check_expr(e, ctx, Some(&Ty::reference(t.clone())))?;
                        t
                    }
                };
                self.finish_expr(ty, expected, *span)
            }
            Expr::Binary(op, e1, e2, span) => {
                let ty = match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        self.check_expr(e1, ctx, Some(&Ty::int()))?;
                        self.check_expr(e2, ctx, Some(&Ty::int()))?;
                        Ty::int()
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        self.check_expr(e1, ctx, Some(&Ty::int()))?;
                        self.check_expr(e2, ctx, Some(&Ty::int()))?;
                        Ty::bool()
                    }
                    BinOp::And | BinOp::Or => {
                        self.check_expr(e1, ctx, Some(&Ty::bool()))?;
                        self.check_expr(e2, ctx, Some(&Ty::bool()))?;
                        Ty::bool()
                    }
                    BinOp::Eq | BinOp::Ne => {
                        let t = self.check_expr(e1, ctx, None)?;
                        self.check_expr(e2, ctx, Some(&t))?;
                        let t = self.resolve(&t);
                        if contains_meta(&t) {
                            self.require_bound("Eq".to_string(), t, *span);
                        } else if !self.admits_eq(&t, &mut HashSet::new()) {
                            return Err(TyError::NoEquality {
                                is_param: self.is_type_param(&t),
                                ty: t,
                                span: *span,
                            });
                        }
                        Ty::bool()
                    }
                    BinOp::Concat => {
                        let t = self.check_expr(e1, ctx, None)?;
                        let t = self.resolve(&t);
                        if !matches!(t.kind, TyKind::Str | TyKind::List(_) | TyKind::Meta(_)) {
                            return Err(TyError::Mismatch {
                                expected: Ty::str(),
                                found: t,
                                span: e1.span(),
                            });
                        }
                        self.check_expr(e2, ctx, Some(&t))?;
                        let ty = self.resolve(&t);
                        match &ty.kind {
                            TyKind::Str | TyKind::List(_) => ty,
                            TyKind::Meta(_) => return Err(TyError::Ambiguous { span: *span }),
                            _ => {
                                return Err(TyError::Mismatch {
                                    expected: Ty::str(),
                                    found: ty,
                                    span: e2.span(),
                                });
                            }
                        }
                    }
                    BinOp::Cons => {
                        let t = self.check_expr(e1, ctx, None)?;
                        let list_ty = Ty::list(t);
                        self.check_expr(e2, ctx, Some(&list_ty))?;
                        list_ty
                    }
                };
                self.finish_expr(ty, expected, *span)
            }
            Expr::Tuple(es, span) => {
                let exp = expected.map(|ty| self.resolve(ty));
                let expected_ts = match exp.as_ref().map(|ty| &ty.kind) {
                    Some(TyKind::Tuple(ts)) if ts.len() == es.len() => Some(ts),
                    _ => None,
                };
                let mut ts = Vec::with_capacity(es.len());
                for (i, e) in es.iter().enumerate() {
                    let expected_t = expected_ts.map(|ts| &ts[i]);
                    ts.push(self.check_expr(e, ctx, expected_t)?);
                }
                let ty = Ty::tuple(ts);
                self.finish_expr(ty, expected, *span)
            }
            Expr::List(es, span) => {
                let exp = expected.map(|ty| self.resolve(ty));
                let t = match exp.as_ref().map(|ty| &ty.kind) {
                    Some(TyKind::List(t)) => (**t).clone(),
                    _ => self.fresh_meta(),
                };
                for e in es {
                    self.check_expr(e, ctx, Some(&t))?;
                }
                let ty = Ty::list(t);
                self.finish_expr(ty, expected, *span)
            }
            Expr::Proj(e, index, span) => {
                let t = self.check_expr(e, ctx, None)?;
                let t = self.resolve(&t);
                let ty = match &t.kind {
                    TyKind::Tuple(ts) => {
                        ts.get(*index as usize)
                            .cloned()
                            .ok_or(TyError::NoSuchComponent {
                                index: *index,
                                arity: ts.len(),
                                span: *span,
                            })?
                    }
                    TyKind::Meta(_) => self.undetermined(*span)?,
                    _ => {
                        return Err(TyError::NotATuple {
                            index: *index,
                            found: t,
                            span: *span,
                        });
                    }
                };
                self.finish_expr(ty, expected, *span)
            }
            Expr::Block(stmts, tail, span) => {
                let mut cx = ctx.clone();
                let mut leaves = false;
                for stmt in stmts {
                    let (e, at) = match stmt {
                        Stmt::Let(name, annotation, init, at) => {
                            let ty = if let Some(annotation) = annotation {
                                let ty = self.annotation(annotation, &cx, *at)?;
                                self.check_expr(init, &cx, Some(&ty))?;
                                ty
                            } else {
                                self.check_expr(init, &cx, None)?
                            };
                            cx = cx.extend(name.clone(), ty);
                            (init, *at)
                        }
                        Stmt::Expr(e) => {
                            self.check_expr(e, &cx, None)?;
                            (e, e.span())
                        }
                    };
                    if !leaves && self.is_diverging(e.span()) {
                        leaves = true;
                        self.dead_after(at, *span);
                    }
                }
                let ty = match tail {
                    Some(e) => self.check_expr(e, &cx, expected)?,
                    None if leaves => self.fresh_meta(),
                    None => Ty::unit(),
                };
                if tail.as_ref().is_some_and(|e| self.is_diverging(e.span())) {
                    self.record_diverging(*span);
                }
                self.finish_expr(ty, expected, *span)
            }
            Expr::If(cond, then, els, span) => {
                self.check_expr(cond, ctx, Some(&Ty::bool()))?;
                if self.is_diverging(cond.span()) {
                    self.dead_after(cond.span(), *span);
                }
                let t = if let Some(e) = els {
                    let t = self.check_expr(then, ctx, expected)?;
                    self.check_expr(e, ctx, Some(&t))?;
                    if self.is_diverging(then.span()) && self.is_diverging(e.span()) {
                        self.record_diverging(*span);
                    }
                    t
                } else {
                    let t = self.check_expr(then, ctx, None)?;
                    self.unify(&t, &Ty::unit(), then.span()).map_err(|_| {
                        TyError::IfWithoutElse {
                            found: self.resolve(&t),
                            span: then.span(),
                        }
                    })?;
                    Ty::unit()
                };
                self.finish_expr(t, expected, *span)
            }
            Expr::While(cond, body, span) => {
                self.check_expr(cond, ctx, Some(&Ty::bool()))?;
                if self.is_diverging(cond.span()) {
                    self.dead_after(cond.span(), *span);
                }
                self.check_expr(body, ctx, Some(&Ty::unit()))?;
                self.finish_expr(Ty::unit(), expected, *span)
            }
            Expr::For(name, iter, body, span) => {
                let t = self.fresh_meta();
                self.check_expr(iter, ctx, Some(&Ty::list(t.clone())))?;
                if self.is_diverging(iter.span()) {
                    self.dead_after(iter.span(), *span);
                }
                let cx = ctx.extend(name.clone(), t);
                self.check_expr(body, &cx, Some(&Ty::unit()))?;
                self.finish_expr(Ty::unit(), expected, *span)
            }
            Expr::Assign(e1, e2, span) => {
                let t = self.fresh_meta();
                self.check_expr(e1, ctx, Some(&Ty::reference(t.clone())))?;
                self.check_expr(e2, ctx, Some(&t))?;
                self.finish_expr(Ty::unit(), expected, *span)
            }
            Expr::Return(e, span) => {
                let ret = ctx
                    .ret()
                    .ok_or(TyError::ReturnOutsideFunction { span: *span })?;
                self.check_expr(e, ctx, Some(&ret))?;
                self.record_diverging(*span);
                let ty = self.fresh_meta();
                self.finish_expr(ty, expected, *span)
            }
            Expr::Lambda(params, body, span) => {
                let exp = expected.map(|ty| self.resolve(ty));
                let expected_fn = match exp.as_ref().map(|ty| &ty.kind) {
                    Some(TyKind::Fn(param_tys, ret)) if param_tys.len() == params.len() => {
                        Some((param_tys, ret))
                    }
                    _ => None,
                };
                let ret_ty = expected_fn
                    .map(|(_, ret)| (**ret).clone())
                    .unwrap_or_else(|| self.fresh_meta());
                let mut cx = ctx.enter(Some(ret_ty.clone()), ctx.self_ty());
                let mut param_tys = Vec::with_capacity(params.len());
                for (i, param) in params.iter().enumerate() {
                    let ty = if let Some(annotation) = &param.ty {
                        self.annotation(annotation, ctx, param.span)?
                    } else if let Some((expected_ps, _)) = expected_fn {
                        expected_ps[i].clone()
                    } else {
                        self.fresh_meta()
                    };
                    cx = cx.extend(param.name.clone(), ty.clone());
                    param_tys.push(ty);
                }
                self.check_expr(body, &cx, Some(&ret_ty))?;
                let ty = Ty::func(
                    param_tys.iter().map(|ty| self.resolve(ty)).collect(),
                    self.resolve(&ret_ty),
                );
                self.finish_expr(ty, expected, *span)
            }
            Expr::Call(f, args, span) => {
                let (f_ty, bounds) = self.check_callee(f, ctx)?;
                let ty = match &f_ty.kind {
                    TyKind::Fn(param_tys, ret) => {
                        if param_tys.len() != args.len() {
                            return Err(TyError::ArityMismatch {
                                callee: match &**f {
                                    Expr::Var(name, _) => name.clone(),
                                    _ => "this function".to_string(),
                                },
                                expected: param_tys.len(),
                                found: args.len(),
                                span: *span,
                            });
                        }
                        for (arg, param_ty) in args.iter().zip(param_tys.iter()) {
                            self.check_expr(arg, ctx, Some(param_ty))?;
                        }
                        self.finish_call(bounds, param_tys, args, *span);
                        (**ret).clone()
                    }
                    TyKind::Meta(_) => {
                        let mut param_tys = Vec::with_capacity(args.len());
                        for arg in args {
                            param_tys.push(self.check_expr(arg, ctx, None)?);
                        }
                        let ret = self.fresh_meta();
                        let fn_ty = Ty::func(param_tys.clone(), ret.clone());
                        self.unify(&f_ty, &fn_ty, *span)?;
                        self.finish_call(bounds, &param_tys, args, *span);
                        ret
                    }
                    _ => {
                        return Err(TyError::NotAFunction {
                            found: f_ty,
                            span: f.span(),
                        });
                    }
                };
                self.finish_expr(ty, expected, *span)
            }

            // ---- M6: relations ----
            Expr::Relation(..) => todo_m6!("T-Add / T-Clear / T-Solutions / T-Query"),
            Expr::ForQuery(..) => todo_m6!("T-ForQuery"),

            // ---- M7: algebraic data types ----
            Expr::Ctor(..) => todo_m7!("T-Con"),
            Expr::Match(..) => todo_m7!("T-Match (patterns, then exhaustiveness)"),
            Expr::Try(..) => todo_m7!("T-Try"),

            // ---- M8: objects ----
            Expr::Struct(..) => todo_m8!("T-Struct"),
            Expr::Field(..) => todo_m8!("T-Field"),
            Expr::Method(..) => todo_m8!("T-Method (dispatch on the receiver's type; bounds)"),
        }
    }

    /// Make `a` and `b` the same type, or fail with a `Mismatch` at `span`.
    /// While every type is known this is a structural comparison; once
    /// inference variables exist it also *solves* them (`Checker::solve`),
    /// with an occurs check so no type contains itself.
    pub fn unify(&mut self, a: &Ty, b: &Ty, span: Span) -> Result<(), TyError> {
        fn occurs(id: u32, ty: &Ty) -> bool {
            match &ty.kind {
                TyKind::Meta(other) => id == *other,
                TyKind::List(inner) | TyKind::Ref(inner) => occurs(id, inner),
                TyKind::Tuple(parts) | TyKind::Named(_, parts) => {
                    parts.iter().any(|part| occurs(id, part))
                }
                TyKind::Fn(params, ret) => {
                    params.iter().any(|param| occurs(id, param)) || occurs(id, ret)
                }
                _ => false,
            }
        }

        let a = self.resolve(a);
        let b = self.resolve(b);

        if a == b {
            return Ok(());
        }

        let meta_solution = match (&a.kind, &b.kind) {
            (TyKind::Meta(id), _) => Some((*id, &b)),
            (_, TyKind::Meta(id)) => Some((*id, &a)),
            _ => None,
        };
        if let Some((id, ty)) = meta_solution {
            if occurs(id, ty) {
                return Err(TyError::InfiniteType { span });
            }
            self.solve(id, ty.clone());
            return Ok(());
        }

        match (&a.kind, &b.kind) {
            (TyKind::List(found), TyKind::List(expected))
            | (TyKind::Ref(found), TyKind::Ref(expected)) => {
                return self.unify(found, expected, span);
            }
            (TyKind::Tuple(found), TyKind::Tuple(expected)) if found.len() == expected.len() => {
                for (f, e) in found.iter().zip(expected.iter()) {
                    self.unify(f, e, span)?;
                }
                return Ok(());
            }
            (TyKind::Fn(found_params, found_ret), TyKind::Fn(expected_params, expected_ret))
                if found_params.len() == expected_params.len() =>
            {
                for (found, expected) in found_params.iter().zip(expected_params.iter()) {
                    self.unify(found, expected, span)?;
                }
                return self.unify(found_ret, expected_ret, span);
            }
            (
                TyKind::Named(found_name, found_args),
                TyKind::Named(expected_name, expected_args),
            ) if found_name == expected_name && found_args.len() == expected_args.len() => {
                for (found, expected) in found_args.iter().zip(expected_args.iter()) {
                    self.unify(found, expected, span)?;
                }
                return Ok(());
            }
            _ => {}
        }

        Err(TyError::Mismatch {
            expected: b,
            found: a,
            span,
        })
    }

    /// Type-check one rule (Appendix D, "Relations"): bind each generator's
    /// logic variables at their relation's column types, check the head's
    /// terms against the head relation's columns, and check every filter
    /// against `Bool`. A distinct judgment from `check_expr`, which it calls
    /// for the filters; the driver runs it over each rule once relations
    /// arrive.
    pub fn check_rule(&mut self, rule: &Rule) -> Result<(), TyError> {
        let _ = rule;
        todo_m6!("check_rule (generators bind logic variables; head and filters typed)")
    }
}

/// Provided helpers (Milestone M5): plumbing that no typing rule describes.
/// Paste this module at the end of the file, unchanged.
mod helpers {
    use crate::ast::{Decl, Expr, Name, Span, Ty, TyKind};
    use crate::types::{Checker, Ctx, TyError};
    use std::ops::Range;

    type Res<T> = Result<T, TyError>;
    type Bounds = Range<usize>;

    impl Checker {
        /// A type annotation written inside a body (`let x: T`, `|x: T|`): `Self`
        /// resolved to the enclosing `impl`'s type, and every name it uses checked
        /// to be a declared type or a type parameter in scope (`Self` outside an
        /// `impl` names no type).
        pub fn annotation(&self, ty: &Ty, ctx: &Ctx, span: Span) -> Res<Ty> {
            let ty = match ctx.self_ty() {
                Some(self_ty) => ty.with_self(&self_ty),
                None => ty.clone(),
            };
            self.validate_type(&ty, span)?;
            Ok(ty)
        }

        /// The type of a native prelude function (Appendix C, "Functions").
        /// `print` / `println` / `to_string` carry a `Print` bound and `contains`
        /// an `Eq` bound; until M8 `len` carries `Len` and `min` / `max` /
        /// `minimum` / `maximum` carry `Ord`, which the built-in types satisfy.
        /// `None` for a name that is not a native primitive.
        pub fn native_fn_type(&mut self, name: &str, span: Span) -> Option<Ty> {
            let opt = |t: Ty| Ty::named("Option".to_string(), vec![t]);
            let sig = match name {
                "print" | "println" => {
                    let t = self.fresh_meta();
                    self.require_bound("Print".to_string(), t.clone(), span);
                    Ty::func(vec![t], Ty::unit())
                }
                "to_string" => {
                    let t = self.fresh_meta();
                    self.require_bound("Print".to_string(), t.clone(), span);
                    Ty::func(vec![t], Ty::str())
                }
                "abs" => Ty::func(vec![Ty::int()], Ty::int()),
                "even" | "odd" => Ty::func(vec![Ty::int()], Ty::bool()),
                "range" => Ty::func(vec![Ty::int(), Ty::int()], Ty::list(Ty::int())),
                #[cfg(not(feature = "m8"))]
                "len" => {
                    let t = self.fresh_meta();
                    self.require_bound("Len".to_string(), t.clone(), span);
                    Ty::func(vec![t], Ty::int())
                }
                #[cfg(not(feature = "m8"))]
                "min" | "max" => {
                    let t = self.fresh_meta();
                    self.require_bound("Ord".to_string(), t.clone(), span);
                    Ty::func(vec![t.clone(), t.clone()], t)
                }
                #[cfg(not(feature = "m8"))]
                "minimum" | "maximum" => {
                    let t = self.fresh_meta();
                    self.require_bound("Ord".to_string(), t.clone(), span);
                    Ty::func(vec![Ty::list(t.clone())], opt(t))
                }
                "contains" => {
                    let t = self.fresh_meta();
                    self.require_bound("Eq".to_string(), t.clone(), span);
                    Ty::func(vec![Ty::list(t.clone()), t], Ty::bool())
                }
                "head" => {
                    let t = self.fresh_meta();
                    Ty::func(vec![Ty::list(t.clone())], opt(t))
                }
                "tail" => {
                    let t = self.fresh_meta();
                    Ty::func(vec![Ty::list(t.clone())], opt(Ty::list(t)))
                }
                "unwrap_or" => {
                    let t = self.fresh_meta();
                    Ty::func(vec![opt(t.clone()), t.clone()], t)
                }
                "map" => {
                    let (a, b) = (self.fresh_meta(), self.fresh_meta());
                    Ty::func(
                        vec![Ty::list(a.clone()), Ty::func(vec![a], b.clone())],
                        Ty::list(b),
                    )
                }
                "filter" => {
                    let a = self.fresh_meta();
                    let keep = Ty::func(vec![a.clone()], Ty::bool());
                    Ty::func(vec![Ty::list(a.clone()), keep], Ty::list(a))
                }
                "fold" => {
                    let (a, b) = (self.fresh_meta(), self.fresh_meta());
                    Ty::func(
                        vec![
                            Ty::list(a.clone()),
                            b.clone(),
                            Ty::func(vec![b.clone(), a], b.clone()),
                        ],
                        b,
                    )
                }
                "is_some" => {
                    let t = self.fresh_meta();
                    Ty::func(vec![opt(t)], Ty::bool())
                }
                "read_int" => Ty::func(vec![], Ty::int()),
                "read_bool" => Ty::func(vec![], Ty::bool()),
                "read_line" => Ty::func(vec![], Ty::str()),
                "read_int_opt" => Ty::func(vec![], opt(Ty::int())),
                "read_bool_opt" => Ty::func(vec![], opt(Ty::bool())),
                "read_line_opt" => Ty::func(vec![], opt(Ty::str())),
                _ => return None,
            };
            Some(sig)
        }

        /// The type of the top-level global `x`: its annotation, or the type
        /// the driver recorded for its initializer. `None` if `x` is not a
        /// global.
        pub fn global_type(&mut self, x: &Name) -> Option<Res<Ty>> {
            let (annot, init) = match self.decl(x) {
                Some(Decl::Global(annot, init)) => (annot.clone(), init.clone()),
                _ => return None,
            };
            Some(match (annot, self.global_types.get(x)) {
                (Some(ty), _) => Ok(ty),
                (None, Some(ty)) => Ok(ty.clone()),
                (None, None) => self.check_expr(&init, &Ctx::new(None, None), None),
            })
        }

        /// Synthesize the type of a call's callee, resolved, and note what the
        /// call's bookkeeping needs: a named callee is exempt from the
        /// determination rule, and the bounds the callee's type carries come
        /// back as a range to pass to `finish_call`.
        pub fn check_callee(&mut self, f: &Expr, ctx: &Ctx) -> Res<(Ty, Bounds)> {
            let start = self.obligations.len();
            let ty = self.check_expr(f, ctx, None)?;
            if matches!(f, Expr::Var(..)) {
                self.note_callee(f.span());
            }
            Ok((self.resolve(&ty), start..self.obligations.len()))
        }

        /// Call after checking a call's arguments against the parameter types
        /// `param_tys`: a bound the callee placed on a type parameter is
        /// reported at the argument whose parameter mentions it, or at the
        /// whole call if none does.
        pub fn finish_call(
            &mut self,
            bounds: Bounds,
            param_tys: &[Ty],
            args: &[Expr],
            call_span: Span,
        ) {
            for i in bounds {
                let want = &self.obligations[i].1;
                let blamed = param_tys.iter().position(|p| contains_ty(p, want));
                self.obligations[i].2 = match blamed {
                    Some(j) => args[j].span(),
                    None => call_span,
                };
            }
        }

        /// An operand whose type is still unknown where its rule needs it: in
        /// code that never runs nothing is required of it; elsewhere its type
        /// is undetermined.
        pub fn undetermined(&mut self, span: Span) -> Res<Ty> {
            if self.in_dead_code(span) {
                Ok(self.fresh_meta())
            } else {
                Err(TyError::Ambiguous { span })
            }
        }
    }

    /// Whether `needle` occurs in `hay` (structurally, spans aside).
    fn contains_ty(hay: &Ty, needle: &Ty) -> bool {
        if hay == needle {
            return true;
        }
        let any = |ts: &[Ty]| ts.iter().any(|t| contains_ty(t, needle));
        match &hay.kind {
            TyKind::Tuple(ts) | TyKind::Named(_, ts) => any(ts),
            TyKind::List(t) | TyKind::Ref(t) => contains_ty(t, needle),
            TyKind::Fn(ps, r) => any(ps) || contains_ty(r, needle),
            _ => false,
        }
    }
}
