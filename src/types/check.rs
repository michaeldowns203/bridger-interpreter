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
//! [`TyKind::Meta`](crate::ast::TyKind::Meta), and the same `unify` call that
//! compares two known types solves it.
//!
//! A few choices the checker makes cannot be recovered at run time, so it hands
//! them to the evaluator through `Checker::record_conversion`, keyed by an
//! expression's span: the `from` a `?` converts through when the error types
//! differ, and the impl chosen when a method call's receiver leaves it
//! ambiguous (both M8). Record at the same span the evaluator looks up, or the
//! choice is silently lost.

use super::{Checker, Ctx, TyError};
use crate::ast::{Expr, Rule, Span, Ty};

impl Checker {
    /// The type of `e` in context `ctx`, checked against `expected` when one
    /// is given. Records the result at `e`'s span.
    pub fn check_expr(
        &mut self,
        e: &Expr,
        ctx: &Ctx,
        expected: Option<&Ty>,
    ) -> Result<Ty, TyError> {
        // `ctx` and `expected` are read by the arms you write; this line only
        // keeps the unused-variable lint quiet until then.
        let _ = (ctx, expected);
        match e {
            // ---- M5: the checker over M1–M4's expressions ----
            Expr::Lit(..) => todo_m5!("T-Int / T-Bool / T-Str / T-Unit"),
            Expr::Var(..) => todo_m5!("T-Var / T-Self"),
            Expr::Unary(..) => todo_m5!("T-Neg / T-Not / T-Ref / T-Deref"),
            Expr::Binary(..) => {
                todo_m5!("T-Arith / T-Ord / T-Eq / T-And / T-Or / T-Concat / T-Cons")
            }
            Expr::Tuple(..) => todo_m5!("T-Tuple"),
            Expr::List(..) => todo_m5!("T-List"),
            Expr::Proj(..) => todo_m5!("T-Proj"),
            Expr::Block(..) => todo_m5!("T-Block / T-Let / T-Seq"),
            Expr::If(..) => todo_m5!("T-If"),
            Expr::While(..) => todo_m5!("T-While"),
            Expr::For(..) => todo_m5!("T-For"),
            Expr::Assign(..) => todo_m5!("T-Assign"),
            Expr::Return(..) => todo_m5!("T-Return (reads ctx.ret())"),
            Expr::Lambda(..) => {
                todo_m5!("T-Lam (parameter types from `expected`, the annotation, or a fresh meta)")
            }
            Expr::Call(..) => todo_m5!("T-App (first-order matching of generics at the call)"),

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
        let _ = (a, b, span);
        todo_m5!("unify (structural agreement; solves TyKind::Meta with an occurs check)")
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
