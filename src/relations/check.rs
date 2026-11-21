//! Static checks on rules — YOUR file.  \[student\]  (Milestones M6, M7)
//!
//! A rule body is a list of expressions (see [`Rule`]); the parser has not
//! sorted them into generators and filters, and it could not have. These
//! checks are run by `Interpreter::check` (from M6), after the program is
//! loaded and before `main` runs, and together make the engine in `engine.rs`
//! safe to run: after them, every generator names a relation over variables
//! and literals, every variable a filter or the head uses is bound by a
//! generator, and every filter is pure, so it can be evaluated any number of
//! times in any order.
//!
//! Each check is its own function, called once per rule by the provided
//! driver (`check_rules` in `relations/mod.rs`); [`check_guards`] is a
//! separate M7 check over the whole program. Everything else in this file —
//! how you compute the impure functions, the rule's scope, a witness path — is
//! yours to shape; the driver calls only the four functions below.
//!
//! To list a milestone's holes:
//!
//! ```text
//! grep -rn 'todo_m6!' src
//! ```

use super::RuleError;
use crate::ast::{Program, Rule};

/// Which conjuncts of `rule` are generators: a call whose callee names a
/// relation declared in `program`. Everything else is a filter. A generator's
/// arguments must be variables or literals (`ArgumentNotATerm`), and its
/// count must match the relation's declared arity (`Arity`); the head must
/// name a declared relation of the right arity too.
pub fn check_generators(program: &Program, rule: &Rule) -> Result<Vec<bool>, RuleError> {
    let _ = (program, rule);
    todo_m6!("check_generators: classify conjuncts; terms only; head and generator arities")
}

/// Range restriction: every variable in the head, and every variable a
/// filter reads, is bound by some generator of the same rule — or names a
/// top-level definition (a global constant or a function), which every
/// definition may refer to. A generator-bound variable shadows a top-level
/// name; a variable bound by neither is `Unbound`. `generators` is
/// `check_generators`'s answer for this rule.
pub fn check_range_restriction(
    program: &Program,
    rule: &Rule,
    generators: &[bool],
) -> Result<(), RuleError> {
    let _ = (program, rule, generators);
    todo_m6!("check_range_restriction: head and filter variables are generator-bound")
}

/// A filter must be pure (reference, "Purity and effects"): a deterministic
/// function of the variables the generators bound. The never-pure forms are
/// `ref` / `deref` / `:=`, `add` / `clear`, every query (`solutions q`, a
/// bare `q`, `for q`), `while` / `for`, and the impure builtins (`print`,
/// `read_*`); a call is pure only if it names a function known pure or a pure
/// native, so a call through a parameter, a local, a global, or a computed
/// closure is impure — a locally bound name is a local wherever it appears,
/// whatever function shares its name; a method call reaches one head's
/// method when the declarations settle the receiver (`self`, a parameter, a
/// literal, a type or struct name, a generator variable, or a field chain
/// from one) and every impl's method otherwise, and a method with no impl
/// behind it is a built-in conformance, pure; the function handed to
/// `map`/`filter`/`fold` must be a named function, a pure native, or a
/// lambda, for the same reason; `e?` is pure when every
/// `impl From`'s `from` is (it is a `match` and a `return`, and `return` is
/// control, not an effect). A
/// function is pure when its body is, and the set of pure functions is the
/// **greatest** fixpoint: assume every function pure, strike out each whose
/// body contains a never-pure form or calls a struck-out function, repeat
/// until nothing changes. (Equivalently: the impure set is the least fixpoint
/// of "reaches an effect".) Two further conditions make a filter total, which
/// the fixpoint engine needs: the pure call graph is **acyclic** (no self- or
/// mutual recursion among filter-reachable functions), and no such function
/// takes a function-typed parameter. A rejected filter reports the chain of
/// calls from the filter to the effect it reaches (`Impure { witness }`).
/// `generators` is `check_generators`'s answer for this rule.
pub fn check_pure(program: &Program, rule: &Rule, generators: &[bool]) -> Result<(), RuleError> {
    let _ = (program, rule, generators);
    todo_m6!("check_pure: every filter is a pure, total function of the bound variables")
}

/// Every `match` guard in the program must be pure (M7): a guard is a test
/// the matcher runs while choosing an arm, and an effect there would make the
/// choice depend on how many arms were tried. The same purity judgment as a
/// rule filter's, including that no function it reaches takes a function-typed
/// parameter (the analysis cannot follow one); recursion is allowed, since a
/// guard runs once per arm and need not be total. Reports
/// `ImpureGuard { witness }`.
pub fn check_guards(program: &Program) -> Result<(), RuleError> {
    let _ = program;
    todo_m7!("check_guards: every match guard in the program is pure")
}

/// Provided helpers (Milestone M6): walks over expressions that no rule
/// describes. Paste this module at the end of the file, unchanged.
pub mod helpers {
    use crate::ast::{Expr, Name, QArg, Query, Rel, Stmt};
    use std::collections::HashSet;

    /// The immediate subexpressions of `e`, in source order. A query
    /// contributes its bound arguments, never its holes.
    pub fn subexprs(e: &Expr) -> Vec<&Expr> {
        let mut cs: Vec<&Expr> = Vec::new();
        match e {
            Expr::Lit(..) | Expr::Var(..) => {}
            Expr::Unary(_, e1, _)
            | Expr::Field(e1, _, _)
            | Expr::Proj(e1, _, _)
            | Expr::Return(e1, _)
            | Expr::Try(e1, _)
            | Expr::Lambda(_, e1, _) => cs.push(e1),
            Expr::Binary(_, l, r, _) | Expr::Assign(l, r, _) => {
                cs.push(l);
                cs.push(r);
            }
            Expr::If(c, t, els, _) => {
                cs.push(c);
                cs.push(t);
                if let Some(e1) = els {
                    cs.push(e1);
                }
            }
            Expr::While(c, b, _) | Expr::For(_, c, b, _) => {
                cs.push(c);
                cs.push(b);
            }
            Expr::Call(f, args, _) | Expr::Method(f, _, args, _) => {
                cs.push(f);
                cs.extend(args.iter());
            }
            Expr::Tuple(es, _) | Expr::List(es, _) | Expr::Ctor(_, es, _) => {
                cs.extend(es.iter());
            }
            Expr::Struct(_, fields, _) => cs.extend(fields.iter().map(|(_, e)| e)),
            Expr::Match(scrut, arms, _) => {
                cs.push(scrut);
                for a in arms {
                    if let Some(g) = &a.guard {
                        cs.push(g);
                    }
                    cs.push(&a.body);
                }
            }
            Expr::Block(stmts, tail, _) => {
                for s in stmts {
                    match s {
                        Stmt::Let(_, _, e1, _) | Stmt::Expr(e1) => cs.push(e1),
                    }
                }
                if let Some(t) = tail {
                    cs.push(t);
                }
            }
            Expr::ForQuery(q, b, _) => {
                cs.extend(query_exprs(q));
                cs.push(b);
            }
            Expr::Relation(rel, _) => match rel {
                Rel::Add(q) | Rel::Solutions(q) | Rel::Query(q) => {
                    cs.extend(query_exprs(q));
                }
                Rel::Clear(_) => {}
            },
        }
        cs
    }

    /// The bound arguments of a query: every argument that is not a hole.
    pub fn query_exprs(q: &Query) -> impl Iterator<Item = &Expr> {
        q.args.iter().filter_map(|a| match a {
            QArg::Expr(e) => Some(e),
            QArg::Hole(_) => None,
        })
    }

    /// The names `e` reads and does not bind itself, each once, in order of
    /// first appearance: every variable in value position, minus those bound
    /// within `e` (a `let` over the rest of its block, a lambda's parameters,
    /// a `for` variable, a relational `for`'s named holes, a pattern's
    /// names). A direct call's callee, `f` in `f(x)`, is not counted; its
    /// arguments are.
    pub fn free_vars(e: &Expr) -> Vec<Name> {
        let mut out = Vec::new();
        free_vars_into(e, &HashSet::new(), &mut out);
        out
    }

    fn free_vars_into(e: &Expr, bound: &HashSet<Name>, out: &mut Vec<Name>) {
        match e {
            Expr::Var(x, _) => {
                if !bound.contains(x) && !out.contains(x) {
                    out.push(x.clone());
                }
            }
            Expr::Call(callee, args, _) => {
                if !matches!(&**callee, Expr::Var(..)) {
                    free_vars_into(callee, bound, out);
                }
                for a in args {
                    free_vars_into(a, bound, out);
                }
            }
            Expr::Lambda(params, body, _) => {
                let mut inner = bound.clone();
                inner.extend(params.iter().map(|p| p.name.clone()));
                free_vars_into(body, &inner, out);
            }
            Expr::Block(stmts, tail, _) => {
                let mut inner = bound.clone();
                for s in stmts {
                    match s {
                        Stmt::Let(x, _, rhs, _) => {
                            free_vars_into(rhs, &inner, out);
                            inner.insert(x.clone());
                        }
                        Stmt::Expr(e1) => free_vars_into(e1, &inner, out),
                    }
                }
                if let Some(t) = tail {
                    free_vars_into(t, &inner, out);
                }
            }
            Expr::For(x, iter, body, _) => {
                free_vars_into(iter, bound, out);
                let mut inner = bound.clone();
                inner.insert(x.clone());
                free_vars_into(body, &inner, out);
            }
            Expr::Match(scrut, arms, _) => {
                free_vars_into(scrut, bound, out);
                for arm in arms {
                    let mut inner = bound.clone();
                    inner.extend(arm.pat.binders());
                    if let Some(g) = &arm.guard {
                        free_vars_into(g, &inner, out);
                    }
                    free_vars_into(&arm.body, &inner, out);
                }
            }
            Expr::ForQuery(q, body, _) => {
                let mut inner = bound.clone();
                for a in &q.args {
                    match a {
                        QArg::Expr(e1) => free_vars_into(e1, bound, out),
                        QArg::Hole(Some(x)) => {
                            inner.insert(x.clone());
                        }
                        QArg::Hole(None) => {}
                    }
                }
                free_vars_into(body, &inner, out);
            }
            _ => {
                for c in subexprs(e) {
                    free_vars_into(c, bound, out);
                }
            }
        }
    }

    /// Every name bound anywhere within `e`: `let` names, lambda
    /// parameters, `for` variables, a relational `for`'s named holes, and
    /// the names a `match` arm's pattern binds.
    pub fn bound_names(e: &Expr) -> HashSet<Name> {
        let mut out = HashSet::new();
        bound_names_into(e, &mut out);
        out
    }

    fn bound_names_into(e: &Expr, out: &mut HashSet<Name>) {
        match e {
            Expr::Block(stmts, _, _) => {
                for s in stmts {
                    if let Stmt::Let(x, ..) = s {
                        out.insert(x.clone());
                    }
                }
            }
            Expr::Lambda(params, _, _) => {
                out.extend(params.iter().map(|p| p.name.clone()));
            }
            Expr::Match(_, arms, _) => {
                for arm in arms {
                    out.extend(arm.pat.binders());
                }
            }
            Expr::For(x, ..) => {
                out.insert(x.clone());
            }
            Expr::ForQuery(q, ..) => {
                for a in &q.args {
                    if let QArg::Hole(Some(x)) = a {
                        out.insert(x.clone());
                    }
                }
            }
            _ => {}
        }
        for c in subexprs(e) {
            bound_names_into(c, out);
        }
    }
}