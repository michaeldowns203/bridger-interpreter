//! The relations engine — YOUR file.  \[student\]  (Milestone M6)
//!
//! Answers a query by computing the **least fixpoint** of the program's rules
//! over the base facts and the dynamic facts in `self.db`, then matching the
//! query against the result. This is the evaluation the reference's
//! `E-Query` / `E-Solutions` / `E-ForQuery` rules describe; the `Relation`
//! and `ForQuery` arms of `eval_expr` — and the `Call` arm, for a relation
//! applied in call syntax — call [`Interpreter::solutions`] and read off the
//! substitutions.
//!
//! The pieces you build it from: [`Subst::unify`] to match a generator
//! against a fact, `self.eval_expr` (in an environment built from
//! the current substitution) to evaluate a filter, [`RelationDb`] for the
//! dynamic facts, and `self.program().rules` for the rules and the bodiless
//! base facts. The simplest correct shape is the **naive** loop: fire every
//! rule against all the facts derived so far, add what is new, stop when a
//! round adds nothing; `RelationDb::add` reports whether a tuple was new. A
//! semi-naive refinement — each round joining so that at least one generator
//! reads only the facts the previous round added — derives the same facts and
//! is not required; the naive loop passes the same tests.
//!
//! To list this milestone's holes:
//!
//! ```text
//! grep -rn 'todo_m6!' src
//! ```
//!
//! [`RelationDb`]: RelationDb

use super::{RelationDb, Subst, Term, Tuple};
use crate::ast::{self, Decl, Expr, Lit, Name, QArg, Query, Rule, Span, Ty};
use crate::interp::value::compare;
use crate::interp::{type_of, Control, Env, Interpreter, RuntimeError, Value};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

/// The distinct named holes of `q`, in order of first appearance.
pub(crate) fn named_holes(q: &Query) -> Vec<Name> {
    let mut holes: Vec<Name> = Vec::new();
    for arg in &q.args {
        if let QArg::Hole(Some(x)) = arg {
            if !holes.contains(x) {
                holes.push(x.clone());
            }
        }
    }
    holes
}

impl Interpreter {
    /// Looks up `name` in `env` and returns the relation's declared column count.
    /// Returns `UnboundVariable` if the name is missing, or `NotARelation` if
    /// it does not name a declared relation.
    pub(crate) fn relation_arity(
        &self,
        name: &str,
        span: Span,
        env: &Env,
    ) -> Result<usize, Control> {
        match (env.lookup(name), self.program.decls.get(name)) {
            (Some(Value::Relation(_)), Some(Decl::Relation(columns))) => Ok(columns.len()),
            (None, _) => Err(RuntimeError::UnboundVariable { name: name.to_string(), span }.into()),
            _ => Err(RuntimeError::NotARelation { name: name.to_string(), span }.into()),
        }
    }

    /// Every distinct assignment to the named holes of `q` under which `q`
    /// holds — facts that differ only at a bound argument or an anonymous
    /// hole give one solution — in canonical order (`compare` over the hole
    /// values, first hole first).
    /// Bound arguments of `q` are evaluated in `env` first. A hole-free query
    /// yields either one empty substitution or none, which is how the
    /// boolean-position query reads. `span` locates the query for diagnostics.
    pub fn solutions(&mut self, q: &Query, span: Span, env: &Env) -> Result<Vec<Subst>, Control> {
        if self.materializing {
            return Err(RuntimeError::QueryInFilter { span }.into());
        }

        let arity = self.relation_arity(&q.name, span, env)?;

        let holes = named_holes(q);
        let mut pattern = Vec::with_capacity(q.args.len());
        for (i, arg) in q.args.iter().enumerate() {
            match arg {
                QArg::Expr(e) => pattern.push(Term::Val(self.eval_expr(e, env)?)),
                QArg::Hole(Some(x)) => pattern.push(Term::Var(x.clone())),
                QArg::Hole(None) => pattern.push(Term::Var(format!("?{i}"))),
            }
        }
        let pattern_len = pattern.len();
        if pattern_len != arity {
            return Err(RuntimeError::ArityMismatch {
                expected: arity,
                found: pattern_len,
                span,
            }
            .into());
        }

        if self.db.derived().is_none() {
            self.materializing = true;
            let result = self.least_fixpoint(&env.root());
            self.materializing = false;
            self.db.set_derived(result?);
        }
        let facts: &[Tuple] = self
            .db
            .derived()
            .and_then(|closure| closure.get(&q.name))
            .map(Vec::as_slice)
            .unwrap_or(&[]);

        let mut rows: Vec<Vec<Value>> = facts
            .iter()
            .filter_map(|fact| Subst::new().unify(&pattern, fact))
            .map(|s| {
                holes
                    .iter()
                    .map(|h| s.get(h).cloned().expect("hole bound by unify"))
                    .collect()
            })
            .collect();
        rows.sort_by(|a, b| compare_rows(a, b));
        rows.dedup_by(|a, b| compare_rows(a, b) == Ordering::Equal);

        Ok(rows
            .into_iter()
            .map(|row| {
                let mut s = Subst::new();
                for (h, v) in holes.iter().zip(row) {
                    s.bind(h.clone(), v);
                }
                s
            })
            .collect())
    }

    /// Computes all facts implied by the dynamic facts and the program's rules.
    /// Uses semi-naive rounds: for each rule, try each generator with the
    /// previous round's new facts (`delta`), while its other generators read
    /// all known facts. Skip attempts whose selected generator has no new facts.
    /// Rules without generators, including permanent base facts, run only in
    /// the first round. Stop when a round adds no new facts: the least fixpoint.
    fn least_fixpoint(&mut self, root: &Env) -> Result<HashMap<Name, Vec<Tuple>>, Control> {
        let mut known = RelationDb::new();
        let mut delta = RelationDb::new();
        for relation in self.db.relations() {
            for tuple in self.db.facts(relation) {
                known.add(relation, tuple.clone());
                delta.add(relation, tuple.clone());
            }
        }

        let rules = self.program.rules.clone();
        let mut first_round = true;
        loop {
            let mut derived: Vec<(&Name, Tuple)> = Vec::new();
            for rule in &rules {
                let generators: Vec<(usize, &Name)> = rule
                    .body
                    .iter()
                    .enumerate()
                    .filter_map(|(i, c)| self.as_generator(c).map(|(r, _)| (i, r)))
                    .collect();
                if generators.is_empty() {
                    if first_round {
                        for tuple in self.fire(rule, &known, &delta, None, root)? {
                            derived.push((&rule.head.name, tuple));
                        }
                    }
                    continue;
                }
                for (i, relation) in generators {
                    if delta.facts(relation).is_empty() {
                        continue;
                    }
                    for tuple in self.fire(rule, &known, &delta, Some(i), root)? {
                        derived.push((&rule.head.name, tuple));
                    }
                }
            }

            let mut next_delta = RelationDb::new();
            let mut changed = false;
            for (relation, tuple) in derived {
                if known.add(relation, tuple.clone()) {
                    next_delta.add(relation, tuple);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
            delta = next_delta;
            first_round = false;
        }

        Ok(known
            .relations()
            .map(|r| (r.to_string(), known.facts(r).to_vec()))
            .collect())
    }

    /// Applies one rule and returns the head tuples it produces.
    /// First, match all generators in body order to build variable bindings.
    /// If `delta_at` is `Some(i)`, the generator at body position `i` matches
    /// only `delta` facts; other generators match all `known` facts.
    /// Then test the filters in body order for each set of bindings, discarding
    /// it at the first `false`. Use each surviving set to fill in the rule's head.
    fn fire(
        &mut self,
        rule: &Rule,
        known: &RelationDb,
        delta: &RelationDb,
        delta_at: Option<usize>,
        root: &Env,
    ) -> Result<Vec<Tuple>, Control> {
        let mut subs = vec![Subst::new()];
        let mut filters = Vec::new();
        for (i, conjunct) in rule.body.iter().enumerate() {
            let mut next = Vec::new();
            match self.as_generator(conjunct) {
                Some((relation, args)) => {
                    for sub in &subs {
                        let mut pattern = Vec::with_capacity(args.len());
                        for arg in args {
                            pattern.push(match arg {
                                Expr::Var(x, _) => Term::Var(x.clone()),
                                other => Term::Val(self.eval_expr(other, &bind_all(root, sub))?),
                            });
                        }
                        let source = if delta_at == Some(i) { delta } else { known };
                        for fact in source.facts(relation) {
                            if let Some(extended) = sub.unify(&pattern, fact) {
                                next.push(extended);
                            }
                        }
                    }
                }
                None => {
                    filters.push(conjunct);
                    continue;
                }
            }
            subs = next;
            if subs.is_empty() {
                return Ok(Vec::new());
            }
        }
        let mut tuples = Vec::new();
        'solutions: for sub in &subs {
            for filter in &filters {
                if !self.filter_holds(filter, sub, root)? {
                    continue 'solutions;
                }
            }
            tuples.push(instantiate_head(&rule.head, sub, root)?);
        }
        Ok(tuples)
    }

    /// If `e` is a direct call to a declared relation, returns its name and
    /// unevaluated arguments. Returns `None` for any other expression.
    fn as_generator<'e>(&self, e: &'e Expr) -> Option<(&'e Name, &'e [Expr])> {
        match e {
            Expr::Call(callee, args, _) => match &**callee {
                Expr::Var(name, _)
                    if matches!(self.program.decls.get(name), Some(Decl::Relation(_))) =>
                {
                    Some((name, args.as_slice()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Evaluate `filter` in `root` extended with `sub`. A non-`Bool` result is
    /// a `TypeError`; a `return` is `ReturnOutsideFunction`.
    fn filter_holds(&mut self, filter: &Expr, sub: &Subst, root: &Env) -> Result<bool, Control> {
        match self.eval_expr(filter, &bind_all(root, sub)) {
            Ok(Value::Bool(b)) => Ok(b),
            Ok(other) => {
                Err(RuntimeError::TypeError {
                    expected: Ty::bool(),
                    found: type_of(&other),
                    span: filter.span(),
                }
                .into())
            }
            Err(Control::Return(_)) => Err(RuntimeError::ReturnOutsideFunction {
                span: filter.span(),
            }
            .into()),
            Err(stuck) => Err(stuck),
        }
    }
}

/// The tuple `head` gives under `sub`; a variable `sub` leaves unbound is
/// looked up in `root`.
fn instantiate_head(head: &ast::Atom, sub: &Subst, root: &Env) -> Result<Tuple, Control> {
    head.terms
        .iter()
        .map(|t| match t {
            ast::Term::Lit(lit) => Ok(lit_value(lit)),
            ast::Term::Var(x) => sub
                .get(x)
                .cloned()
                .or_else(|| root.lookup(x))
                .ok_or_else(|| {
                    RuntimeError::UnboundVariable {
                        name: x.clone(),
                        span: head.span,
                    }
                    .into()
                }),
        })
        .collect()
}

/// `root` extended with every binding in `sub`.
fn bind_all(root: &Env, sub: &Subst) -> Env {
    sub.iter()
        .fold(root.clone(), |env, (x, v)| env.extend(x.clone(), v.clone()))
}

/// The value of a literal.
fn lit_value(lit: &Lit) -> Value {
    match lit {
        Lit::Int(n) => Value::Int(*n),
        Lit::Bool(b) => Value::Bool(*b),
        Lit::Str(s) => Value::Str(Rc::from(s.as_str())),
        Lit::Unit => Value::Unit,
    }
}

/// The lexicographic `compare` order on equal-length solution rows.
fn compare_rows(a: &[Value], b: &[Value]) -> Ordering {
    a.iter()
        .zip(b)
        .map(|(x, y)| compare(x, y))
        .find(|o| *o != Ordering::Equal)
        .unwrap_or(Ordering::Equal)
}
