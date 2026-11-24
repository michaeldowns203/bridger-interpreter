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

use self::helpers::{bound_names, free_vars, subexprs};
use super::RuleError;
use crate::ast::{Decl, Expr, Lit, Name, Param, Program, Rel, Rule, SrcId, Term, Ty, TyKind, UnOp};
use crate::interp::prelude::native_names;
use std::collections::{HashMap, HashSet};

/// If `e` is a direct call to a declared relation, returns its name and
/// unevaluated arguments. Returns `None` for any other expression.
pub(crate) fn as_generator<'e>(program: &Program, e: &'e Expr) -> Option<(&'e Name, &'e [Expr])> {
    match e {
        Expr::Call(callee, args, _) => match &**callee {
            Expr::Var(name, _) if matches!(program.decls.get(name), Some(Decl::Relation(_))) => {
                Some((name, args.as_slice()))
            }
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn is_native(name: &str) -> bool {
    native_names().any(|n| n == name)
}

/// The variables bound by `rule`'s generators.
fn generator_vars(program: &Program, rule: &Rule) -> HashSet<Name> {
    rule.body
        .iter()
        .filter_map(|c| as_generator(program, c))
        .flat_map(|(_, args)| args.iter())
        .filter_map(|a| match a {
            Expr::Var(x, _) => Some(x.clone()),
            _ => None,
        })
        .collect()
}

/// Which conjuncts of `rule` are generators: a call whose callee names a
/// relation declared in `program`. Everything else is a filter. A generator's
/// arguments must be variables or literals (`ArgumentNotATerm`), and its
/// count must match the relation's declared arity (`Arity`); the head must
/// name a declared relation of the right arity too.
pub fn check_generators(program: &Program, rule: &Rule) -> Result<Vec<bool>, RuleError> {
    let head = &rule.head;
    let head_name = head.name.clone();
    let Some(Decl::Relation(columns)) = program.decls.get(&head_name) else {
        return Err(RuleError::NotARelation {
            name: head_name,
            span: head.span,
        });
    };
    let cols_len = columns.len();
    let terms_len = head.terms.len();
    if cols_len != terms_len {
        return Err(RuleError::Arity {
            name: head_name,
            expected: cols_len,
            found: terms_len,
            span: head.span,
        });
    }

    let mut generators = Vec::with_capacity(rule.body.len());
    for conjunct in &rule.body {
        if let Some((name, args)) = as_generator(program, conjunct) {
            let Some(Decl::Relation(columns)) = program.decls.get(name) else {
                unreachable!() // `as_generator` already confirmed that the declaration exists
            };
            let cols_len = columns.len();
            let args_len = args.len();
            if cols_len != args_len {
                return Err(RuleError::Arity {
                    name: name.clone(),
                    expected: cols_len,
                    found: args_len,
                    span: conjunct.span(),
                });
            }
            for arg in args {
                if !matches!(arg, Expr::Var(..) | Expr::Lit(..)) {
                    return Err(RuleError::ArgumentNotATerm { span: arg.span() });
                }
            }
            generators.push(true);
        } else {
            if let Expr::Call(callee, _, span) = conjunct {
                if let Expr::Var(name, _) = &**callee {
                    if !matches!(
                        program.decls.get(name),
                        Some(Decl::Fn(..) | Decl::Global(..))
                    ) && !is_native(name)
                    {
                        return Err(RuleError::NotARelation {
                            name: name.clone(),
                            span: *span,
                        });
                    }
                }
            }
            generators.push(false);
        }
    }
    Ok(generators)
}

/// Range restriction: every head variable is bound by a generator of the
/// same rule, or it is `Unbound` at the head. Every name a filter reads is
/// generator-bound or names a global, a function, or a native, or it is
/// `Unbound` at the filter. A generator-bound variable shadows a top-level
/// name. `generators` is `check_generators`'s answer for this rule.
pub fn check_range_restriction(
    program: &Program,
    rule: &Rule,
    generators: &[bool],
) -> Result<(), RuleError> {
    let vars = generator_vars(program, rule);

    for term in &rule.head.terms {
        if let Term::Var(x) = term {
            if !vars.contains(x) {
                return Err(RuleError::Unbound {
                    var: x.clone(),
                    span: rule.head.span,
                });
            }
        }
    }

    let top_level = |x: &str| match program.decls.get(x) {
        Some(Decl::Fn(..) | Decl::Global(..)) => true,
        Some(_) => false,
        None => is_native(x),
    };
    for (filter, _) in rule.body.iter().zip(generators).filter(|(_, g)| !**g) {
        for x in free_vars(filter) {
            if !vars.contains(&x) && !top_level(&x) {
                return Err(RuleError::Unbound {
                    var: x,
                    span: filter.span(),
                });
            }
        }
    }
    Ok(())
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
    let purity = Purity::new(program);
    let mut scope = PurityScope::default();
    for conjunct in &rule.body {
        if let Some((name, args)) = as_generator(program, conjunct) {
            if let Some(Decl::Relation(columns)) = program.decls.get(name) {
                for (arg, ty) in args.iter().zip(columns) {
                    if let Expr::Var(x, _) = arg {
                        scope.locals.insert(x.clone());
                        scope.types.insert(x.clone(), ty.clone());
                    }
                }
            }
        }
    }
    for conjunct in &rule.body {
        scope.hide_bindings(conjunct);
    }
    for (filter, _) in rule.body.iter().zip(generators).filter(|(_, g)| !**g) {
        let span = filter.span();

        let reached = purity.reached(filter, &scope);
        if let Some(name) = reached.iter().find(|k| purity.higher_order(k)) {
            return Err(RuleError::HigherOrder {
                name: name.clone(),
                span,
            });
        }
        if let Some(witness) = purity.effect(filter, &scope, &[]) {
            return Err(RuleError::Impure { span, witness });
        }
        if let Some(name) = reached.iter().find(|k| purity.recursive(k)) {
            return Err(RuleError::Recursive {
                name: name.clone(),
                span,
            });
        }
    }
    Ok(())
}

/// Whether `name` is an impure native: output, `to_string`, or a reader.
fn impure_native(name: &str) -> bool {
    matches!(
        name,
        "print"
            | "println"
            | "to_string"
            | "read_int"
            | "read_bool"
            | "read_line"
            | "read_int_opt"
            | "read_bool_opt"
            | "read_line_opt"
    )
}

/// The callback's argument index for `map`, `filter`, and `fold`.
fn callback_index(native: &str) -> Option<usize> {
    match native {
        "map" | "filter" => Some(1),
        "fold" => Some(2),
        _ => None,
    }
}

/// Whether `ty` contains a function type.
fn has_fn_type(ty: &Ty) -> bool {
    match &ty.kind {
        TyKind::Fn(..) => true,
        TyKind::List(t) | TyKind::Ref(t) => has_fn_type(t),
        TyKind::Tuple(ts) | TyKind::Named(_, ts) => ts.iter().any(has_fn_type),
        _ => false,
    }
}

/// Locals for call classification, and declared types safe to use for receivers.
#[derive(Default)]
struct PurityScope {
    locals: HashSet<Name>,
    types: HashMap<Name, Ty>,
}

impl PurityScope {
    fn hide_bindings(&mut self, expr: &Expr) {
        for name in bound_names(expr) {
            self.types.remove(&name);
            self.locals.insert(name);
        }
    }
}

/// A callable's body, its local names, and whether it takes a
/// function-typed parameter.
struct Body<'p> {
    expr: &'p Expr,
    scope: PurityScope,
    higher_order: bool,
    /// Prelude callables, exempt from the recursion and higher-order checks.
    trusted: bool,
}

impl<'p> Body<'p> {
    fn new(expr: &'p Expr, params: &[Param], self_ty: Option<&Ty>, trusted: bool) -> Self {
        let mut scope = PurityScope::default();
        for param in params {
            scope.locals.insert(param.name.clone());
            let ty = if matches!(param.ty.kind, TyKind::SelfTy) {
                self_ty.unwrap_or(&param.ty)
            } else {
                &param.ty
            };
            scope.types.insert(param.name.clone(), ty.clone());
        }
        if let Some(ty) = self_ty {
            scope.locals.insert("self".into());
            scope.types.insert("self".into(), ty.clone());
        }
        scope.hide_bindings(expr);
        Self {
            expr,
            scope,
            higher_order: params.iter().any(|p| has_fn_type(&p.ty)),
            trusted,
        }
    }
}

/// The purity analysis of a program. Callables are keyed by name: a function
/// as `f`, and methods by head and name as `H.m`. `impure` maps
/// each impure callable to its witness.
struct Purity<'p> {
    program: &'p Program,
    bodies: HashMap<Name, Vec<Body<'p>>>,
    calls: HashMap<Name, Vec<Name>>,
    impure: HashMap<Name, Vec<Name>>,
}

impl<'p> Purity<'p> {
    /// Collects every callable's body and computes the impure set as a least
    /// fixpoint: each round marks every callable whose body reaches an effect,
    /// given those marked so far, until a round marks none.
    fn new(program: &'p Program) -> Self {
        let mut bodies: HashMap<Name, Vec<Body<'p>>> = HashMap::new();
        for (name, decl) in &program.decls {
            if let Decl::Fn(_, params, _, body) = decl {
                let trusted = program.spans.get(name).is_some_and(|s| s.src == SrcId(0));
                bodies.insert(name.clone(), vec![Body::new(body, params, None, trusted)]);
            }
        }
        for imp in &program.impls {
            let Some(head) = Self::type_head(program, &imp.ty) else {
                continue;
            };
            for method in &imp.methods {
                bodies
                    .entry(format!("{head}.{}", method.name))
                    .or_default()
                    .push(Body::new(
                        &method.body,
                        &method.params,
                        Some(&imp.ty),
                        imp.span.src == SrcId(0),
                    ));
            }
        }
        let mut purity = Self {
            program,
            bodies,
            calls: HashMap::new(),
            impure: HashMap::new(),
        };
        for (key, bodies) in &purity.bodies {
            let mut refs = Vec::new();
            for body in bodies {
                purity.refs(body.expr, &body.scope, &mut refs);
            }
            purity.calls.insert(key.clone(), refs);
        }
        purity.find_impure();
        purity
    }

    fn find_impure(&mut self) {
        let mut keys: Vec<_> = self.bodies.keys().cloned().collect();
        keys.sort();
        loop {
            let mut changed = false;
            for key in &keys {
                if self.impure.contains_key(key) {
                    continue;
                }
                if let Some(witness) = self.bodies[key]
                    .iter()
                    .find_map(|b| self.effect(b.expr, &b.scope, &[]))
                {
                    self.impure.insert(key.clone(), witness);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn type_head(program: &Program, ty: &Ty) -> Option<Name> {
        Some(match &ty.kind {
            TyKind::Int => "Int".into(),
            TyKind::Bool => "Bool".into(),
            TyKind::Str => "String".into(),
            TyKind::Unit => "()".into(),
            TyKind::List(_) => "[]".into(),
            TyKind::Named(n, _)
                if matches!(
                    program.decls.get(n),
                    Some(Decl::Struct(..) | Decl::Type(..))
                ) =>
            {
                n.clone()
            }
            _ => return None,
        })
    }

    /// Only declarations settle a receiver; calls and local initializers do not.
    fn receiver_type(&self, e: &Expr, scope: &PurityScope) -> Option<Ty> {
        match e {
            Expr::Var(x, _) if scope.locals.contains(x) => scope.types.get(x).cloned(),
            Expr::Var(x, _) => match x.as_str() {
                "Int" => Some(Ty::int()),
                "Bool" => Some(Ty::bool()),
                "String" => Some(Ty::str()),
                _ if matches!(
                    self.program.decls.get(x),
                    Some(Decl::Struct(..) | Decl::Type(..))
                ) =>
                {
                    Some(Ty::named(x.clone(), vec![]))
                }
                _ => None,
            },
            Expr::Struct(x, ..) => Some(Ty::named(x.clone(), vec![])),
            Expr::Lit(lit, _) => Some(match lit {
                Lit::Int(_) => Ty::int(),
                Lit::Bool(_) => Ty::bool(),
                Lit::Str(_) => Ty::str(),
                Lit::Unit => Ty::unit(),
            }),
            Expr::Field(recv, field, _) => {
                let ty = self.receiver_type(recv, scope)?;
                let TyKind::Named(name, args) = &ty.kind else {
                    return None;
                };
                let Decl::Struct(generics, fields) = self.program.decls.get(name)? else {
                    return None;
                };
                let substitutions = generics
                    .params
                    .iter()
                    .zip(args.iter())
                    .map(|(p, t)| (p.name.clone(), t.clone()))
                    .collect();
                Some(
                    fields
                        .iter()
                        .find(|f| f.name == *field)?
                        .ty
                        .substitute(&substitutions),
                )
            }
            _ => None,
        }
    }

    fn method_key(&self, recv: &Expr, method: &str, scope: &PurityScope) -> Name {
        let head = self
            .receiver_type(recv, scope)
            .and_then(|ty| Self::type_head(self.program, &ty))
            .unwrap_or_default();
        format!("{head}.{method}")
    }

    fn conversions(&self) -> Vec<Name> {
        self.program
            .impls
            .iter()
            .filter(|imp| imp.trait_.as_ref().is_some_and(|t| t.name == "From"))
            .filter_map(|imp| Self::type_head(self.program, &imp.ty))
            .map(|head| format!("{head}.from"))
            .collect()
    }

    /// An unsettled method name reaches every head that implements it.
    fn targets(&self, key: &str) -> Vec<Name> {
        let mut targets: Vec<_> = self
            .bodies
            .keys()
            .filter(|name| {
                if key.starts_with('.') {
                    name.ends_with(key)
                } else {
                    name.as_str() == key
                }
            })
            .cloned()
            .collect();
        targets.sort();
        targets
    }

    /// The witness of the first effect `e` reaches in source order, or `None`
    /// if `e` is pure. Empty for an effect of `e`'s own form; otherwise the
    /// names called through, ending at the impure native or queried relation.
    fn effect(&self, e: &Expr, scope: &PurityScope, path: &[Name]) -> Option<Vec<Name>> {
        match e {
            Expr::Unary(UnOp::Ref | UnOp::Deref, ..)
            | Expr::Assign(..)
            | Expr::While(..)
            | Expr::For(..)
            | Expr::ForQuery(..)
            | Expr::Relation(Rel::Add(_) | Rel::Clear(_) | Rel::Solutions(_), _) => Some(vec![]),
            Expr::Relation(Rel::Query(q), _) => Some(vec![q.name.clone()]),
            Expr::Var(x, _) => self.mention(x, scope, path),
            Expr::Call(callee, args, _) => {
                let first = match &**callee {
                    Expr::Var(f, _) => self.call(f, args, scope, path),
                    Expr::Lambda(..) => Some(vec![]),
                    other => Some(self.effect(other, scope, path).unwrap_or_default()),
                };
                first.or_else(|| args.iter().find_map(|a| self.effect(a, scope, path)))
            }
            Expr::Method(recv, m, args, _) => self
                .effect(recv, scope, path)
                .or_else(|| self.through(&self.method_key(recv, m, scope), path))
                .or_else(|| args.iter().find_map(|a| self.effect(a, scope, path))),
            Expr::Try(inner, _) => self.effect(inner, scope, path).or_else(|| {
                self.conversions()
                    .iter()
                    .find_map(|key| self.through(key, path))
            }),
            _ => subexprs(e)
                .into_iter()
                .find_map(|c| self.effect(c, scope, path)),
        }
    }

    /// `key` followed by its witness, if `key` is impure.
    fn through(&self, key: &str, path: &[Name]) -> Option<Vec<Name>> {
        for target in self.targets(key) {
            if !self.impure.contains_key(&target) || path.contains(&target) {
                continue;
            }
            let mut next_path = path.to_vec();
            next_path.push(target.clone());
            if let Some(witness) = self.bodies[&target]
                .iter()
                .find_map(|body| self.effect(body.expr, &body.scope, &next_path))
            {
                let mut witness = witness;
                witness.insert(0, key.to_string());
                return Some(witness);
            }
        }
        None
    }

    /// The effect of naming `x` as a value: a function counts as called, and
    /// an impure native is an effect.
    fn mention(&self, x: &str, scope: &PurityScope, path: &[Name]) -> Option<Vec<Name>> {
        if scope.locals.contains(x) {
            return None;
        }
        match self.program.decls.get(x) {
            Some(Decl::Fn(..)) => self.through(x, path),
            Some(_) => None,
            None if impure_native(x) => Some(vec![x.to_string()]),
            None => None,
        }
    }

    /// The effect of calling `f`, judged by what `f` names; excludes the
    /// arguments' own effects.
    fn call(
        &self,
        f: &str,
        args: &[Expr],
        scope: &PurityScope,
        path: &[Name],
    ) -> Option<Vec<Name>> {
        let one = || Some(vec![f.to_string()]);
        if scope.locals.contains(f) {
            return one();
        }
        match self.program.decls.get(f) {
            Some(Decl::Fn(..)) => self.through(f, path),
            Some(_) => one(),
            None if impure_native(f) => one(),
            None if is_native(f) => {
                let callback = callback_index(f).and_then(|i| args.get(i))?;
                match callback {
                    Expr::Lambda(..) => None,
                    Expr::Var(g, _) if !scope.locals.contains(g) => match self.program.decls.get(g)
                    {
                        Some(Decl::Fn(..)) => None,
                        None if is_native(g) && !impure_native(g) => None,
                        _ => Some(vec![g.clone()]),
                    },
                    Expr::Var(g, _) => Some(vec![g.clone()]),
                    _ => Some(vec![]),
                }
            }
            None => one(),
        }
    }

    /// The callables `e` reaches transitively, in the order first met.
    fn reached(&self, e: &Expr, scope: &PurityScope) -> Vec<Name> {
        let mut out = Vec::new();
        self.refs(e, scope, &mut out);
        self.follow_calls(&mut out);
        out
    }

    /// Appends to `out` each callable `e` refers to directly, once.
    fn refs(&self, e: &Expr, scope: &PurityScope, out: &mut Vec<Name>) {
        let mut push = |key: String| {
            for target in self.targets(&key) {
                if !out.contains(&target) {
                    out.push(target);
                }
            }
        };
        match e {
            Expr::Var(x, _) if !scope.locals.contains(x) => {
                if matches!(self.program.decls.get(x), Some(Decl::Fn(..))) {
                    push(x.clone());
                }
            }
            Expr::Method(recv, m, _, _) => push(self.method_key(recv, m, scope)),
            Expr::Try(..) => {
                for key in self.conversions() {
                    push(key);
                }
            }
            _ => {}
        }
        for c in subexprs(e) {
            self.refs(c, scope, out);
        }
    }

    /// Whether `key` takes a function-typed parameter.
    fn higher_order(&self, key: &str) -> bool {
        self.bodies[key]
            .iter()
            .any(|b| !b.trusted && b.higher_order)
    }

    /// Whether `key` can reach itself.
    fn recursive(&self, key: &str) -> bool {
        if self.bodies[key].iter().all(|b| b.trusted) {
            return false;
        }
        let mut reached = self.calls[key].clone();
        self.follow_calls(&mut reached);
        reached.iter().any(|name| name == key)
    }

    fn follow_calls(&self, reached: &mut Vec<Name>) {
        let mut i = 0;
        while i < reached.len() {
            for next in &self.calls[&reached[i]] {
                if !reached.contains(next) {
                    reached.push(next.clone());
                }
            }
            i += 1;
        }
    }
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
