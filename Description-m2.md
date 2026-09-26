# Milestone 2 Description
## Concept Questions
> What does `env.lookup(x)` return, and how does your `Expr::Var` arm turn each of its two outcomes into a result of `eval_expr`? For the stuck outcome, name the 
> `RuntimeError` variant you build, which fields it carries, and which node's span it blames.

`env.lookup(x)` returns an `Option<Value>`. This is either the bound value of `x` or `None` if `x` is not bound. If `env.lookup(x)` returns the bound value, `eval_expr` returns
`Ok(value)`. If `env.lookup(x)` returns `None`, then `eval_expr` returns an `Err(Control::Raise(RuntimeError::UnboundVariable { name: x.clone(), span: *span }))`, where `span` is
the unbound variable `x`'s span.

> Explain how your block arm threads the environment through its items. When you evaluate a `Stmt::Let`, in which environment do you evaluate its right-hand side, and what do
> you pass to the items that follow? Point to the lines where you call `env.extend`.

First, my block arm clones the environment and stores it in a mutable variable. When I evaluate a `Stmt::Let`, I evaluate its right-hand side in the current scope. Then, I call 
`local_env.extend` on line 115 of [`eval.rs`](src/interp/eval.rs) and set the mutable copy of the environment to this new child scope. I pass this child scope to the items that follow.

> `env.extend` returns a *new* `Env` and leaves the one it was called on untouched. Using that fact, explain why a name bound by a `let` inside a block is not in scope outside the
> block — refer to what happens to the block's environment when your arm returns.

When my arm returns, the block's environment is discarded. So, a name bound by a `let` inside a block is only present in the local environment, which extends but does not change the
caller's environment, for the duration of the block; then, the copy is discarded.

> In `{ let x = 1; let x = x + 1; x }` the second `let` *shadows* the first rather than changing it. Explain, in terms of what `extend` does, why this produces `2` and not a mutation of
> the original binding — and why M2's `let` could not build a counter whose value changes over time.

This produces `2` because a `let`'s right-hand side is evaluated in the current scope before it extends that scope to create a new child scope. So, `x+1` in the second let evaluates to `2`,
and `lookup(x)` returns the nearest binding of `x`, which holds `2`. The parent binding of `x`, `1`, still exists in the parent scope. `let` creates a new binding rather than updating an 
existing binding, so it could not build a counter whose value changes over time.

> When a block contains a stuck item — say `{ z; 1 }` with `z` unbound — the block is stuck and the tail `1` is never reached. Walk through how the `?` operator in your arm produces that:
> what it does when a sub-evaluation returns `Err(Control::Raise(..))`, and which node's span the reported error carries.

The `?` operator in my `Stmt::Let` and `Stmt::Expr` arms propagates any error returned by `self.eval_expr` to the caller. So, when a sub-evaluation returns `Err(Control::Raise(..))`, `?`
returns immediately from the block's evaluation with the unbound variable `z`'s span, meaning the tail `1` is never reached.

## How you implemented it
> Walk through your `Expr::Block` arm: how do you destructure it into its items and optional tail, iterate the items while carrying the growing environment, dispatch on `Stmt::Let`
> versus `Stmt::Expr`, and produce the block's value (including `Value::Unit` when there is no tail)? Naming the provided tools you used (`self.eval_expr`, `env.lookup`, `env.extend`,
> `RuntimeError`, `.into()`/`?`) is encouraged. Note that the `Option<Ty>` annotation on a `let` is ignored at this milestone.

First, my `Expr::Block` arm extracts the statements and the optional tail with `Expr::Block(stmts, tail, _)`. Then, it clones the current environment and stores it in a mutable variable.
Then, it iterates over each of the block's statements. For each statement, it checks whether that statement is a `Stmt::Let` or a `Stmt::Expr`. If it is a `Stmt::Let`, it ignores the optional
type annotation and evaluates the right-hand side of the expression in the current scope with `self.eval_expr` and uses `extend` to bind `name` to the evaluated right-hand side if that
evaluation succeeded. If it is a `Stmt::Expr`, it simply evaluates the expression in the current scope (again propagating any error this returns to the caller with `?`). After the statements 
have been evaluated, I perform a `match` over the tail. If it is `None`, I return `Ok(Value::Unit)`. If it is `Some(expr)`, I evaluate the expression in the new scope and return its value.

> Point out anything that was tricky, a bug you fixed, or a design choice you made — and if you used an assistant, say what you had it do and how you checked its work.

It was tricky to understand when to use `?` and when to wrap something in `Ok(..)`. The distinction was whether I needed to extract a value from a sub-evaluation or return a successful
value from the current evaluation. For example, inside `Stmt::Let`, I needed to use `?` because I needed to get the value from the sub-evaluation to pass to `extend`. Inside `Stmt::Expr`, `?`
ensures a failure stops the block; I discard the value. However, in the `match tail`, I just needed to return a `Result`. So, an error could be that result, meaning I did not need to use `?`.
However, in the `None` branch, I needed to use `Ok` to tell the caller that that specific result was not an error. I used GPT-6 Astra to give me starting points and for help with syntax.
I also used it to check my work. I checked its work by forcing it to explain every decision to me and how it relates to what is taught in the textbook. I also made sure I understood each piece 
of the code and that nothing was ambiguous or unclear to me.