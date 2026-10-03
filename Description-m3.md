# Milestone 3 Description
## Concept Questions
> Your `eval_expr` returns `Result<Value, Control>`, and a `return` travels as `Err(Control::Return(v))` — the same `Err` side an error uses.
> In your `Expr::Return` arm, how do you build that value, and why carry a `return` as an `Err` rather than an ordinary `Value`? How do the two
> channels — `Control::Return` and `Control::Raise` — stay distinct, and what catches `Control::Return` at this milestone?

My `Expr::Return` arm in [`eval.rs`](src/interp/eval.rs) evaluates its operand with `self.eval_expr(expr, env)?` and wraps the resulting value in
`Err(Control::Return(...))`. Using `Err` lets `?` propagate the return immediately through enclosing expressions instead of treating it as an ordinary value.
`Control::Return` carries a returned value, while `Control::Raise` carries a runtime error. No evaluator arm catches `Control::Return` yet.

> Walk through your assignment arm `e1 := e2`: in what order do you evaluate the two sides, which one must be a `Value::Ref(loc)`, which
> `self.store` operation you call, and what value the form returns. For the stuck case — assigning to something that is not a reference — name the
> `RuntimeError` variant you build and how you form the expected type.

My assignment arm evaluates the left side first and requires `Value::Ref(loc)`. Only then does it evaluate the right side, call
`self.store.write(loc, value)`, and return `Ok(Value::Unit)`. Each operand evaluation uses `?` to propagate an early exit. For a non-reference target,
my `type_error` helper constructs `Control::Raise(RuntimeError::TypeError { ... })`, using `Ty::reference(Ty::unit())` as the expected type,
`type_of` for the actual type, and the assignment's span.

> The Mutation chapter's rules thread a store *in* and a store *out*, yet your interpreter keeps one `self.store` and mutates it in place. Explain, using
> `let a = ref 1; let b = a; b := 9; deref a` ⇒ `9`, why aliasing works: what `ref` allocated, what `b = a` copied, and why writing through `b`
> is visible through `a`.

`ref 1` allocates a fresh cell containing `1`, and `a` holds that cell's location. Binding `b` to `a` copies the reference value, not the cell,
so both names refer to the same location. `b := 9` changes that cell's contents, and `deref a` therefore reads `9`. The rules describe the store before 
and after the write; my interpreter implements this by updating the cell in `self.store`, while `a` and `b` remain bound to the same location.

> Your `while` arm is a host `loop` and your `for` arm walks a list. For each, say what value the body produces and what you do with it, what the loop
> as a whole evaluates to, and — for `for` — how `env.extend(x, item)` gives the loop variable a fresh binding each turn. Then explain how a
> `return` inside either body escapes the loop, referring to the `?` in your arm.

Each body evaluation can produce a value, but both loop arms discard successful body values and return `Ok(Value::Unit)` when they finish normally.
In `for`, `env.extend(name.clone(), item.clone())` creates a fresh child environment from the original environment each iteration, so the loop variable
is local to that iteration. Both arms use `?` on body evaluation: if it returns `Err(Control::Return(v))`, evaluation immediately exits the loop's arm
with that same result, skipping remaining iterations.

> In `if 3 { 1 } else { 2 }` the condition is not a `Bool`, and the program is stuck. Walk through how your `Expr::If` arm produces that, and
> contrast it with `if false { 9 }`, which is not stuck. Which branches does your arm evaluate in each case, and what does an else-less `if` return
> when its condition is false?

For `if 3 { 1 } else { 2 }`, my arm evaluates the condition to `Value::Int(3)`, then `expect_bool` produces a `TypeError` expecting `Bool` and finding
`Int`, at the `if` expression's span. The `?` propagates it before either branch executes. For `if false { 9 }`, the condition passes the Boolean check,
the then-branch is skipped, and the absent else-branch produces `Ok(Value::Unit)`. Neither example evaluates a branch, but only the first is stuck.

## How you implemented it

> Walk through one of your loop arms (`Expr::While` or `Expr::For`): how you destructure it, how you re-evaluate the condition or iterate the list,
> where you take the body's value with `?` and drop it, and how you produce `Value::Unit`. Then describe the two new cases you added inside
> `Expr::Unary` for `UnOp::Ref` and `UnOp::Deref`. Naming the provided tools you used (`self.eval_expr`, `self.store.alloc`/`read`/`write`,
> `env.extend`, `RuntimeError`, `Ty::reference`, `.into()`/`?`) is encouraged.

My `Expr::While(cond, body, span)` arm extracts the condition, body, and span. Then, inside a Rust `loop`, it reevaluates the condition and checks
it with `expect_bool`. A false condition exits with `break Ok(Value::Unit)`; otherwise, `self.eval_expr(body, env)?;` propagates early exits and discards
the successful body value before the next iteration.

For `UnOp::Ref`, I evaluate the operand first, then pass its value to `self.store.alloc` and wrap the fresh location in `Ok(Value::Ref(...))`.
For `UnOp::Deref`, I evaluate the operand and match its value: a reference is read with `self.store.read(loc)`, while a non-reference produces a
`TypeError` expecting `Ty::reference(Ty::unit())` at the dereference's span. Both operand evaluations use `?`.

> Point out anything that was tricky, a bug you fixed, or a design choice you made — and if you used an assistant, say what you had it do and how
> you checked its work.

On my first iteration of the `Expr::While` arm, I placed the condition outside the `loop`. This meant that a change to the condition would never cause
the loop to exit. I fixed this by moving the condition inside the `loop` and re-evaluating it on each iteration. I used GPT-6 Astra to supply an initial
skeleton for the code. Then, if I got stuck, I asked it for help with the problem I was facing. Finally, I asked it explain any portions of the code or 
concepts I did not understand.