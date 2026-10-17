# Milestone 4 Description
## Concept Questions
> In `{ let y = 1; let f = |x| x + y; let y = 100; f(0) }` the result is `1`, not `101`. Walk through what your `Expr::Lambda` arm stores in
> the closure, which environment your `Expr::Call` arm extends with the parameter `x`, and why that gives `1`. What would the result be if your `Call`
> arm extended the *caller's* environment instead, and what is the name for the scoping discipline your interpreter implements?

My `Expr::Lambda` arm in [`eval.rs`](src/interp/eval.rs) stores the parameter names, a cloned body, and a clone of the current environment in a
`Closure::Bridger`. Here, that environment contains `y = 1`. The later `let y = 100` creates a new binding without changing the environment the
closure captured. My `Expr::Call` arm extends the captured environment with `x = 0`, so the body evaluates `0 + 1` and returns `1`. Extending the
caller's environment instead would produce `100`, since the caller's nearest binding is `y = 100`. My interpreter implements static, or lexical, scope.

> Your `Call` arm evaluates the operator, the arguments, and checks the arity, in some order. Say the order your code uses, and use it to explain why
> `5(print(1))` is stuck with `NotAFunction` *without* printing anything, while `(|x, y| 0)(print(1))` prints `1` and then is stuck with
> `ArityMismatch`. Which span do both errors carry?

My call arm evaluates the operator first and checks that it is a `Value::Closure`. It then evaluates the arguments from left to right in the caller's
environment using `eval_elements`, and only afterward checks the argument count for a Bridger closure. In `5(print(1))`, the operator evaluates to an
integer, so `NotAFunction` is raised before `print(1)` runs. In `(|x, y| 0)(print(1))`, the operator is a closure, so the argument prints `1` before
the arity check finds one argument for two parameters and raises `ArityMismatch`. Both errors carry the span of the whole call expression.

> At M3, nothing you wrote caught `Control::Return`. Now your `Call` arm does. Show how your arm turns `Err(Control::Return(v))` into the
> call's value while letting a `Control::Raise` through, and explain why you must not apply `?` to the body's result before calling `leave_call`. What
> two things would go wrong if you did?

After `enter_call` succeeds, I save the body's evaluation result in `outcome` without applying `?`, then call `leave_call`. I match on `outcome`:
`Ok(value)` remains successful, `Err(Control::Return(value))` becomes `Ok(value)`, and `Control::Raise(error)` is propagated through
`Err(Control::from(error))`. This makes a return stop at the current call boundary. Using `?` on the body's result would skip `leave_call` on either
error channel, leaving the call-depth count too high. It would also propagate `Control::Return` out of the call instead of catching it as the call's value.

> `fold(range(0, 1000000), 0, |a, x| a + x)` runs to completion, while the recursive `sum_to(1000000)` is a `StackOverflow`, even though
> both call a Bridger function a million times. Explain the difference in terms of how many calls are *in progress at once* and what your
> `enter_call`/`leave_call` pair counts. How does `fold`'s callback reach your `Call` arm at all, given that `fold` is a native?

The provided `fold` implementation uses a loop, completing each callback before starting the next one. A million callback calls therefore do not mean
a million calls are active at once. Recursive `sum_to` starts another call before its current call finishes, so its active calls accumulate until
`enter_call` rejects a call at the limit of 100,000. My `enter_call`/`leave_call` pair counts active Bridger calls, not the total calls made over time.
The native `fold` invokes the provided `self.apply` helper, which binds the callback and its argument values in a temporary environment, builds an
`Expr::Call`, and passes it to `self.eval_expr`. Each callback therefore goes through my ordinary call arm and its depth accounting.

> A top-level `fn fact` can call itself, but `let fact = |n| if n == 0 { 1 } else { n * fact(n - 1) };` inside `main` is stuck with an unbound
> variable. Using what your `Lambda` arm captures and what the provided driver does for top-level functions, explain why the two behave differently.

For the local `let`, my block arm evaluates the right-hand side before extending the environment with `fact`. The lambda therefore captures an
environment that does not yet contain its own name. Adding `fact` to a new child environment afterward does not add it to the closure's captured
environment, so a recursive call from its body cannot find that binding. The provided driver handles top-level functions differently: `eval_program`
uses `env.add_function` to create closures over a shared root environment and install their names into that same root. Once the functions run, that
root contains their own bindings and the bindings of the other top-level functions, allowing recursion and mutual recursion.

## How you implemented it

> Walk through your `Expr::Call` arm from start to finish: how you destructure it, how you evaluate the operator and arguments, how you dispatch on
> `Closure::Bridger` versus `Closure::Native`, how you build the body's environment, and how you handle the body's result. Then describe your
> `Expr::Lambda` arm in a sentence or two. Naming the provided tools you used (`self.eval_expr`, `env.extend`, `enter_call`, `leave_call`,
> `eval_prelude`, `type_of`, `RuntimeError`, `.into()`/`?`) is encouraged.

I destructure `Expr::Call` into `operator`, `args`, and `span`, then evaluate the operator with `self.eval_expr(operator, env)?`. A non-closure
produces `NotAFunction`, using `type_of` for the found type and the call's span. For a closure, I evaluate the arguments with `eval_elements` in the
caller's environment and match on `closure.as_ref()`. The native branch passes the builtin ID, argument values, and span to `eval_prelude`, then
converts a runtime error into `Control::Raise` with `map_err`.

The Bridger branch checks the argument count against `params.len()` and returns `ArityMismatch` if they differ. Otherwise, I clone `captured_env`
into `local_env`, pair parameter names with argument values using `zip`, and repeatedly assign the result of `local_env.extend` back to `local_env`.
I then call `enter_call`, evaluate the body in `&local_env`, save its result, and call `leave_call`. Finally, I preserve a successful value, catch a
`Control::Return` as a successful call result, or propagate a `Control::Raise`.

My lambda arm collects cloned parameter names, clones the body and environment, and wraps the resulting `Closure::Bridger` in `Rc::from` and
`Value::Closure`, returning it with `Ok`. It does not evaluate the body, and it does not retain the parameter type annotations in the runtime closure.

> Say what, if anything, you changed in your M1–M3 arms for this milestone — for example, to make `==` on a function stuck, or to fix an evaluation-order 
> problem a whole-program test exposed — and why.

I changed the M1 equality and inequality handling to share a `BinOp::Eq | BinOp::Ne` branch that calls my `expect_comparable` helper on both
operands before comparing them. The helper borrows each value and calls the provided `uncomparable` function, which checks for uncomparable
components, including functions nested inside tuples or lists. If it returns `Some(found)`, I raise `NotComparable` using that type and the binary
expression's span; `None` means the check passed. This prevents Rust's closure pointer comparison from being used as Bridger's function equality.

I also reused `expect_list` for the tail of `BinOp::Cons`, added `expect_ref` to share reference validation between dereference and assignment,
and used `ok_or_else` to convert a missing variable lookup into `UnboundVariable`. These cleanups preserve the existing behavior: operands evaluate
left to right, and assignment validates its target before evaluating its right-hand side.

> Point out anything that was tricky, a bug you fixed, or a design choice you made — and if you used an assistant, say what you had it do and how
> you checked its work.

One bug was that my original comparability helper only matched a direct `Value::Closure`. It rejected comparing functions directly, but allowed
tuples or lists containing functions to reach Rust's equality comparison. I fixed this by using the provided `uncomparable` helper, which searches
inside compound values and returns the type of an uncomparable component. My `expect_comparable` helper now turns that result into `NotComparable`
and uses the returned type for `found`, rather than the type of the enclosing tuple or list.

I used Codex to help when I got stuck, explain Rust syntax and ownership, and review my implementation. It pointed out the missing nested-function
check and showed me where the assignment required it. Next time, I need to read the assignment description more carefully so I catch things like 
this the first time without the use of an AI assistant. It also suggested ways to use existing helpers and reduce duplicated code, such as reusing
`expect_list` and sharing reference validation through `expect_ref`. At my request, it made some focused code changes. I checked its explanations and changes
by asking follow-up questions about the code and the reasons for each change, including borrowing versus ownership and handling `Result<(), Control>`.