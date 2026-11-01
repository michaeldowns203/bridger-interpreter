# Milestone 5 Description
## Concept Questions
> Under `--features m4`, `late.brg` (above) prints `start` and then stops at the whole assignment; under `--features m5` it prints nothing and
> reports `total`, with *expected ref<_>, found Int*. Using your `Assign` arm and your `unify`, explain where the `ref<_>` comes from, why the error
> lands on `total` rather than on the whole assignment, and why `expected` and `found` come out in that order, not the reverse.

My `Assign` arm in [`check.rs`](src/types/check.rs) creates a fresh inference variable, assigns it to `t`, and checks the left-hand side of the assignment against `Ty::reference(t.clone())`,
which produces the expected `ref<_>`. The `Var` arm finds `total`'s `Int` type and calls `finish_expr`, which invokes `unify` at the variable’s span, so the error points at `total`.
My `unify` takes the found type first and the expected type second, then puts them into the corresponding error fields. M5 checks the program before
evaluation, so the error prevents `start` from being printed.

> `[] ++ [true]` has type `[Bool]`, but `[] ++ []` is `Ambiguous`. Trace both through your concatenation arm: what type the left operand
> synthesizes, how the right operand is checked, and what type remains afterward. For `[] ++ []`, is it your concatenation arm or the driver's
> determination rule that reports `Ambiguous` (and when does the other one fire)? Why does a type have to be *recorded* for the determination rule to
> judge it?

My concatenation arm first infers `[α]` for the empty left list, then checks the right operand against that type. In `[] ++ [true]`, checking `true`
solves `α` as `Bool`, giving `[Bool]`; with two empty lists, nothing solves it, so the result remains `[α]`. My arm accepts that list shape, but
`require_resolved` in [`mod.rs`](src/types/mod.rs) reports `Ambiguous` after the declaration is checked because the element type is still unknown.
The concatenation arm itself reports `Ambiguous` when the entire concatenation type is still an unsolved variable. `require_resolved` does not walk
the expressions again: it checks the spans and types saved by `record`, which my `finish_expr` helper calls. Without recording an expression's type,
that expression would be absent from this check, so its unresolved type could be missed.

> In one body, `id(1)` and `id("a")` both check for a generic `fn id<T>(x: T) -> T`, but in `|f| (f(1), f("a"))` the second call is rejected.
> Point at the place in your `Var` arm where a type parameter becomes an inference variable, and explain why the first program checks. What would
> go wrong if that variable were made once per declaration instead of once per use? Why does the lambda's parameter `f` not get the same
> treatment?

In my `Var` arm, `.map(|param| (param.name.clone(), self.fresh_meta()))` gives each generic parameter a fresh inference variable on every lookup
of a declared function, and `sig.substitute` replaces its occurrences. The two uses of `id` can therefore independently infer `Int` and `String`;
one variable shared across the declaration would incorrectly force them to agree. The lambda parameter `f` instead comes from `ctx.lookup` with one
shared type: `f(1)` constrains its input to `Int`, so `f("a")` fails.

> `{ let f = |x| x(x); () }` is `InfiniteType`. Walk through what your `Lambda` and `Call` arms ask `unify` to do for `x(x)`, and show where
> your occurs check fires. What would happen in your `unify` (and later, in `resolve`) if you left the occurs check out?

My `Lambda` arm gives `x` a fresh inference variable, say `α`. In `x(x)`, my `Call` arm sees an unknown callee, infers `α` for the argument, creates
a fresh result `β`, and asks `unify` to equate `α` with `fn(α) -> β`. The local `occurs` helper finds `α` inside that function's parameter
types and returns `true`, so `unify` returns `InfiniteType` before `solve` runs. Without this check, `unify` would store a cyclic solution, and `resolve` would repeatedly
expand the same variable until the stack overflowed.

> `fn f() -> Int { return 1; let y = []; println(y); 2 }` checks, although nothing fixes the element type of `y`, while `fn f() -> Int {
> return 1; 1 + true }` is rejected. Using your `Block` arm, explain where you call `dead_after`, why that call has to come *before* the remaining
> statements are checked, and why the second program is still an error.

After checking each statement, my `Block` arm detects the first diverging expression and calls `dead_after(at, *span)` before continuing
the loop. This marks the remaining code unreachable before its expressions are checked. Marking dead code early also matters for expressions such
as tuple projection, whose `undetermined` helper consults `in_dead_code` during checking: without the mark, it could report `Ambiguous` immediately,
before a later call to `dead_after` could help. In the example above, the driver's later determination and bound checks skip the unreachable code,
allowing `y`'s element type to remain unknown in the first
program. Unreachable code is still checked for concrete type mismatches: the arithmetic arm checks `true` against `Int`, so `1 + true` still fails.

## How you implemented it

> Walk through your `Expr::Call` arm and your `unify` from start to finish. For `Call`: how you get the callee's type, the three cases it can be in (a
> function type, an unsolved variable, anything else), how you check the arguments, and what `finish_call` does with the callee's bounds. For
> `unify`: the order of your cases and how you report the innermost disagreement inside compound types. Naming the provided tools you used
> (`check_callee`, `fresh_meta`, `resolve`, `record`, `Ty::func`, `TyError`, `?`) is encouraged.

My `Call` arm uses `check_callee` to obtain the resolved type and the range of bounds created for the callee. A function type requires matching arity,
otherwise producing `ArityMismatch` at the whole call. With matching arity, it checks arguments against parameters from left to right.
`finish_call` moves each bound's error span to the first argument whose corresponding parameter type contains the constrained type, or to the whole
call if no parameter does. It updates diagnostic spans; the driver checks the bounds later. For an unsolved callee, I infer argument types, create
a result with `fresh_meta`, and unify the callee with the `Ty::func` built from them; anything else produces `NotAFunction` at the callee.
Finally, `finish_expr` checks the result against `expected`, resolves it, records it, and returns it, using `?` to propagate failures.

My `unify` resolves both inputs first and succeeds immediately if they are equal. Next it handles an inference variable on either side, rejecting an
occurrence inside its proposed solution before calling `solve`. Otherwise, it recursively unifies matching lists, references, tuples, functions, or named
types, checking widths, arities, and names where needed. Recursive calls preserve found/expected order and propagate their errors, so an inner mismatch
is reported directly; incompatible outer shapes produce `Mismatch` with the resolved inputs and supplied span.
For example, unifying `[Int]` with `[Bool]` reports found `Int`, expected `Bool`, while preserving the span supplied to the outer call.

> Describe how your `check_expr` enforces the nesting bound and keeps `self.depth` balanced when an arm fails, and whether you factored the
> shared ending of every arm (Chk-Sub, `resolve`, `record`) into a method of your own.

My `check_expr` returns `TooDeep` when `self.depth >= MAX_NESTING`; otherwise, it increments the counter and saves the result of
`check_expr_inner` without applying `?`. It then decrements the counter and returns that result, so both success and error paths balance the depth.
I moved the expression match into `check_expr_inner` and extracted the shared expected-type check, resolution, and recording into `finish_expr`, which each completed arm calls.

> Point out anything that was tricky, a bug you fixed, or a design choice you made — and if you used an assistant, say what you had it do and how
> you checked its work.

The generic handling in my `Var` arm was tricky, especially keeping track of what the different `params` and `args` represent. `generics.params`
contains type parameters like `T`, while the function's `params` contains value parameters and their declared types. A trait bound's `args` contains
types, unlike a function call's `args`, which contains expressions to check. Understanding substitution meant tracing how the map from a name like
`T` to an inference variable replaces occurrences inside larger types, such as `[T]`, as well as in the return type and trait-bound arguments.
I also had to distinguish substituting those bound arguments from passing the substituted type parameter itself to `require_trait` as the type that
must satisfy the bound. Finally, I needed to understand why the generic and signature data is cloned before calling `fresh_meta`: the declaration
is borrowed from the checker, but allocating inference variables requires a mutable borrow.

I used Codex to help when I got stuck, explain Rust syntax and ownership, and review my implementation. At my request, it implemented individual
arms and made focused changes, including extracting `finish_expr` and adding the nesting guard. I checked its explanations and changes by asking
follow-up questions about the code and the reasons for each step, including generic substitution, resolving inference variables, and the occurs check.
