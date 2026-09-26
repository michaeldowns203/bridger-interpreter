# Milestone 1 Description
## Concept Questions
> What does it mean for an expression to be *stuck*, as opposed to evaluating to a value? Explain in terms of your method's return type: 
> what does `eval_expr` return in each case (the `Ok`/`Err` shape), and for a stuck expression, which `RuntimeError` variant and *expected/found* types does it carry?

`eval_expr` returns a `Result<Value, Control>`. In the `Ok` case, it returns `Ok(value)`, which represents the result of evaluating the expression. A stuck expression
cannot produce a value under the evaluation rules and returns `Err(Control::Raise(error))`. Specifically, it raises a `RuntimeError` variant that indicates 
the reason it is stuck. If the `RuntimeError` is mismatched types, it returns a `TypeError` that indicates the expected and found types. For M1, the expected types were 
usually `Bool` or `Int`. To derive the bad type, I used the `type_of` function, defined in [`value.rs`](src/interp/value.rs), on the bad `Value`. The `Mod` and `Div` 
expressions can also get stuck with a `DivByZero` `RuntimeError`.

> Walk through how the `?` operator behaves in one of your arms: when you write `self.eval_expr(sub, env)?`, what happens if that subexpression is stuck, and what does 
> it save you from writing by hand? What would the same arm look like without `?`?

The `?` operator is the same as writing a `match` over the `Result` type. If the subexpression is stuck, it immediately returns and propagates the `Err` to its caller. 
If it is successful, it unwraps `Ok(Value)` to a `Value` that can be used by the caller. There would be much more ceremony without this operator; I would have to write out the 
`match` for every branch at every level that could return an error:
```Rust
match self.eval_expr(expr, env) {
    Ok(value) => value,
    Err(control) => return Err(control)
}
```

> In your `and`/`or` implementation, how do you avoid evaluating the right operand once the left operand has already decided the answer? Point to the lines that do it, 
> name the Rust control flow you used, and say why you could *not* evaluate both operands first and then combine them.

Lines 56-68 of [`eval.rs`](src/interp/eval.rs) handle `and` and `or` operations. I used Rust's `&&` and `||` operators to perform the operations as they also short-circuit. 
I could not evaluate both operands first then combine them, as this would not short circuit invalid expressions. For example, if I evaluated first, `true` or `1/0` would 
throw a `DivByZero` error instead of evaluating to true.

> Why does your integer arithmetic *wrap* rather than overflow-panic, and which specific operations (or method calls) in your code produce that behavior?

My integer arithmetic wraps rather than overflow-panicking because Bridger defines integer operations using signed 64-bit wrapping arithmetic. I use Rust's `wrapping_neg`,
`wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_div`, and `wrapping_rem` to ensure that `Neg`, `Add`, `Sub`, `Mul`, `Div`, and `Mod` all produce wrapping arithmetic.

> When your code reports a stuck expression, which node's *span* does the error carry, and how does your code get that span? Why is blaming that node more useful to a user 
> than blaming, say, the whole expression?

When my code reports a stuck expression, the error carries its AST-node span. Pattern matching the `Expr` extracts the span, and I pass a copy of it to the runtime errors 
with `*span`. Blaming the node is more useful than blaming the expression because it makes the error visible, which makes it easier to fix. It would be much more challenging
to fix an error in a large, nested expression if the error only states that something went wrong *somewhere* within that expression rather than the exact node that caused the issue.

## How you implemented it
> Walk through your `Expr::Binary` arm: how do you evaluate the operands, dispatch on the `BinOp`, build the result value, and report a type error? Naming the provided tools 
> you used (`self.eval_expr`, `type_of`, the wrapping operations, `RuntimeError`, `.into()`/`?`) is encouraged.

I created a helper function, `eval_binary`, to reduce duplicated code across operations within the `Expr::Binary` arm. First, I evaluate the left operand with `self.eval_expr`. 
Then, I `match` over the operator, first performing `and` and `or` operations that require the right side to be evaluated only
if short-circuiting does not take place. Then, I use `_` to catch all other cases. I evaluate the right-hand side, as every non-short-circuiting operator needs both 
operands, and call `eval_binary`. First, `eval_binary` matches all arithmetic and integer-comparison cases. It calls another helper that matches over the `value`, returns `Ok` if the `value` is an 
`Int`, and throws a `TypeError` if it isn't. If both operands are integers, it checks whether the operator is `Div` or `Mod`. If it matches, it checks whether the right operand is 
0, and throws a `DivByZero` error if it is. Finally, it matches over the operation and performs the arithmetic with the validated integers, wrapping in results in `Ok(Value::Int)` or `Ok(Value::Bool)`. Then, I check `Eq` and `Ne`. These 
operators require valid operands of any type, so their logic is just the Rust comparison logic. Next, I handle `Concat`. First, I check whether both arguments are `Str`s, and use 
`format!` to concatenate them if so. Next, I check whether they are both `List`s, and use `List`'s `concat` method to concatenate them if so. Otherwise, I check whether the 
left operand is a `List` or `Str`, and report a `TypeError` on the right if it is. Finally, if nothing else was a match, the left operand was invalid, so throw a `TypeError`. 
I arbitrarily defined the expected type as `Str` in this case as the `TypeError.expected` field stores a single `Ty`, but really it could be a `List` or a `Str`. Last, I match `Cons` operator and use 
`List`'s `cons` function to perform it. If any branch of a helper falls through to an unreachable case, which should not be possible, I panic with `unreachable!`. I use `?` on every
`self.eval_expr` so that an invalid expression is propagated to the caller.

> Point out anything that was tricky, a bug you fixed, or a design choice you made — and if you used an assistant, say what you had it do and how you checked its work.

Understanding Rust's syntax was tricky at first. After I got that down, the short-circuiting gave me trouble. I was evaluating the right-hand operand before passing it to 
short-circuiting branch, which was causing it to fail for invalid right-hand operands. I fixed that bug. Once I completed M1, I realized that there was a lot of duplicated 
code. So, I had GPT-6 Astra refactor it for me. I verified that it performed the same and inquired about the new syntax it used. Once I felt I understood the refactored code, 
I was happy with the finished result.