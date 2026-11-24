# Milestone 6 Description
## Concept Questions
> `solutions uses("app", ?m)` in `deps.brg` (from above) is `["gfx", "io", "net", "ui"]`. Using your engine, explain how `uses("app", "io")` gets
> derived: which round of your fixpoint first produces it, which rule fires, and what substitution your `unify` builds for each generator. How does
> your loop decide that it has reached the fixpoint? Why does the same loop terminate on a graph with a cycle, such as an extra fact
> `needs("io", "app")`?

My `least_fixpoint` in [`engine.rs`](src/relations/engine.rs) is semi-naive: it starts with the four `needs` facts as both `known` and `delta`.
In round 1, `rule uses(a, b) :- needs(a, b);` copies them into `uses`. In round 2, `rule uses(a, c) :- needs(a, b) and uses(b, c);` fires with
`uses(b, c)` reading only round 1's new facts. `unify` matches `needs(a, b)` against `("app", "net")` to build `{a ↦ "app", b ↦ "net"}`, then
matches `uses(b, c)` against `("net", "io")`, which agrees on `b` and adds `c ↦ "io"`, so the head gives `uses("app", "io")`.
At the end of each round, my `least_fixpoint` loop calls `known.add` (`RelationDb::add`) on each derived tuple. It returns `true` only when
the tuple is new, so only a new tuple sets `changed` to true. If none are new, `changed` stays false and the loop stops. This also makes
`least_fixpoint` terminate with a cycle: these rules only copy values already in facts, and the five strings allow at most 25 `uses` tuples.
Since `known` stores a set, deriving an existing tuple again does not count as a change.

> `solutions needs(?a, ?)` is `["app", "net", "ui"]`, three values from four facts. Point at where your engine cuts each match down to the named holes,
> removes duplicates, and sorts. Why must the anonymous hole be cut away *before* duplicates are removed? Why does each `?` need a fresh variable
> name, and what would `solutions needs(?, ?)` return if your engine gave every anonymous hole the same name?

In `solutions`, `named_holes` lists only named holes. The `filter_map`/`map` over the facts keeps just those holes' values from each match,
`sort_by(compare_rows)` sorts with the provided `compare`, and `dedup_by` removes adjacent equal rows. `needs("app", "ui")` and `needs("app", "net")`
differ only at the anonymous position, so if that value were kept, they would be two different rows and `"app"` would appear twice. `unify` treats
repeated variable names as one variable that must agree, so each `?` gets its own name, `?{i}`, from its position. If all `?` shared a name,
`needs(?, ?)` would only match facts with equal columns; `deps.brg` has none, so it would return `[]` instead of `[()]`.

> `rule leaf(a) :- size(a, n) and m > cap;` is `Unbound (m)`, but `n > cap` is accepted, and so is `{ let m = n * 2; m > cap }`. Walk through your
> `check_range_restriction` on all three: which names `free_vars` gives for each filter, and which test lets each name through or rejects it. Why
> does the language insist that every *head* variable be bound by a generator? What would a rule like `rule uses(a, c) :- needs(a, b);` have to
> mean if it were allowed?

My `check_range_restriction` in [`check.rs`](src/relations/check.rs) takes the generator-bound set from `generator_vars`, here `{a, n}`. A name
passes if it is in that set or `top_level` accepts it (a global, function, or native). For `m > cap`, `free_vars` gives `[m, cap]`; `m` is
neither, so it is `Unbound (m)` at the filter. For `n > cap` it gives `[n, cap]`: `n` is generator-bound and `cap` is a global. For the block it
also gives `[n, cap]`, because the `let` binds `m` inside the filter, so `free_vars` leaves it out. Head variables are checked first and only
against the generator set. Head variables get their values from generator facts; head literals are also allowed. `uses(a, c) :- needs(a, b)` would
mean `a` uses *every* string `c`, an infinite relation the engine could not list.

> `hops.brg` (above) is rejected as `Recursive`, although `hops(2)` always returns. Show where your `check_pure` finds the cycle and why it reports
> `Recursive` rather than `Impure`. Then, for the filter `note(a)`, where `note` calls `println`, explain how your code builds the witness
> `[note, println]`, and how it computes the impure set `I` as a least fixpoint over the program's functions.

For `hops(2)`, `check_pure` runs three checks in order. `reached` finds `[hops]`. No reached function takes a function parameter. `effect` finds
nothing, because the body of `hops` only compares, branches, and calls `hops`, which is not in `I`. Then `recursive("hops")` follows the calls
in the body of `hops` (from `refs`) back to `hops`. Recursion is not an effect, since `hops` reads and writes nothing; the issue is termination.
The check uses only the call graph, not argument values, so it cannot tell that `hops(2)` stops. `Purity::new` computes `I`: starting empty, each
round runs `effect` on every function body not yet in `I`, adding any that reaches an effect with its witness, until a round adds nothing. For
`note`, the call to `println` gives `["println"]`. In the filter, `call` finds that `note` is a top-level function, and `through` prepends its name:
`[note, println]`.

> The purity check already rejects every filter that queries, yet your engine also keeps a `materializing` flag. Point at where you set and clear it
> in `solutions`, and explain why it must be cleared before an error from the rounds is returned. Using the textbook's `p`/`q`/`r` program from the
> chapter's design problems, describe what your engine would do, run without the checks, if the flag were not there.

`solutions` sets `self.materializing = true` immediately before `least_fixpoint`, clears it right after, and only then applies `result?`. An
interpreter can keep being used after a stuck run (a test calls `eval_program` again after another `load_program`), so a flag left set would make
every later query, `add`, or `clear` fail with `QueryInFilter`. In the `p`/`q`/`r` program, `solutions p(?x)` fires `p`'s rule, whose filter
`not r(x)` asks the query `r(x)`. Without the flag, that query would call `solutions`, find no stored closure, start another fixpoint, fire `p`'s
rule again, and repeat until Rust overflows the stack. With the flag, `solutions` stops at `r(x)` with `QueryInFilter`.

## How you implemented it

> Walk through your `solutions` from start to finish: how you turn the query's arguments into terms, how you compute the fixpoint (the starting
> facts, one round, and firing one rule through its generators and filters), and how you build the answer. Say how your `Subst::unify` handles a
> variable already bound, and how it leaves the original substitution unchanged on failure. Naming the provided tools you used (`RelationDb`,
> `Subst`, `compare`, `type_of`, `env.root()`, `Control`) is encouraged.

`solutions` first checks `materializing`, then `relation_arity` checks that the name looks up to a relation in `env` and returns its column count.
It evaluates arguments once from left to right: expressions become `Term::Val`, named holes `Term::Var(x)`, and each anonymous hole a fresh
`Term::Var`. Only after that does it check the count (`ArityMismatch`). If `self.db` has no stored closure, `least_fixpoint` copies the dynamic
facts into two `RelationDb` sets, `known` and `delta`. Each round, `fire` runs every rule once per generator, with that generator reading `delta`
and the others reading `known`. Rules without generators fire only in round 1; bodiless rules supply the permanent base facts this way.
The facts actually added become the next `delta`. `fire` starts with one empty `Subst` and joins all generators in body order through `unify`.
For each resulting substitution, it evaluates the filters in body order in `env.root()` with the bindings, stopping at the first `false`.
A non-`Bool` result gives a `TypeError` using `type_of`, and a `Control::Return` gives
`ReturnOutsideFunction`. `instantiate_head` builds the head tuples. The closure is saved with `set_derived`, and the answer is matched, cut, sorted
with `compare`, and deduplicated as described above. `Subst::unify` returns `None` on a length mismatch, then works on `self.clone()`: a constant
must equal the fact, an already-bound variable's value must equal it, and an unbound variable is bound in the copy. A failure returns `None` early,
and since only the copy changes, `self` is untouched.

> Describe how your `check_pure` decides what a call reaches: how you tell a local from a top-level function or a native, how you treat `map`,
> `filter`, and `fold` callbacks, and which of the provided helpers (`subexprs`, `free_vars`, `bound_names`) you used and where.

A filter's locals are the generator variables plus `bound_names` from every conjunct. A function's locals are its parameters plus `bound_names(body)`. In
`call`, a callee in the locals is a local and an effect (`[name]`), even if a function has the same name. Otherwise, a `Decl::Fn` is impure if
it is in `I`; a relation or global is an effect; an impure native (`print`, `println`, `to_string`, `read_*`) is an effect; and other natives are
pure. For `map`/`filter`/`fold`, `callback_index` finds the callback, which must be a lambda, a top-level function (judged as a mention), or a pure
native. An invalid named callback gives its name as the witness; a computed callback gives an empty witness. `subexprs` drives the `effect` and
`refs` walks, `free_vars` drives range restriction, and
`bound_names` builds the local sets.

> Point out anything that was tricky, a bug you fixed, or a design choice you made. If you used an assistant, say what you had it do and how you
> checked its work.

My first naive fixpoint took about 16 seconds on the 150-edge transitive-closure test, so I made it semi-naive, which derives the same facts and
runs the suite in under a second. Two other choices: a closure computed for one query is cached until the next `add` or `clear`; and the rules
are cloned before the loop, because firing a filter needs `&mut self`. Clearing `materializing` before `?` was easy to get wrong. I followed the
M6 page for range restriction: only generators bind head variables. Signed integers such as `-1` already parse as literals, so generator
arguments need no special negation case. Method calls in filters conservatively reach every impl of that name. I used Claude Code to explain
`unify`, query arguments, rule scoping, and the design questions. At my request, it wrote most of the code: `unify`, the engine, the evaluator and
type checker arms, and the rule checks. I checked it with `cargo m6` (all tests pass), by running `deps.brg`, `hops.brg`, and
`tests/programs/d_relations.brg` against the expected output, and by asking it why each part works the way it does.
