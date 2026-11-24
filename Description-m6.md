# Milestone 6 Description
## Concept Questions
> `solutions uses("app", ?m)` in `deps.brg` (from above) is `["gfx", "io", "net", "ui"]`. Using your engine, explain how `uses("app", "io")` gets
> derived: which round of your fixpoint first produces it, which rule fires, and what substitution your `unify` builds for each generator. How does
> your loop decide that it has reached the fixpoint? Why does the same loop terminate on a graph with a cycle, such as an extra fact
> `needs("io", "app")`?

My `least_fixpoint` in [`engine.rs`](src/relations/engine.rs) starts with the four `needs` facts in both `known` (all facts found so far)
and `delta` (new facts to use in the next round). In round 1, `rule uses(a, b) :- needs(a, b);` copies them into `uses`. In round 2,
`rule uses(a, c) :- needs(a, b) and uses(b, c);` fires with `uses(b, c)` reading round 1's new facts. `unify` matches `needs(a, b)` against
`("app", "net")`, giving `{a ↦ "app", b ↦ "net"}`. Matching `uses(b, c)` against `("net", "io")` agrees on `b` and adds `c ↦ "io"`,
so the head produces `uses("app", "io")` for the first time.

At the end of each round, my `least_fixpoint` loop calls `known.add` (`RelationDb::add`) on each derived tuple. A new tuple sets
`changed` to true. If no tuple is new, it stays false and the loop stops. Even with a cycle, these rules only copy existing values. Five strings
allow at most 25 `uses` tuples, and deriving an existing tuple again does not count as a change.

> `solutions needs(?a, ?)` is `["app", "net", "ui"]`, three values from four facts. Point at where your engine cuts each match down to the named holes,
> removes duplicates, and sorts. Why must the anonymous hole be cut away *before* duplicates are removed? Why does each `?` need a fresh variable
> name, and what would `solutions needs(?, ?)` return if your engine gave every anonymous hole the same name?

In `solutions`, `named_holes` collects each named hole once, in first-appearance order. After `filter_map` finds matching facts,
the following `map` keeps only those holes' values. `sort_by` uses `compare_rows` and the provided `compare` to sort these rows;
`dedup_by` then removes adjacent duplicates. For `needs(?a, ?)`, the facts `("app", "ui")` and `("app", "net")` both become the row
`["app"]`. If the anonymous value were kept during deduplication, those rows would remain different and `"app"` would appear twice.

Each anonymous hole gets a fresh internal name, such as `?0`, that a source identifier cannot spell. Reusing one name would make
`unify` require those positions to agree. Then `solutions needs(?, ?)` would match only facts with equal columns. The example has
none, so it would return `[]` instead of `[()]`, which represents one answer with no named values.

> `rule leaf(a) :- size(a, n) and m > cap;` is `Unbound (m)`, but `n > cap` is accepted, and so is `{ let m = n * 2; m > cap }`. Walk through your
> `check_range_restriction` on all three: which names `free_vars` gives for each filter, and which test lets each name through or rejects it. Why
> does the language insist that every *head* variable be bound by a generator? What would a rule like `rule uses(a, c) :- needs(a, b);` have to
> mean if it were allowed?

My `check_range_restriction` in [`check.rs`](src/relations/check.rs) first collects the variables named by generators, here `{a, n}`.
For a filter, each name from `free_vars` must be in that set or name a top-level global, function, or native. For `m > cap`, the names
are `[m, cap]`; `m` meets neither condition, so the check reports `Unbound (m)` at the filter. For `n > cap`, they are `[n, cap]`:
`n` comes from the generator and `cap` is a global. The block also gives `[n, cap]`, because its `let` binds `m` locally.

Head variables are checked first and must come from generators so the engine has a value for each one; literals supply their own
values. Allowing `uses(a, c) :- needs(a, b)` would leave `c` unrestricted: whenever `a` needs something, it would use every string `c`,
an infinite relation the engine could not list.

> `hops.brg` (above) is rejected as `Recursive`, although `hops(2)` always returns. Show where your `check_pure` finds the cycle and why it reports
> `Recursive` rather than `Impure`. Then, for the filter `note(a)`, where `note` calls `println`, explain how your code builds the witness
> `[note, println]`, and how it computes the impure set `I` as a least fixpoint over the program's functions.

`check_pure` checks higher-order calls, effects, and recursion in that order. For `hops(2)`, `reached` finds `hops`, whose parameter
is an `Int`. Its body has no effects, so it is not in the impure set `I`. However, `refs` records that `hops` calls itself in the
`calls` map. `recursive("hops")` follows that map using `follow_calls` and finds `hops` again, giving `Recursive` rather than `Impure`.
The check follows calls without considering argument values, so it cannot establish that this particular call terminates.

`Purity::new` calls `find_impure` to compute `I`. Starting empty, it repeatedly uses `effect` to inspect unmarked bodies, adding any
that reaches an effect, until no more are added. Thus `note` becomes impure because its body calls `println`. For the filter `note(a)`,
`call` asks `through` to examine `note`'s body. It gets `[println]` and prepends `note`, producing `[note, println]`. This walk uses
the current impure set to find the first effect in source order and tracks visited callables to avoid following a cycle forever.

> The purity check already rejects every filter that queries, yet your engine also keeps a `materializing` flag. Point at where you set and clear it
> in `solutions`, and explain why it must be cleared before an error from the rounds is returned. Using the textbook's `p`/`q`/`r` program from the
> chapter's design problems, describe what your engine would do, run without the checks, if the flag were not there.

In `solutions`, I set `self.materializing = true` before `least_fixpoint`, clear it afterward, and only then apply `result?`.
If an error returned before the flag was cleared, reusing the interpreter would make later queries, `add`, and `clear` fail with
`QueryInFilter` even though no fixpoint was being computed.

In the chapter's example, answering `solutions p(?x)` fires `p`'s rule, whose filter `not r(x)` calls `solutions` again for `r(x)`.
Without the flag, that query would find no cached closure and start another fixpoint over the same rules, reaching `p`'s filter
again until the stack overflowed. The flag instead stops the inner query with `QueryInFilter`, even without the static checks.

## How you implemented it

> Walk through your `solutions` from start to finish: how you turn the query's arguments into terms, how you compute the fixpoint (the starting
> facts, one round, and firing one rule through its generators and filters), and how you build the answer. Say how your `Subst::unify` handles a
> variable already bound, and how it leaves the original substitution unchanged on failure. Naming the provided tools you used (`RelationDb`,
> `Subst`, `compare`, `type_of`, `env.root()`, `Control`) is encouraged.

`solutions` first rejects a query during materialization. Then `relation_arity` resolves the relation in the caller's environment
and gets its column count. Arguments are processed once, left to right: expressions become `Term::Val`, named holes become
`Term::Var(name)`, and anonymous holes get fresh internal names. The argument count is checked afterward.

If there is no cached closure, `least_fixpoint` copies the dynamic facts into `known` and `delta`. Each round, it calls `fire` once
per generator whose relation has delta facts. That generator reads `delta`; the others read `known`. Rules without generators run
only in round 1, including bodiless rules that supply permanent facts. New tuples enter `known` and become the next round's `delta`;
a round with no additions ends the loop.

`fire` starts with one empty substitution. It joins all generators in body order using `Subst::unify`, then evaluates the filters
for each resulting substitution in `env.root()` extended with its bindings. Filters run in body order and stop at the first `false`.
A non-`Bool` gives `TypeError`, using `type_of` for the actual type; a `Control::Return` gives `ReturnOutsideFunction`.
`instantiate_head` fills in the head from each surviving substitution. `solutions` caches the closure, matches the query against it,
keeps only named-hole values, sorts and deduplicates them, and returns substitutions containing those named bindings.

`Subst::unify` rejects a length mismatch, then clones the substitution. Constants and already-bound variables must equal the fact's
corresponding value; an unbound variable gets that value. A mismatch returns `None`. Only the clone changes, so the original remains
available for trying another fact.

> Describe how your `check_pure` decides what a call reaches: how you tell a local from a top-level function or a native, how you treat `map`,
> `filter`, and `fold` callbacks, and which of the provided helpers (`subexprs`, `free_vars`, `bound_names`) you used and where.

I collect a filter's local names from its generator variables and `bound_names` over every conjunct. For a function, locals are its
parameters plus `bound_names(body)`. `call` treats a call through any of these names as impure, even if a top-level function shares
its name. Otherwise, it looks up the declaration: a function is judged through its body, while calling a relation or global is
impure. Native output functions, readers, and `to_string` are impure; other natives are allowed, subject to their arguments.

For `map` and `filter`, `callback_index` selects the second argument; for `fold`, the third. The callback must be a lambda, a top-level
function, or a pure native. Its contents still need checking: `effect` visits a lambda's body, and a named function passed as a value
counts as a call. A local callback gives its name as the witness; a computed callback gives an empty witness.

`subexprs` drives the expression walks in `effect` and `refs`. `refs` builds the call graph, which `reached` follows for the higher-order
and recursion checks. `free_vars` is used by range restriction, while `bound_names` identifies locals. For method calls, declared
receiver types select that head's methods; an unknown receiver makes the analysis consider every implementation with that method name.

> Point out anything that was tricky, a bug you fixed, or a design choice you made. If you used an assistant, say what you had it do and how you
> checked its work.

I had to work through the difference between a substitution and an environment. A substitution holds the values found by matching
generators, while `bind_all` adds those bindings to the root environment so a filter can use both logic variables and top-level names.
I also needed to trace how one empty substitution can become several matches, and why semi-naive evaluation lets one generator
read new facts while the others read all known facts. Requiring every generator to read only new facts would miss matches between
old and new facts.

The purity check took more explanation because a filter can reach an effect through several function calls. Walking through the
call graph and the witness helped me distinguish finding an effect from detecting recursion. One bug was evaluating filters before
later generators had bound their variables; `fire` now joins every generator first. The purity checker also needed to distinguish
methods by receiver type and construct witnesses in source order rather than discovery order.

I asked Claude Code to explain the concepts and write most of the initial implementation, then checked it with `cargo m6`, the
example programs, and code walkthroughs. Codex later reviewed and refactored the code, fixed the ordering and purity issues, and
helped revise this description. It verified the changes with cumulative `cargo m6` tests, formatting, Clippy, and focused purity
checks outside the repository. I checked its explanations by asking follow-up questions about substitutions, environments, the
fixpoint rounds, and how the purity checker follows calls.
