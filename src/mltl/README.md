# mltl

One crate to import for the whole verified library: write formulas and
traces as text, run any algorithm, and print the results as text.

```rust
let mut atoms = mltl::Atoms::new();
let f = atoms.parse("G[0,2] (request -> F[0,1] grant)")?;
let trace = atoms.trace([vec!["request"], vec!["grant"], vec![]])?;

mltl::eval(&f, &trace);                                     // true
atoms.print(&mltl::nnf(&mltl::progress(&f, &trace[..1])));  // "F[0,0] grant & G[0,1] (!request | F[0,1] grant)"
mltl::partition(&atoms.parse("F[0,2] grant")?, 1, 1)?;      // F[0,0] grant, G[0,0] !grant & F[1,1] grant, ...
```

More examples, all run as tests: [`src/lib.rs`](src/lib.rs).

## What is guaranteed

Each function calls one verified function, whose `ensures` clause is the
guarantee:

| Here | Verified function and its guarantee |
|---|---|
| [`Atoms::parse`](src/lib.rs#L124) | [`Atoms::parse`](../mltl-parse/src/atoms.rs#L260): returns exactly the formula the text denotes, with each name replaced by its number |
| [`Atoms::trace`](src/lib.rs#L132) | [`Atoms::trace`](../mltl-parse/src/atoms.rs#L353): the numbered trace agrees with the named one on every name, so formulas keep their truth value |
| [`Atoms::print`](src/lib.rs#L154) | [`Atoms::print`](../mltl-parse/src/atoms.rs#L531): the text parses back to the same formula |
| [`eval`](src/lib.rs#L163) | [`mltl_eval_bottom_up`](../mltl-eval/src/bottom_up.rs#L288): the result is the MLTL semantics |
| [`progress`](src/lib.rs#L170), [`progress_afp`](src/lib.rs#L176) | [`prog`](../formula_progression/src/extended.rs#L311), [`formula_progression`](../formula_progression/src/algorithm.rs#L491) |
| [`partition`](src/lib.rs#L187), [`partition_with`](src/lib.rs#L203) | [`with_width`](../language_partitioning/src/splits.rs#L54) / [`with_compositions`](../language_partitioning/src/splits.rs#L181), then [`LP_mltl`](../language_partitioning/src/exec.rs#L724) |
| [`nnf`](src/lib.rs#L210), [`bnf`](src/lib.rs#L215) | [`convert_nnf`](../mltl-core/src/properties.rs#L2659), [`convert_bnf`](../mltl-core/src/properties.rs#L2725) |

## Atom names

One [`Atoms`](src/lib.rs#L106) table numbers the atoms of all formulas and
traces of a problem, so a name means the same atom everywhere. `pN` is
atom N, and any other name gets the next free number when it first
appears. One catch: once a name has a number, a later `pN` may not use
that number or a higher one (parse the formula with the largest `pN`
first, or use only names).

Agent context: [agent-docs/modules/mltl.md](../../agent-docs/modules/mltl.md).
