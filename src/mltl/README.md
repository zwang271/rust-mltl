# mltl

One crate to import for the whole verified library: write formulas and
traces as text, run any algorithm, and print the results as text.

```rust
let mut cx = mltl::Context::new();
let f = cx.parse_formula("G[0,2] (request -> F[0,1] grant)")?;
let trace = cx.parse_trace("[{request}, {grant}, {}]")?;
let g = cx.parse_formula("F[0,2] grant")?;

mltl::eval(&f, &trace);                                    // true
cx.display(&mltl::nnf(&mltl::progress(&f, &trace[..1])));  // F[0,0] grant & G[0,1] (!request | F[0,1] grant)
mltl::partition(&g, 1, 1)?;                                // F[0,0] grant, G[0,0] !grant & F[1,1] grant, ...
cx.west(&g)?;                                              // "# grant\ns,s,1\ns,1,s\n1,s,s\n"
mltl::monitor(&f, &trace)?;                                // R2U2's verdicts, each proved right
mltl::sat(&f)?;                                            // Sat(a trace), Unsat or Unknown (needs CaDiCaL)
```

More examples, all run as tests: [`src/lib.rs`](src/lib.rs).

## What is guaranteed

Each function calls one verified function, whose `ensures` clause is the
guarantee:

| Here | Verified function and its guarantee |
|---|---|
| [`Context::parse_formula`](src/lib.rs#L253) | [`Atoms::parse`](../mltl-parse/src/atoms.rs#L292): returns exactly the formula the text denotes, with each name replaced by its number |
| [`Context::parse_trace`](src/lib.rs#L282), [`Context::parse_csv`](src/lib.rs#L288) | [`Atoms::parse_trace`](../mltl-parse/src/atoms.rs#L609), [`Atoms::parse_csv`](../mltl-parse/src/atoms.rs#L636): the numbered trace agrees with the text on every name, so formulas keep their truth value |
| [`Context::trace`](src/lib.rs#L262) | [`Atoms::trace`](../mltl-parse/src/atoms.rs#L570): the same, for a trace given as lists of names |
| [`Context::display`](src/lib.rs#L301) | [`Atoms::print`](../mltl-parse/src/atoms.rs#L910), [`Atoms::print_trace`](../mltl-parse/src/atoms.rs#L699): the text parses back to the same formula or trace |
| [`eval`](src/lib.rs#L467) | [`BitTrace::from_sets`](../mltl-eval/src/bit_trace.rs#L163) (same trace, packed into bits), then [`mltl_eval_bottom_up_bits`](../mltl-eval/src/bottom_up.rs#L298): the result is the MLTL semantics |
| [`progress`](src/lib.rs#L477), [`progress_afp`](src/lib.rs#L483) | [`prog`](../formula_progression/src/extended.rs#L311), [`formula_progression`](../formula_progression/src/algorithm.rs#L491) |
| [`partition`](src/lib.rs#L494), [`partition_with`](src/lib.rs#L528) | [`with_width`](../language_partitioning/src/splits.rs#L54) / [`with_compositions`](../language_partitioning/src/splits.rs#L181), then [`LP_mltl`](../language_partitioning/src/exec.rs#L724) |
| [`nnf`](src/lib.rs#L621), [`bnf`](src/lib.rs#L626) | [`convert_nnf`](../mltl-core/src/properties.rs#L2736), [`convert_bnf`](../mltl-core/src/properties.rs#L2802) |
| [`Context::west`](src/lib.rs#L327) | [`fast_reg_checked`](../west/src/api.rs#L40): a trace at least `complen(f)` long satisfies `f` exactly when it matches one of the lines; [`trace_to_text`](../west/src/api.rs#L221) writes them |
| [`sat`](src/lib.rs#L557) | [`solve`](../mltl-sat/src/solve.rs#L312): `Sat(t)` means `t` satisfies `f`; `Unsat` means no trace of length `complen(f)` does. CaDiCaL is not trusted: its answers are checked |
| [`monitor`](src/lib.rs#L577), [`Monitor`](src/lib.rs#L586) | [`monitor_trace`](../r2u2/src/exec_engine.rs#L738), [`Monitor::step`](../r2u2/src/exec_engine.rs#L619): every verdict is right, and none comes later than the formula's worst-case delay |

Not verified (plain Rust, small): the wrappers themselves, the column
header of [`Context::west`](src/lib.rs#L327), [`value_at`](src/lib.rs#L616)
(reads a verdict list), and [`Context::unused`](src/lib.rs#L346), which
warns about atoms of a trace that a formula doesn't use. Such atoms can't
change the result
([`lemma_semantics_own_atoms`](../mltl-core/src/properties.rs#L2661)).

## Atom names

One [`Context`](src/lib.rs#L234) holds the table that numbers the atoms of
all formulas and traces of a problem, so a name means the same atom everywhere. `pN` is
atom N, and any other name gets the next free number when it first
appears. One catch: once a name has a number, a later `pN` may not use
that number or a higher one (parse the formula with the largest `pN`
first, or use only names).

Agent context: [agent-docs/modules/mltl.md](../../agent-docs/modules/mltl.md).
