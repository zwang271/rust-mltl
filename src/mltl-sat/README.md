# mltl-sat

MLTL satisfiability, proved in Verus. A port of the REU's Isabelle
translation from MLTL to Boolean logic (the "fast" translation of Hariharan
et al.). The SAT solving itself is done by CaDiCaL, which is not verified;
every answer it gives is checked by verified code before we report it.

Question answered: is there a trace of length `complen φ` that satisfies
`φ`? (Short traces are left out on purpose: `G[1,1] false` holds on the
empty trace but on no trace of length 2.)

## Start here

[`solve`](src/solve.rs#L312) is the function to use. It returns the answer
and how long each phase took. Its `ensures` is the whole guarantee, stated
about your formula `f`:

- `Some(Sat(π))`: `π` has length `complen f` and satisfies `f`;
- `Some(Unsat)`: no trace of length `complen f` satisfies `f`;
- `Some(Unknown)`: the solver's output did not check;
- `None`: `f` has an ill-formed interval or is too big to encode.

The only trusted pieces are [`run_solver`](src/solve.rs#L264), which runs
CaDiCaL and promises nothing about its output, and
[`now_ns`](src/solve.rs#L271), a clock read used only for the timings. `solve` is three steps:

1. [`encode`](src/encode.rs#L1340) builds the CNF. Its `ensures`: the CNF
   is satisfiable exactly when some trace of length `complen φ` satisfies
   `φ` (the counterpart of Isabelle's `mltl_dimacs_correct`).
2. CaDiCaL runs ([`run_cadical`](src/cadical.rs#L23)) and returns a model
   or an LRAT proof.
3. [`decide`](src/solve.rs#L207) checks that output. Its `ensures`, about
   the encoded formula `φ`:
   - [`Answer`](src/solve.rs#L34) `Sat(π)`: `π` satisfies `φ`
     ([`semantics_mltl`](../mltl-core/src/mltl.rs#L164)) and has length
     [`complen_mltl`](../mltl-core/src/properties.rs#L758)`(φ)`. The
     verified evaluator confirmed it.
   - `Answer::Unsat`: no trace of length `complen φ` satisfies `φ`
     ([`mltl_sat_len`](../mltl-core/src/properties.rs#L2500)). The
     verified LRAT checker accepted CaDiCaL's proof against our own CNF, and
     step 1's guarantee carries that to `φ`.
   - `Answer::Unknown`: the solver's output did not check.
   - And the other way round: if CaDiCaL returns a real model of the CNF,
     the answer is always `Sat`. A model never decodes to a bad trace.

Isabelle's end-to-end solver also proves it always answers; ours can still say
`Unknown` when CaDiCaL's unsatisfiability proof uses steps our checker does
not support (none did on the benchmarks).

Nothing about CaDiCaL, the DIMACS file, or the parsing of its output is
trusted: they can only turn an answer into `Unknown`.

## The Isabelle theorem

[`soundness_fast_mltl_to_sat_root_complen`](src/fast.rs#L640): for
well-formed intervals
([`intervals_welldef`](../mltl-core/src/properties.rs#L17)), `φ` is
satisfiable at length `complen φ` iff the clauses
[`fast_mltl_to_sat_root`](src/fast.rs#L149)`(φ)` are satisfiable
([`sat`](../propositional/src/formula.rs#L90)). The translation:
[`fast_mltl_to_sat`](src/fast.rs#L93),
[`get_associated_clauses_at_node`](src/fast.rs#L79),
[`unroll_until`](src/fast.rs#L38). The two directions:
[`trace_agrees_assign`](src/fast.rs#L423) and
[`assign_agrees_trace`](src/fast.rs#L530).

The executable encoding gives each distinct subformula one variable per
time step, as the Isabelle translation does, and encodes each Until
unrolling with one fresh variable per step, so its size is linear in the
interval.

## Running it

Needs `cadical` on `PATH` (or `$CADICAL`):
`cargo run --release -p mltl-sat --example mltl_sat -- 'G[0,3] (p0 | p1)'`,
or `--file FORMULAS.txt`, one formula per line
([`examples/mltl_sat.rs`](examples/mltl_sat.rs)). On the 100 benchmark
formulas of the REU paper, the whole pipeline took 5.5 s (slowest formula
0.13 s). Proofs: [`scripts/verify.sh`](../../scripts/verify.sh); tests:
`cargo test -p mltl-sat --release`.

Agent context: [agent-docs/correspondence/mltl-sat.md](../../agent-docs/correspondence/mltl-sat.md),
[agent-docs/project/m7-sat.md](../../agent-docs/project/m7-sat.md).
