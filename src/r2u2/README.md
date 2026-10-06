# r2u2

A runtime monitor for MLTL, proved correct in Verus. It runs the algorithm
of the [R2U2](https://r2u2.temporallogic.org) monitor (as formalized in the
`MLTL_R2U2-` repo, `isabelle/R2U2_*.thy`): one queue of verdicts per
subformula, ring buffers of fixed size, verdicts produced as soon as the
operators can decide them.

Why: R2U2 as shipped can give wrong verdicts. For
`p0 U[0,0] ((p1 U[1,1] p0) U[0,2] p1)` on the trace `{}, {p0}, {p1}`, the
formula is false at step 1, but `r2u2_core` (compiled by C2PO) reports true:
a queue sized too small overwrites a verdict before it is read. This crate
reports false, and proves it is always right.

## Start here

**[`Monitor`](src/exec_engine.rs#L559)** is the monitor: `Monitor::new(φ)`,
then [`step`](src/exec_engine.rs#L619)`(state)` once per time step (a
`HashSet` of the atoms true at that step), then
[`verdicts`](src/exec_engine.rs#L683)`()`. The `ensures` clause of `step` is
the guarantee: after `k` steps, for every trace that starts with the states
fed so far,

- every verdict is right: it gives each step `t` it covers the truth value
  of `φ` at `t` ([`semantics_mltl`](../mltl-core/src/mltl.rs#L164)), and
- every step `t` with `t + wpd(φ) < k` is covered. `wpd(φ)`
  ([`wpd`](src/engine.rs#L147)) is the formula's worst-case delay, the sum of
  the upper bounds along its deepest chain of temporal operators.

[`monitor_trace`](src/exec_engine.rs#L738) runs a whole trace, with the same
guarantee in its `ensures`.

A verdict `(v, t)` means "`v` at every step after the previous verdict's
step, up to `t`", so one verdict can cover several steps. For `!p0` on
`{p0}, {p0}, {}` the verdicts are `(false, 0), (false, 1), (true, 2)`
(both examples are tests: [`tests/readme_example.rs`](tests/readme_example.rs)).
`new` rejects intervals with `a > b`; otherwise the only failure is
arithmetic overflow of `usize`
(`step` returns `false`); a wrong verdict is never returned.

## How it is proved

Three versions of the monitor, each proved to give the same verdicts as the
next:

- **History model** ([`engine.rs`](src/engine.rs)): every queue keeps all
  verdicts ever written. Correct for every formula
  ([`r2u2_sound`](src/soundness.rs#L520)) and on time
  ([`r2u2_prompt`](src/promptness.rs#L475)).
- **Ring model** ([`ring_engine.rs`](src/ring_engine.rs)): queues are ring
  buffers with read pointers, as in R2U2. It gives exactly the history
  model's verdicts ([`r2u2_ring_eq`](src/ring_sim.rs#L1045)) with
  [`child_slots`](src/ring_engine.rs#L174) slots per queue: 1 for the child
  of a `!` and for the root; for a child of `&` or `U`, C2PO's size plus
  half of the extra a slower child needs, rounded up
  ([`half.rs`](src/half.rs)). Rounding down is not enough: then some traces
  give wrong verdicts.
- **Executable** ([`exec.rs`](src/exec.rs),
  [`exec_engine.rs`](src/exec_engine.rs)): the ring model as running code.

Formulas are first rewritten into `true`, `false`, atoms, `!`, `&` and `U`.

## Speed

About 6.5× slower than `r2u2_core` (median over 15 formulas, range 2–12×);
see [`benchmarks/`](benchmarks/README.md). Runtime check against
[`mltl-eval`](../mltl-eval): `cargo test -p r2u2 --release`.

Nothing is trusted beyond vstd's specifications of `Vec` and `HashSet`.
Proofs: [`scripts/verify.sh`](../../scripts/verify.sh) `-p r2u2`.

Agent context: [agent-docs/modules/r2u2.md](../../agent-docs/modules/r2u2.md),
[agent-docs/correspondence/r2u2.md](../../agent-docs/correspondence/r2u2.md).
