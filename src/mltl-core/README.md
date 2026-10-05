# mltl-core

The shared foundation for every MLTL algorithm in this repo: the formula
syntax, its meaning on finite traces, and standard properties (normal forms,
well-defined intervals, computation length, ...), all proved in Verus.

## Start here

- **[`Mltl<A>`](src/mltl.rs#L21)**: the formula type, one variant per
  Isabelle constructor (`True`, `False`, `Prop`, `Not`, `And`, `Or`,
  `Future`, `Global`, `Until`, `Release`).
- **[`semantics_mltl`](src/mltl.rs#L164)**: what it means for a trace
  to satisfy a formula. Every guarantee in this repo is stated against it. It
  is AFP's definition case for case, with one deliberate difference: each
  trace step is a *finite* set of atoms, since MLTL is a finite logic.

## Executable functions

- **[`convert_nnf`](src/properties.rs#L2659)** pushes negations down to the
  atoms. Its `ensures`: the result is Isabelle's `convert_nnf f`, it is in
  negation normal form ([`is_nnf`](src/properties.rs#L642)), and for well-defined
  intervals it means the same as `f` on every trace.
- **[`convert_bnf`](src/properties.rs#L2725)** rewrites into `True`/`Prop`/`Not`/`And`/`Until`
  only. Its `ensures`: the result is Isabelle's `convert_bnf f`, it is in that
  form ([`is_bnf`](src/properties.rs#L1307)), has the same computation length, and for
  well-defined intervals stays well-defined and means the same as `f`.

The terms these statements use:
[`intervals_welldef`](src/properties.rs#L17) (every `[a,b]` has `a ≤ b`),
[`semantic_equiv`](src/properties.rs#L35) (same truth value on every trace),
and [`complen_mltl`](src/properties.rs#L758) (computation length).

## Key theorem

- [`atomics_agree_semantics`](src/properties.rs#L2577): two traces
  that agree on the formula's atoms for its first `complen_mltl` steps give
  the formula the same truth value. That is what makes the computation
  length meaningful: nothing after it, and no other atom, matters.
  It trivially implies the formula-progression corollary `complen_property`
  (extending a trace of at least `complen_mltl` steps never changes the
  verdict), since a trace and any extension of it agree on their first
  steps; [`complen_property_via_atomics`](src/properties.rs#L2635) is that
  short proof.

## Sources

It follows the AFP entry
[`Mission_Time_LTL`](https://www.isa-afp.org/entries/Mission_Time_LTL.html):
`MLTL_Encoding.thy` and `MLTL_Properties.thy`, all ported. It also ports the
unpublished `MLTL_Properties_Extended.thy` (normal forms, unrolling lemmas,
an evaluator specification, and the "r2u2 form" that the
[`r2u2`](../r2u2) monitor runs on). Executable
evaluators live in [`mltl-eval`](../mltl-eval). Proofs: [`scripts/verify.sh`](../../scripts/verify.sh).

Agent context: [agent-docs/modules/mltl-core.md](../../agent-docs/modules/mltl-core.md),
[agent-docs/correspondence/mission-time-ltl.md](../../agent-docs/correspondence/mission-time-ltl.md).
