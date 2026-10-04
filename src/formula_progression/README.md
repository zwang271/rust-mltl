# formula_progression

Formula progression for MLTL, proved correct in Verus.

Progression reads a trace one state at a time and rewrites the formula, so
that the rest of the trace has to satisfy the rewritten formula. Example:
`G[0,3] p` after a state where `p` holds becomes `G[0,2] p`. After a state
where `p` fails, it becomes `False`. That gives a verdict early, before the
trace ends.

## Start here

**[`prog`](src/extended.rs#L311)** is the function to use. Its `ensures`
clause is the correctness statement. For a formula `f` with well-formed
intervals and a trace `π`, the result `r` satisfies:

- `r` is exactly what Isabelle's `prog f π` computes;
- on every non-empty continuation `ρ`, `r` holds iff `π @ ρ` satisfies `f`;
- so if `r` is `True` (`False`), every non-empty continuation of `π`
  satisfies (violates) `f`. The verdict is final.

[`prog_owned`](src/extended.rs#L279) is the same function taking `f` by
value (no copy when progressing step by step), with the same guarantees.

**[`formula_progression`](src/algorithm.rs#L491)** is the AFP algorithm
exactly as published, without simplification, so its formulas grow with
every step. Its `ensures` states AFP's two main theorems for the result:
the continuation property above (Theorem 2), and that on a trace at least as
long as the formula's computation length, the result is equivalent to `True`
iff the trace satisfies `f` (Theorem 3).

Both take a `Mltl<usize>` and a trace in `mltl-eval`'s format
(`&[HashSet<usize>]`).

## What the guarantees mean

"Satisfies" is [`semantics_mltl`](../mltl-core/src/mltl.rs#L163), the AFP
semantics of MLTL. The other terms in the statements:
[`intervals_welldef`](../mltl-core/src/properties.rs#L17) (every `[a,b]`
has `a ≤ b`), [`complen_mltl`](../mltl-core/src/properties.rs#L758) (trace
length needed to decide a formula) and
[`semantic_equiv`](../mltl-core/src/properties.rs#L35) (same truth value on
every trace).

The algorithms the results are equal to, as in the Isabelle sources:
[`prog_spec`](src/extended.rs#L100),
[`formula_progression_spec`](src/algorithm.rs#L102) and its one-step case
[`formula_progression_len1_spec`](src/algorithm.rs#L42).

## Key theorems

- [`satisfiability_preservation`](src/correctness.rs#L186) (AFP Theorem 2):
  the rest of the trace satisfies the progressed formula iff the whole trace
  satisfies the original.
- [`formula_progression_correctness`](src/correctness.rs#L595) (AFP
  Theorem 3): on a long-enough trace, the result is equivalent to `True`
  iff the trace satisfies the formula.
- [`simp_mltl_correct`](src/simp.rs#L401): the simplifier never changes a
  formula's meaning. This is why simplifying does not weaken the guarantee.
- [`prog_early_eval`](src/extended.rs#L192): main theorem of the unpublished
  `Formula_Progression_Extended.thy`. A `True`/`False` result from `prog`
  is a final verdict, and conversely.

Every other definition and lemma of the AFP entry
[`Mission_Time_LTL_Formula_Progression`](https://www.isa-afp.org/entries/Mission_Time_LTL_Formula_Progression.html)
and of `Formula_Progression_Extended.thy` is ported too, with nothing
trusted. Proofs: [`scripts/verify.sh`](../../scripts/verify.sh). Runtime checks:
`cargo test -p formula_progression --release`. Speed compared with the
Isabelle-exported Haskell: [`benchmarks/README.md`](benchmarks/README.md).

Agent context: [agent-docs/correspondence/formula-progression.md](../../agent-docs/correspondence/formula-progression.md),
[agent-docs/modules/formula-progression.md](../../agent-docs/modules/formula-progression.md).
