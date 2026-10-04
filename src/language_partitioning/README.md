# language_partitioning

Language partitioning for MLTL, proved correct in Verus. Port of the AFP
entry
[`Mission_Time_LTL_Language_Partition`](https://www.isa-afp.org/entries/Mission_Time_LTL_Language_Partition.html).

Partitioning splits a formula into several formulas that together say the
same thing, but no two of which can hold on the same trace. You choose how
to split each temporal interval by giving a *composition*: a list of block
widths that add up to the interval's length. Example: `F[0,9] x` with the
composition `[3,3,3]` becomes

- `F[0,2] x` (x first holds in the first block),
- `G[0,2] ¬x ∧ F[3,5] x` (in the second),
- `G[0,5] ¬x ∧ F[6,8] x` (in the third).

A trace satisfies `F[0,9] x` exactly when it satisfies one of the three
formulas, and no trace satisfies two of them. `k` sets how many levels deep
the splitting recurses into subformulas.

## Start here

**[`LP_mltl`](src/exec.rs#L724)** is the function to use. It takes an
extended formula (an MLTL formula with a composition on every `F`, `G`, `U`,
`R`; type [`MltlExtExec`](src/exec.rs#L23)) and the depth `k`, and returns a
list of plain MLTL formulas. Its `ensures` clause is the correctness
statement. If the intervals are well formed and every composition fits its
interval ([`check_lp_input`](src/exec.rs#L852) decides this), then:

- the result is exactly what Isabelle's `LP_mltl φ k` computes;
- **union:** on every trace at least `wpd φ` long, `φ` holds iff some
  formula of the result holds;
- **disjointness:** if every composition is all ones, or `k = 1`, then on
  every such trace no two different formulas of the result both hold.

## What the guarantees mean

"Holds" is [`semantics_mltl`](../mltl-core/src/mltl.rs#L163), the AFP
semantics of MLTL. The other terms:
[`wpd_mltl`](src/ext.rs#L349) (the trace length the theorems need),
[`intervals_welldef`](../mltl-core/src/properties.rs#L17) (every `[a,b]`
has `a ≤ b`), [`is_composition_MLTL`](src/composition.rs#L51) and
[`is_composition_MLTL_allones`](src/composition.rs#L73). The algorithm
the result equals, as in the Isabelle source:
[`LP_mltl_spec`](src/algorithm.rs#L178) and
[`LP_mltl_aux_spec`](src/algorithm.rs#L125).

Isabelle's extended formula type is here the shared
[`MltlParseTree`](../mltl-core/src/parse_tree.rs#L22) (a formula with data
at every node) with the composition as data
([`MltlExt`](src/ext.rs#L23)).

## Key theorems

- [`LP_mltl_language_union`](src/union.rs#L394) and
  [`LP_mltl_language_union_explicit`](src/union.rs#L360): the union theorem.
- [`LP_mltl_language_disjoint`](src/disjoint.rs#L635) (all-ones
  compositions, any `k`) and
  [`LP_mltl_language_disjoint_k1`](src/disjoint.rs#L649) (any compositions,
  `k = 1`): the disjointness theorems.

Every other definition and lemma of the AFP entry is ported or replaced by a
shorter proof, with nothing trusted. Proofs:
[`scripts/verify.sh`](../../scripts/verify.sh). Runtime checks, including
the Isabelle examples: `cargo test -p language_partitioning --release`.

Agent context: [agent-docs/correspondence/language-partitioning.md](../../agent-docs/correspondence/language-partitioning.md),
[agent-docs/modules/language-partitioning.md](../../agent-docs/modules/language-partitioning.md).
