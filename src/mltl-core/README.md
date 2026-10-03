# mltl-core

The shared foundation for every MLTL algorithm in this repo: the formula
syntax, its semantics over finite traces, and standard properties (negation
normal form, well-defined intervals, computation length, ...), all proved in
Verus.

It follows the AFP entry
[`Mission_Time_LTL`](https://www.isa-afp.org/entries/Mission_Time_LTL.html):
`MLTL_Encoding.thy` (datatype `mltl`, `semantics_mltl`) and
`MLTL_Properties.thy`, plus the unpublished `MLTL_Properties_Extended.thy`
(normal forms, unrolling lemmas, an evaluator; R2U2-specific parts excluded).

Status: `src/mltl.rs` (syntax, semantics) and `src/properties.rs` (all of
the above properties) are verified; executable code is next. One deliberate
difference from Isabelle: each trace step is a *finite* set of atoms, since
MLTL is a finite logic. Verify with `scripts/verify.sh`.

Agent context: agent-docs/modules/mltl-core.md,
agent-docs/correspondence/mission-time-ltl.md.
