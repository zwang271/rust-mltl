# Module: mltl-core (`src/mltl-core`)

Shared MLTL foundation: syntax, semantics, properties. Isabelle mapping:
`../correspondence/mission-time-ltl.md`. Evaluators moved to `mltl-eval`
(`mltl-eval.md`, D31).

## Files
- `src/mltl.rs`: syntax (`Mltl<A>`, `implies_mltl`, `iff_mltl`,
  `atoms_mltl`), Isabelle-style helpers (`drop`, `nat_sub` and the drop
  lemmas), `semantics_mltl`, the `MLTL_Encoding.thy` examples.
- `src/properties.rs` (~2400 lines): all of `MLTL_Properties.thy` and the
  non-R2U2 parts of `MLTL_Properties_Extended.thy` (D17), including
  `mltl_eval_spec` + `mltl_eval_correct` and executable `convert_nnf` /
  `convert_bnf`. `spinoff_prover` on `release_until_dual2` and
  `convert_nnf_preserves_semantics`.
- Crate: 130 VERIFIED (2026-10-03).

## Design
- One `Mltl<A>` for spec and exec, `usize` bounds (D15); spec traces
  `Seq<Set<A>>` (D16). No derives yet (`Clone`, `PartialEq`); add when
  needed and check how Verus specifies derived impls.

## Proof patterns that worked
- Concrete examples: `reveal_with_fuel(semantics_mltl, depth)`; assert the
  witness instance before an existential.
- Quantifiers over suffixes: trigger on `drop(pi, k)`, never on
  `semantics_mltl(..)` (see verus-notes).
- Minimal witnesses: `lemma_first_failure` with a closure, instantiated via
  `assert forall .. by { assert(p(k)); }`.
- Induction with rewrites (NNF): `decreases depth_mltl(f)` + fuel 2;
  temporal cases prove the hypothesis on every suffix inside `assert forall`.
- Big case splits: one `assert(goal) by { .. }` per arm (avoids rlimit).
