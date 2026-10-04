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
- `src/mltl.rs` also has exec `clone_mltl`, `eq_mltl` and spec `take` (D35).
- Exec `convert_nnf` / `convert_bnf` state their guarantees in `ensures`
  (normal form, same meaning, …; D37) and delegate the recursion to private
  `convert_nnf_unchecked` / `convert_bnf_unchecked`. `is_nnf` +
  `convert_nnf_is_nnf` added for this (not in Isabelle).
- `complen_property_via_atomics`: AFP's progression corollary, proved from
  `atomics_agree_semantics` (no progression).
- Crate: 137 VERIFIED (2026-10-03).

## Design
- One `Mltl<A>` for spec and exec, `usize` bounds (D15); spec traces
  `Seq<Set<A>>` (D16). No derives; verified `clone_mltl` / `eq_mltl`
  instead (D35).

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
