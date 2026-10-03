# Module: mltl-core (`src/mltl-core`)

Purpose: shared MLTL foundation (goal 2). Isabelle mapping:
`../correspondence/mission-time-ltl.md`.

## Files
- `src/lib.rs` — `pub mod mltl;`
- `src/mltl.rs` — syntax (`Mltl<A>`, `implies_mltl`, `iff_mltl`,
  `atoms_mltl`), Isabelle-style helpers (`drop`, `nat_sub` + drop lemmas),
  `semantics_mltl`, the `MLTL_Encoding.thy` examples, sanity checks.
  11 items VERIFIED 2026-10-02.

## Design (D15, D16)
- One enum `Mltl<A>` for spec and exec; bounds `usize`. Generic atoms `A`.
- Spec traces `Seq<Set<A>>` (finite states, D16). Exec trace types + views: not yet (T2.7; spike
  used `Vec<Vec<bool>>` → `Seq<ISet<nat>>` — must become finite `Set<nat>` and `view_f: Mltl<usize> → Mltl<nat>`).
- No derives yet (`Clone`, `PartialEq`, …). Add when exec code needs them;
  Verus needs specs for derived impls — check verus-notes then.

## Proof tips
- Concrete examples: `reveal_with_fuel(semantics_mltl, depth)`.
- Assert the witness instance (`semantics_mltl(drop(pi, i), φ)`) before the
  existential; prove `drop(pi, k)` shapes with `=~=` or the drop lemmas.
- Quantifiers over suffixes: trigger on `drop(pi, k)`, never on
  `semantics_mltl(..)` (verus-notes gotcha).

## Next
T2.4 `MLTL_Properties` spec fns; T2.5 downstream lemma inventory.
