# Module: mltl-core (`src/mltl-core`)

Purpose: shared MLTL foundation (goal 2). Isabelle mapping:
`../correspondence/mission-time-ltl.md`.

## Files
- `src/lib.rs` — `pub mod mltl;`
- `src/mltl.rs` — syntax (`Mltl<A>`, `implies_mltl`, `iff_mltl`,
  `atoms_mltl`), Isabelle-style helpers (`drop`, `nat_sub` + drop lemmas),
  `semantics_mltl`, the `MLTL_Encoding.thy` examples, sanity checks.
  11 items VERIFIED 2026-10-02.
- `src/properties.rs` — all of `MLTL_Properties.thy`: welldef, semantic
  equivalence, depth, subformulas, basic/duality lemmas, NNF + its 4 lemmas,
  complen, empty traces, the two induction rules. Then (D17) all non-R2U2
  parts of REU `MLTL_Properties_Extended.thy`: extra equivalences/pitfalls,
  CE lemmas, BNF, unrolling + shift lemmas, `mltl_eval`/`mltl_eval_correct`,
  `mltl_sat`, `atomic_props`/`atomics_agree_semantics`. ~2400 lines.
  Crate total 127 VERIFIED 2026-10-02, ~3 s.
- `spinoff_prover` on `release_until_dual2`, `convert_nnf_preserves_semantics`.

- `src/eval.rs` — exec evaluators `mltl_eval` (top-down) and
  `mltl_eval_bottom_up`, both `== semantics_mltl`. Human doc: `src/EVAL_MLTL.md`.
- `tests/eval_agree.rs` — AFP examples + 20k random formula/trace pairs, both
  evaluators agree (`cargo test -p mltl-core --release`).
- `benchmarks/` (D24) — benchmark suite: `gen_workloads.py` (deterministic
  workloads), `driver.rs` (cargo example `bench_driver`; unverified
  libmltl-syntax parser), `libmltl_driver.cc` (built against
  `external/libmltl`), `run.py` (runs all, asserts the two verified
  evaluators agree, records libmltl agreement), `plot.py` (matplotlib, growth
  exponents). Results in `benchmarks/results/*.csv`, plots in
  `benchmarks/plots/`. Human doc: `benchmarks/README.md`.

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

## Proof patterns that worked (properties.rs)
- Equivalence lemmas: often just `reveal_with_fuel(semantics_mltl, 2 or 3)`.
- Need a *minimal* witness (first failure): `lemma_first_failure` with a
  closure `p`; to use its `forall k. p(k)` result, instantiate via
  `assert forall|k| ... implies semantics_mltl(#[trigger] drop(pi, k), ψ) by { assert(p(k)); }`.
- Induction over formulas with rewrites (NNF): `decreases depth_mltl(f)` +
  `reveal_with_fuel(depth_mltl, 2)`; temporal cases prove the IH on all
  suffixes with `assert forall|i| semantics_mltl(#[trigger] drop(pi, i), ..) == .. by { recursive call }`.
- Big case splits: wrap each arm's goal in `assert(goal) by { ... }` so each
  is a separate solver query (avoids rlimit).

## Next
T2.8 (atom instantiation story mostly settled by D19); M10 batching (T10.2);
scalar bottom-up constant-factor work (see plan M10 status).
