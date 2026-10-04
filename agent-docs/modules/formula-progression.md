# Module: formula_progression (`src/formula_progression`)

Formula progression: rewrite a formula after each trace state so that the
rest of the trace must satisfy the rewritten formula. Isabelle mapping:
`../correspondence/formula-progression.md`. Decisions: D33–D35.

## Files
- `src/algorithm.rs`: `weight_operators`, `formula_progression_len1_spec`,
  `formula_progression_spec`, fold/append helpers, well-definedness,
  Theorem 1; exec `formula_progression_len1`, `formula_progression`.
- `src/correctness.rs`: Theorem 2 (`satisfiability_preservation`), the
  computation-length lemmas, Theorem 3 (`formula_progression_correctness`)
  and corollaries (`complen_property`, …).
- `src/simp.rs`: `simp_mltl_aux`, `simp_mltl`, `simp_duals` (`size_mltl` is in mltl-core)
  (spec + exec + lemmas).
- `src/extended.rs`: `formula_progression_alt` (simplify each step, stop
  at True/False), `prog`, `prog_early_eval`; exec `formula_progression_alt`,
  `prog`.
- `tests/progression.rs`: AFP and Extended `value` examples; random
  checks of Theorems 2–3 and `prog_early_eval` against `mltl_eval`.
- `benchmarks/`: drivers (`driver.rs` = example `fp_bench`, `driver.hs`),
  `gen_workloads.py`, `run.py`, `plot.py`, results and plots.
- Crate: 90 VERIFIED (2026-10-03; was 91 before `size_mltl` moved to mltl-core). No trusted items.

## Which function to use
`prog` (or `prog_owned`, by value, for step-by-step use) for real use;
`formula_progression` is the faithful AFP version and grows the formula
without bound (`(p0) U[0,n] (G[0,5] p1)` over n/2 states: 10,479 nodes at
n = 1000 vs 9 for `prog`).

## Performance (T4.6 done 2026-10-03; `benchmarks/README.md`)
vs the Isabelle-exported Haskell `prog` (GHC 9.14.1 -O2, unchanged export),
identical outputs checked by hash on every point:
- System malloc: 0.64–0.99× (Rust slower), except very wide windows
  (w = 256: 1.37×). mimalloc in the driver: 1.09–1.37×, w = 256: 1.75×.
- vs the deployed `run_prog` binary per request: 66× (n = 16384) up to
  ~19,000× (n = 8); ~30 ms process start dominates short requests.
- Both linear in trace length (slopes 1.00–1.03). Haskell's unary `Nat`
  did not hurt: the hot comparisons are against 0 (`less_nat 0 _` is O(1)).
- Profile (sampling profiler): first verified version spent ~75% in
  malloc/free; cloning operands (`clone_mltl`) and rebuilding the whole
  tree per simplifier pass. Ownership passing (`formula_progression_len1_owned`,
  owned `simp_mltl_aux`/`simp_mltl`/`simp_duals`, `*b = f(*b)` box reuse)
  gave 3.4–4.5×; an unverified prototype first, then the same code verified
  with no spec change (D31 order). Now `simp_mltl_aux` itself dominates
  (repeated fixpoint passes, as in Haskell). Further gains would need a
  different representation (node arena / shared DAG) or a one-pass
  simplifier proved equal to the fixpoint: not started.

## Proof patterns that worked
- Recursion that rewrites (Release → `¬(¬φ U ¬ψ)`, Global → `¬F¬φ`):
  prove by `decreases weight_operators(phi)` and call the lemma on the
  rewritten formula; show the measure drop and well-definedness in an
  `assert(..) by { reveal_with_fuel(weight_operators, 2); … }`.
- Strong helper statements make the Isabelle chain short. E.g. "the result
  has the same value on every trace" (`formula_progression_value`) gives
  Theorem 3, its False twin, true-or-false and the append corollaries.
- Quantified ensures (`forall ρ`) over a big case split hit rlimit; prove a
  pointwise version (`…_at(.., rho)`) and wrap it with `assert forall`.
- Equivalences with constants (`False ∨ ψ ≡ ψ`) need fuel 2 on
  `semantics_mltl` inside the `assert forall` (the inner call gets no fuel).

## README links (D37)
Links are by line number; after editing linked files run
`scripts/readme_links.py --fix`.

## Exec notes
- Owned variants move operands into the result; the borrowed
  `formula_progression_len1` is still needed for the operand that appears
  both progressed and unprogressed (Until/Future with `a = 0 < b`).
- `simp_mltl_aux` compares subformulas with `eq_mltl` (O(n) each), and
  `simp_mltl` repeats passes until nothing changes.
