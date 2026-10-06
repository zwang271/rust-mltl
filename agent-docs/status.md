# Status

Current state only. History is in git.

- **Verified:** `scripts/verify.sh` → mltl-core 154 + mltl-eval 66 +
  formula_progression 90 + mltl-parse 139 + language_partitioning 215 = 664
  verified, 0 errors (Verus 0.2026.09.27.3cf1832, 2026-10-03, after
  `cargo clean` of every crate). Runtime tests: `cargo test --workspace --release`.
- **Toolchains:** Verus as above (needs rustup `1.98.1`); `1.85.1` for
  R2U2's pinned code; `stable` for everything else.
- **Last housekeeping:** 2026-10-03 (first pass). **Due now**: milestones 3
  (parser) and 5 (language partitioning) finished 2026-10-03, and
  `decisions.md` / `verus-notes.md` are over the size budget. Deferred so as
  not to collide with the parser session's commits.

| Component | State |
|---|---|
| mltl-core | All of `MLTL_Encoding`, `MLTL_Properties`, and the non-R2U2 parts of `MLTL_Properties_Extended` (incl. parse trees) verified; executable `convert_nnf`, `convert_bnf`, `clone_mltl`, `eq_mltl`. |
| mltl-eval | Top-down, bottom-up, and bit-row-trace bottom-up evaluators verified; benchmark suite. |
| formula progression | Done (D33–D36): AFP theory and the Extended theory's simplified `prog` fully verified, exec + runtime tests; benchmarked vs the Haskell export (about equal; faster with mimalloc; 66×+ vs the deployed API binary). |
| parser | Done: lexer, grammar, parser (sound + complete), printer (round trip), numbering (injective, truth-preserving), AFP binding examples, cargo-style error reports from the verified parser's stopping point (positions proved in bounds, wording tested); 142 verified. Shared atom table `Atoms` (2026-10-04): 156 verified. |
| language partitioning | Done (D38–D40): whole AFP entry verified (union, disjointness for all-ones compositions and for `k = 1`), exec `LP_mltl` with the theorems in its `ensures`, Isabelle examples as runtime tests; mltl_ext = core parse tree (now ported). Printing (`Codegen.thy`) waits for the verified printer. |
| SAT solver | VERIFIED 2026-10-04 (Verus 0.2026.09.27.3cf1832): `src/propositional` (44: AFP formulas/CNF, DIMACS model check, LRAT checker) and `src/mltl-sat` (75: fast translation + `soundness_fast_mltl_to_sat_root_complen`, hash-consed encoder, CNF ⟺ MLTL equisatisfiable, verified `solve` whose `ensures` is the end-to-end guarantee; a real CNF model always gives SAT). CaDiCaL runs through `run_solver` (empty contract, ledger TB1). 100 REU benchmark formulas: 5.5 s total, all agree with Z3. Open: slow translation and other theories (`correspondence/mltl-sat.md`). |
| WEST | VERIFIED 2026-10-04 (D43; Verus 0.2026.09.27.3cf1832): `src/west`, 297 verified, nothing trusted. Spec of `WEST_Algorithms`, `WEST_correct(_v2/_pad)`; faithful exec equal to the spec (identical to Isabelle's Haskell export on 1200 random formulas); fast packed `fast_reg` proved equivalent (matching traces, not Isabelle's list), as fast as the unverified prototype. Benchmarks (upstream's hard sets): finishes the most formulas in every set; 2–5× faster than upstream Rust/C++ and 5–12× than the faithful port by geometric mean, far more by total time on the heaviest sets. `modules/west.md`. |
| R2U2 | VERIFIED 2026-10-04 (D48, D49, D50; Verus 0.2026.09.27.3cf1832); queue sizes halved 2026-10-05 (D55, `half.rs`): crate `src/r2u2`, 244 verified, nothing trusted beyond vstd Vec/HashSet specs. The R2U2 algorithm as in Isabelle (history model, ring model with read pointers, executable `Monitor`), each proved equal to the next; soundness for every MLTL formula with a ≤ b and promptness within `wpd` (`Monitor::step` ensures); child queues `⌈(x + y)/2⌉ + 1` (D55: C2PO's size plus half of the extra a slower child needs; ≈ 1.19× C2PO's total, was 1.38× with D50's `max(wpd(operands) − bpd(child), 0) + 1`), NOT child and root 1. C2PO's own sizes are wrong (80/20000 random runs; far more with large intervals, spike `r2u2-sizing`). ~6.5× slower than `r2u2_core`, which is wrong on some formulas. `modules/r2u2.md`. Next: Isabelle port (`project/m8-isabelle-port.md`). |
| front door `src/mltl` | 2026-10-04 (D47): text-level API over all crates (plain Rust wrappers); split helpers `language_partitioning::splits` verified (220 total); parser-based doc examples in every crate's `lib.rs`. |
| batched evaluator | Designed, shelved (D28). |

## Uncommitted work
Agents commit only when asked, so list finished-but-uncommitted work here and
clear it on commit. (none)
