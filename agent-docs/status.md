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
| parser | Done: lexer, grammar, parser (sound + complete), printer (round trip), numbering (injective, truth-preserving), AFP binding examples, cargo-style error reports from the verified parser's stopping point (positions proved in bounds, wording tested); 142 verified. |
| language partitioning | Done (D38–D40): whole AFP entry verified (union, disjointness for all-ones compositions and for `k = 1`), exec `LP_mltl` with the theorems in its `ensures`, Isabelle examples as runtime tests; mltl_ext = core parse tree (now ported). Printing (`Codegen.thy`) waits for the verified printer. |
| SAT solver | `src/propositional` VERIFIED 2026-10-04 (44 items, Verus 0.2026.09.27.3cf1832): AFP formulas/CNF, DIMACS model check, LRAT checker; checks CaDiCaL 3.0.1 proofs. Next: MLTL translation (`project/m7-sat.md`). |
| WEST, R2U2 in place | Waiting for fork URLs (Q10, deferred). |
| batched evaluator | Designed, shelved (D28). |

## Uncommitted work
Agents commit only when asked, so list finished-but-uncommitted work here and
clear it on commit. (none)
