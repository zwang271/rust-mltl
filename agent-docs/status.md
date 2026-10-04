# Status

Current state only. History is in git.

- **Verified:** `scripts/verify.sh` → mltl-core 138 + mltl-eval 66 +
  formula_progression 90 + mltl-parse 139 = 433 verified, 0 errors (Verus
  0.2026.09.27.3cf1832, 2026-10-03). Runtime tests: `cargo test --workspace --release`.
- **Toolchains:** Verus as above (needs rustup `1.98.1`); `1.85.1` for
  R2U2's pinned code; `stable` for everything else.
- **Last housekeeping:** 2026-10-03 (first pass). Next: when milestone 3
  (parser) finishes, or sooner if a trigger in `INDEX.md` fires.

| Component | State |
|---|---|
| mltl-core | All of `MLTL_Encoding`, `MLTL_Properties`, and the non-R2U2 parts of `MLTL_Properties_Extended` verified; executable `convert_nnf`, `convert_bnf`, `clone_mltl`, `eq_mltl`. |
| mltl-eval | Top-down, bottom-up, and bit-row-trace bottom-up evaluators verified; benchmark suite. |
| formula progression | Done (D33–D36): AFP theory and the Extended theory's simplified `prog` fully verified, exec + runtime tests; benchmarked vs the Haskell export (about equal; faster with mimalloc; 66×+ vs the deployed API binary). |
| parser | Done: lexer, grammar, parser (sound + complete), printer (round trip), numbering (injective, truth-preserving), AFP binding examples; 139 verified. |
| language partitioning | Planned. |
| SAT solver | Planned; source located (D18), not surveyed. |
| WEST, R2U2 in place | Waiting for fork URLs (Q10, deferred). |
| batched evaluator | Designed, shelved (D28). |

## Uncommitted work
Agents commit only when asked, so list finished-but-uncommitted work here and
clear it on commit. (none)
