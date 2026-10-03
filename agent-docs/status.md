# Status

Current state only. History is in git.

- **Verified:** `scripts/verify.sh` → mltl-core 130 + mltl-eval 66 = 196
  verified, 0 errors (Verus 0.2026.09.27.3cf1832, 2026-10-03). Runtime tests:
  `cargo test -p mltl-eval --release`.
- **Toolchains:** Verus as above (needs rustup `1.98.1`); `1.85.1` for
  R2U2's pinned code; `stable` for everything else.
- **Last housekeeping:** 2026-10-03 (first pass). Next: when milestone 3
  (parser) finishes, or sooner if a trigger in `INDEX.md` fires.

| Component | State |
|---|---|
| mltl-core | All of `MLTL_Encoding`, `MLTL_Properties`, and the non-R2U2 parts of `MLTL_Properties_Extended` verified; executable `convert_nnf`, `convert_bnf`. |
| mltl-eval | Top-down, bottom-up, and bit-row-trace bottom-up evaluators verified; benchmark suite. |
| parser (next) | Planned. |
| formula progression | Planned. |
| language partitioning | Planned. |
| SAT solver | Planned; source located (D18), not surveyed. |
| WEST, R2U2 in place | Waiting for fork URLs (Q10, deferred). |
| batched evaluator | Designed, shelved (D28). |

## Uncommitted work
Agents commit only when asked, so list finished-but-uncommitted work here and
clear it on commit. (none)
