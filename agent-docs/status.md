# Status

Current state only — no history. History lives in git (D7): `git log -p -- <path>`.

## Snapshot
- Cargo workspace (`Cargo.toml`, `src/mltl-core`, `scripts/verify.sh`).
  `scripts/verify.sh` VERIFIED 2026-10-02 (Verus 0.2026.09.27.3cf1832): mltl-core
  169 verified, 0 errors (2026-10-03).
- Verus `0.2026.09.27.3cf1832` installed (T1.1; details `verification/verus-notes.md`).
  rustup toolchains: `stable`, `1.85.1` (r2u2 pin), `1.98.1` (Verus).
- Docs: `AGENTS.md`, `CLAUDE.md` (shim), `README.md`, `PLAN.md`, `agent-docs/` created. `.gitignore` ignores CLAUDE.md, PLAN.md (D5, D6); agent-docs + AGENTS.md committed.
- Plan accepted (D9–D12). M1 DONE. M2: T2.1–T2.6b done — `MLTL_Encoding`, `MLTL_Properties`, REU `MLTL_Properties_Extended` (minus R2U2, D17). T2.7 done (exec convert_nnf/convert_bnf/mltl_eval). M10: scalar bottom-up evaluator done; T10.2 batching SHELVED (D28, `project/m10-batched-eval.md`). Next: T2.8, M3 parser (or M10 batching, owner's call). Q10 deferred (D14). SAT source located (D18).

| Component | Status |
|---|---|
| mltl-core | `MLTL_Encoding`, `MLTL_Properties`, `MLTL_Properties_Extended` (non-R2U2) VERIFIED; exec `convert_nnf`, `convert_bnf`, `mltl_eval`, `mltl_eval_bottom_up` VERIFIED |
| parser | PLANNED |
| WEST | PLANNED (upstream github.com/zwang271/WEST; fork deferred, Q10) |
| formula progression | PLANNED |
| language partition | PLANNED |
| SAT solver | PLANNED (source `REU/isabelle/`, D18) |
| R2U2 in place | PLANNED (upstream already has partial Verus annotations) |

## Uncommitted work
Agents don't commit unless asked (AGENTS.md §5), so git history lags the
working tree. List here anything done but not yet committed, and clear it when
committed. (none)
