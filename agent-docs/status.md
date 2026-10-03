# Status

Current state only — no history. History lives in git (D7): `git log -p -- <path>`.

## Snapshot
- Cargo workspace (`Cargo.toml`, `src/mltl-core`, `scripts/verify.sh`).
  `scripts/verify.sh` VERIFIED 2026-10-02 (Verus 0.2026.09.27.3cf1832): mltl-core
  11 verified, 0 errors.
- Verus `0.2026.09.27.3cf1832` installed (T1.1; details `verification/verus-notes.md`).
  rustup toolchains: `stable`, `1.85.1` (r2u2 pin), `1.98.1` (Verus).
- Docs: `AGENTS.md`, `CLAUDE.md` (shim), `README.md`, `PLAN.md`, `agent-docs/` created. `.gitignore` ignores CLAUDE.md, PLAN.md (D5, D6); agent-docs + AGENTS.md committed.
- Plan accepted (D9–D12). M1 DONE. M2: T2.1–T2.3 done (syntax + semantics, `mltl.rs`). Next: T2.4. Q10 deferred (D14).

| Component | Status |
|---|---|
| mltl-core | PARTIAL: `MLTL_Encoding` VERIFIED; `MLTL_Properties` PLANNED |
| parser | PLANNED |
| WEST | PLANNED (upstream github.com/zwang271/WEST; fork deferred, Q10) |
| formula progression | PLANNED |
| language partition | PLANNED |
| SAT solver | DEFERRED (Q3) |
| R2U2 in place | PLANNED (upstream already has partial Verus annotations) |

## Uncommitted work
Agents don't commit unless asked (AGENTS.md §5), so git history lags the
working tree. List here anything done but not yet committed, and clear it when
committed. (none)
