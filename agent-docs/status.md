# Status

Current state only — no history. History lives in git (D7): `git log -p -- <path>`.

## Snapshot
- No Rust code yet. No `Cargo.toml`, no `src/`.
- Verus `0.2026.09.27.3cf1832` installed (T1.1; details `verification/verus-notes.md`).
  rustup toolchains: `stable`, `1.85.1` (r2u2 pin), `1.98.1` (Verus).
- Docs: `AGENTS.md`, `CLAUDE.md` (shim), `README.md`, `PLAN.md`, `agent-docs/` created. `.gitignore` ignores CLAUDE.md, PLAN.md (D5, D6); agent-docs + AGENTS.md committed.
- Plan accepted (D9–D12). Next: T1.2 workspace + verify script (`project/plan.md`). Open: Q10 fork URLs, Q11.

| Component | Status |
|---|---|
| mltl-core | PLANNED |
| parser | PLANNED |
| WEST | PLANNED (upstream github.com/zwang271/WEST; awaiting fork, Q10) |
| formula progression | PLANNED |
| language partition | PLANNED |
| SAT solver | DEFERRED (Q3) |
| R2U2 in place | PLANNED (upstream already has partial Verus annotations) |

## Uncommitted work
Agents don't commit unless asked (AGENTS.md §5), so git history lags the
working tree. List here anything done but not yet committed, and clear it when
committed. (none)
