# Status

Current state only — no history. History lives in git (D7): `git log -p -- <path>`.

## Snapshot
- No Rust code yet. No `Cargo.toml`, no `src/`.
- Verus: not installed (`which verus` empty). `cargo`/`rustc` present (rustup;
  toolchains `stable`, `1.85.1`).
- Docs: `AGENTS.md`, `CLAUDE.md` (shim), `README.md`, `PLAN.md`, `agent-docs/` created. `.gitignore` ignores CLAUDE.md, PLAN.md (D5, D6); agent-docs + AGENTS.md committed.
- Next: M0 owner decisions, then M1 toolchain (`project/plan.md`).

| Component | Status |
|---|---|
| mltl-core | PLANNED |
| parser | PLANNED |
| WEST | PLANNED (source not on machine) |
| formula progression | PLANNED |
| language partition | PLANNED |
| SAT solver | PLANNED (source location UNKNOWN) |
| R2U2 in place | PLANNED (upstream already has partial Verus annotations) |

## Uncommitted work
Agents don't commit unless asked (AGENTS.md §5), so git history lags the
working tree. List here anything done but not yet committed, and clear it when
committed. (none)
