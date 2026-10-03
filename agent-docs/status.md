# Status

Keep this current. Newest entries at top of the log.

## Snapshot (2026-10-02)
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

## Log
- 2026-10-02 — Wrote task-level plan `project/plan.md` + human-facing `../PLAN.md` (PROPOSED, awaiting owner review). Surveyed upstream `r2u2_core` Verus specs (see Q5).
- 2026-10-02 — Moved out of `MLTL_R2U2-` into standalone repo `REPO` (D4); `git init`, no remote.
- 2026-10-02 — Phase 0: created doc scaffolding; surveyed sources into
  `project/sources.md`; recorded D1–D3 and Q1–Q9.
