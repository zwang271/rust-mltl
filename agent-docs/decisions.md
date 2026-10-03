# Decision log

Append-only. To change a decision, add a new entry that supersedes the old one
(reference it by ID). Format: `D<n> (YYYY-MM-DD) — title`, then context /
decision / consequences.

## D1 (2026-10-02) — Documentation split
- Context: owner's kickoff instructions.
- Decision: `agent-docs/` is the agents' source of truth, freely maintained by
  agents; all other Markdown in `rust-mltl/` (except `AGENTS.md`) is
  human-facing and only edited on human request. `src/**/README.md` are short
  dual-audience pointers into `agent-docs/`. Rules in `../AGENTS.md` §3.
- Consequences: stale human docs are logged in `human-doc-backlog.md`, not fixed
  unilaterally.

## D2 (2026-10-02) — Workspace confinement
- Decision: agents write only inside the rust-mltl repo. Upstream sources
  (`ROOT/isabelle`, `ROOT/r2u2`, AFP) are read-only references.
- Consequences: "verify R2U2/WEST in place" must be realized inside
  `rust-mltl/` somehow (submodule, vendored copy, …) — open question Q1.

## D3 (2026-10-02) — CLAUDE.md shim
- Decision: `rust-mltl/CLAUDE.md` contains only `@AGENTS.md` so Claude Code
  agents auto-load the same rules. AGENTS.md stays the single canonical file.

## D4 (2026-10-02) — Separate repository
- Decision: rust-mltl is its own git repo (`REPO`, see `project/sources.md`)
  (was `ROOT/rust-mltl`, never committed there). `ROOT` (`MLTL_R2U2-`) remains
  a read-only reference. No remote configured yet.
- Consequences: Q1 options now include submodules of `r2u2`/WEST inside this repo.

## D5 (2026-10-02) — .gitignore; local-only top-level docs
- Decision: agents maintain `/.gitignore`. `AGENTS.md`, `CLAUDE.md`, `PLAN.md`
  are git-ignored (local only, not committed). (AGENTS.md part superseded by D6.) Also ignored: `/target/`, editor/OS files.
- Consequences: add new build artifacts/tool outputs to `.gitignore` when they
  appear. `PLAN.md` is being annotated inline by the owner (2026-10-02): read
  their inline comments, never overwrite them; fold answers into
  `decisions.md` / `project/plan.md`.

## D6 (2026-10-02) — Commit agent-docs/ and AGENTS.md (supersedes part of D5)
- Context: agent-docs is the project's long-term memory (decisions, trusted-base
  ledger, correspondence); it must be versioned with the code, and its rules
  live in AGENTS.md.
- Decision: commit `agent-docs/` and `AGENTS.md`. `CLAUDE.md` (shim) and
  `PLAN.md` stay git-ignored. agent-docs must not hard-code machine paths; use
  the `REPO`/`ROOT`/`AFP` placeholders defined in `project/sources.md`.

## D7 (2026-10-02) — Git history replaces manual logs
- Context: repo now has git history; a manual log duplicates it and drifts.
- Decision: no manual changelogs. `status.md` is a snapshot of current state
  plus an "Uncommitted work" list (agents only commit on request, so git lags).
  Commit messages carry the what/why and reference D/Q/T IDs. Dates are still
  written for decisions, observations of external state, and verification
  results (with Verus version + command). Details: `INDEX.md` "History and dates".
- Consequences: removed `status.md` Log section (its 3 entries are covered by
  D4, Q5, and commits `3df24c7`, `18a654b` — was `0edeeac` before D8 re-authoring).

## D8 (2026-10-02) — Agent vs. owner commits
- Decision: agent-made commits use author `Claude Code (agent) <noreply@anthropic.com>`
  and a trailer `Agent: Claude Code (<model id>)`. The committer stays the
  owner's git identity (agents commit only on the owner's request, so
  committer = who approved it). Owner commits use the owner's identity, no trailer.
- Query: agent commits `git log --author='(agent)'`; owner commits
  `git log --perl-regexp --author='^((?!\(agent\)).)*$'`; `git blame` shows
  the agent author on agent-written lines.
- Consequences: existing agent commits (0edeeac, 24ba55f, pre-rewrite hashes)
  were re-authored this way; `3df24c7` "first commit" is the owner's.
