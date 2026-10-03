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

## D9 (2026-10-02) — Verus version; in-place mechanism (resolves Q4, Q1, Q2)
- Owner answers to `PLAN.md` decisions 1–3.
- Verus: rust-mltl uses the latest Verus release. Separately reproduce
  upstream `r2u2_core`'s pinned `vstd 0.0.0-2025-08-12-1837` / rust 1.85.1
  (T8.1) before porting R2U2 work to latest.
- In place: fork the upstream repos; bring forks in as git submodules under
  `vendor/` (proofs can be upstreamed via PRs). Fork URLs: Q10.
- WEST upstream: https://github.com/zwang271/WEST
- Q3 (SAT) deferred by owner.

## D10 (2026-10-02) — Parser syntax (resolves Q6)
- AFP-style concrete syntax (e.g. `F[0,3](p & q)`), but atoms are arbitrary
  identifiers, not only `p<n>`/`a<n>`. C2PO input language out of scope (too
  broad). Identifier lexical rules: Q11.
- Consequences: parser output needs atoms beyond `nat` — e.g. `Formula<String>`
  or interned ids + symbol table mapping to `Formula<nat>` for WEST/R2U2. Decide
  in T3.1/T3.2. R2U2 binary decoding (T8.9) still planned separately.

## D11 (2026-10-02) — R2U2 target theorem (resolves Q7)
- Target: `r2u2_core` output matches MLTL semantics (`semantics_mltl`), not
  refinement of the Isabelle R2U2 model. Owner knows of bugs (`ROOT/*_BUG.md`)
  that may falsify it unconditionally; handle when reached (likely added
  preconditions or fixes in the fork). Isabelle R2U2 theories remain a guide
  for invariants and proof structure.

## D12 (2026-10-02) — Milestone order (PLAN.md decision 7)
- Parser before formula progression: M1 → M2 → M3 parser → M4 progression →
  M5 → M6/M8 as unblocked; M7 deferred (Q3). Parser also gives a convenient
  way to write test formulas for later milestones.

## D13 (2026-10-02) — Trace states are `ISet<A>`
- Context: vstd (0.0.0-2026-09-20) splits finite `Set` from possibly-infinite
  `ISet`. Isabelle `semantics_mltl :: 'a set list ⇒ ...` allows infinite sets.
- Decision: spec traces are `Seq<ISet<A>>`, mirroring `'a set list` exactly.
  Exec traces get a `view` into that type (e.g. `Vec<Vec<bool>>` → `Seq<ISet<nat>>`).
- Consequences: use ISet lemmas (`group_iset_lemmas`). If an algorithm needs
  finiteness (e.g. cardinality), state it as an explicit precondition and note
  the divergence in its correspondence page.

## D14 (2026-10-02) — Q10 (fork URLs) deferred by owner
- Owner wants to reach mltl-core first. M6 (WEST) and M8 (R2U2) stay blocked
  on Q10 until revisited. Q11 (identifier rules): agent proposes in T3.1,
  owner confirms — agreed.
