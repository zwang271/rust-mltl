# agent-docs — index (source of truth for agents)

Start here. Read the "always" pages, then whatever matches your task.
Rules for maintaining this folder live in `../AGENTS.md` §3.1.

## Always read
- `status.md` — what exists right now, what's in flight, what's broken.
- `project/goals.md` — the six goals, scope, non-goals, guiding principles.
- `decisions.md` — decision log (append-only; supersede, don't delete).
- `open-questions.md` — unresolved questions that block or shape work.

## By topic
| Topic | Page |
|---|---|
| Where every upstream formalization / implementation lives | `project/sources.md` |
| Planned crate/module layout | `project/architecture.md` |
| Phased plan (coarse) | `project/roadmap.md` |
| Task-level work plan (milestones M0–M9, task IDs T*.*) | `project/plan.md` (human summary: `../PLAN.md`) |
| M10 batched (bit-parallel) evaluator design, SHELVED | `project/m10-batched-eval.md` |
| Verus toolchain, versions, how to run, Verus gotchas | `verification/verus-notes.md` |
| Throwaway feasibility spikes (not built) | `verification/spikes/` |
| Ledger of every trusted assumption (`assume`, `external_body`, …) | `verification/trusted-base.md` |
| Isabelle ↔ Rust correspondence tables (one page per component) | `correspondence/` (exists: `mission-time-ltl.md`) |
| Per-module design notes (one page per `src/` module, created as modules appear) | `modules/` (exists: `mltl-core.md`) |
| Human-facing docs that need a human-approved update | `human-doc-backlog.md` |

## Status vocabulary
`VERIFIED` (Verus accepted; note version + command) · `PARTIAL` · `ASSUMED`
(trusted, in ledger) · `PLANNED` · `UNKNOWN`.

## Maintenance checklist (run at end of every task)
1. `status.md` reflects reality (snapshot only; list uncommitted work there).
2. New decisions → `decisions.md`; resolved questions moved out of `open-questions.md`.
3. New trust → `verification/trusted-base.md`.
4. New/changed spec ↔ Isabelle mapping → `correspondence/<component>.md`.
5. This index still lists every page.
6. If asked to commit: the commit message is the history entry (D7) — say
   what changed and why, reference D/Q/T IDs. Commit as the agent (D8):
   `git commit --author="Claude Code (agent) <noreply@anthropic.com>" --trailer "Agent: Claude Code (<model id>)" -m ...`

## History and dates (D7)
- Chronology of edits = git (`git log`, `git blame`). Don't keep manual changelogs.
- Do write dates for: decision entries; facts about *external* state
  ("upstream r2u2 has X as of YYYY-MM-DD", survey dates); verification claims
  (date + Verus version + command). Git can't tell when the outside world was
  observed, or which tool produced a result.
