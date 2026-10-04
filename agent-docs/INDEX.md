# agent-docs

Agents' working memory for this project. Start here; read the "always" pages,
then what your task needs. Ground rules are in `../AGENTS.md` §3–5.

## What belongs here (D30)
- Current state, decisions with their reasons, and hard-won technical
  knowledge: correspondence tables, Verus pitfalls, facts about external
  tools. Nothing else.
- Not here: conversation summaries, who-said-what, step-by-step narratives,
  superseded material. Git has the history.
- Plain language. IDs (D… decisions, Q… questions, T… tasks, M… milestones)
  are allowed as cross-references between these pages, but **never** use
  them, or any other agent-docs term, when talking to the owner or writing
  human docs. Say what you mean in words.
- Size budget: about 200 lines per page. Over that, tighten or split.

## Always read
- `status.md`: what exists, what's next.
- `decisions.md`: current decisions and why.
- `open-questions.md`: what is waiting on the owner.
- `project/goals.md`: goals, scope, principles.

## By topic
| Topic | Page |
|---|---|
| Where every external source lives (placeholders `REPO`, `ROOT`, `AFP`, `REU`) | `project/sources.md`; this machine's paths: `local-paths.md` (git-ignored) |
| Milestones and tasks | `project/plan.md` (owner's summary: `../PLAN.md`) |
| Shelved batched-evaluator design | `project/m10-batched-eval.md` |
| Ideas and possible new directions | `ideas.md` |
| Planned crate layout | `project/architecture.md` |
| Verus: toolchain, commands, pitfalls | `verification/verus-notes.md` |
| Everything trusted without proof | `verification/trusted-base.md` |
| Isabelle ↔ Rust tables | `correspondence/` |
| Per-module notes | `modules/` (`mltl-core.md`, `mltl-eval.md`, `formula-progression.md`, `mltl-parse.md`) |
| Human docs that need an owner-approved fix | `human-doc-backlog.md` |
| Throwaway spikes (not built) | `verification/spikes/` |

Status words: `VERIFIED` (Verus accepted it; give version and date),
`PARTIAL`, `ASSUMED` (trusted, listed in the ledger), `PLANNED`, `UNKNOWN`.

## End of every task
1. `status.md` is true; uncommitted work is listed there.
2. Decisions and answered questions are recorded (edit entries, don't append
   duplicates).
3. New trust goes in `verification/trusted-base.md`; new Isabelle mappings in
   `correspondence/`.
4. When committing: the message says what changed and why; commit as the
   agent (D8): `git commit --author="Claude Code (agent) <noreply@anthropic.com>" --trailer "Agent: Claude Code (<model id>)"`.

## Housekeeping
Run it when any of these happens, and note the date in `status.md`:
- a milestone finishes;
- `decisions.md` gains about 8 entries since the last pass, or any page
  exceeds its size budget;
- the owner asks.

Checklist:
1. **True:** check every claim in `status.md`, `plan.md`, and module pages
   against the code (rerun `scripts/verify.sh`).
2. **Prune:** delete superseded or finished detail (done tasks become one
   line), merge duplicate decisions, drop stale numbers and paths.
3. **Plain:** remove jargon that has crept in; check `human-doc-backlog.md`.
4. **Reflect:** reread `project/goals.md`, `decisions.md` and recent commits,
   and update `ideas.md`: what we learned, risks, new directions.
5. **Report to the owner** in at most ~10 plain lines: what changed, the 1–3
   most interesting ideas, and any decision needed. No IDs, no doc tour.
