# Reusable prompt: the two-audience doc system

> **Not project knowledge. Agents working on rust-mltl do not need to read
> this page.** It is bookkeeping: the owner's portable write-up of how this
> repo splits agent-facing from human-facing docs, and why, distilled
> (2026-10-04) from `AGENTS.md`, `INDEX.md`, `decisions.md` (D1, D2, D7,
> D8, D30, D37) and the owner's feedback, so it can be pasted into other
> repos. It is exempt from the ~200-line budget. Edit it only if the
> owner asks, or if this repo's doc conventions change and the owner wants
> the prompt kept in step.

Everything below the line is the prompt, verbatim.

---

# Set up and maintain a two-audience documentation system in this repo

You're working in a repo whose owner wants its documentation reorganized
into two spaces: one for humans and one for AI agents. This pattern
has worked well in another project. Below are the rules, the reasons for
them, and how to adopt them here. Read all of it before changing anything.

## The core idea

A repo has two kinds of readers, and they need opposite things.

- **The human owner** has very little attention to spare, maybe 1/1000
  of what agents can spend. They need short, plain pages that say *what*
  something is and *why*, and link out for depth. Their attention is
  the project's bottleneck, so every line they have to read must earn
  its place.
- **Agents** start every session with no memory. They need long, exact
  detail: file paths, exact names, commands, approaches that failed and
  why, the current state, and the reason behind each decision. Without
  it they rediscover the same facts and repeat the same mistakes.

Mix the two and both get worse. Human docs swell with agent notes and
stop being read. Agent knowledge gets cut to keep human docs tidy, or
gets scattered and goes stale. The fix is to separate them physically
and give each space its own owner and rules.

## Layout

| Path | Audience | Who writes it |
|---|---|---|
| `AGENTS.md` | agents: the rules, the entry point | humans; agents only when asked |
| `CLAUDE.md` (or similar tool-specific file) | a one-line shim, `@AGENTS.md` | git-ignored, so the rules live in one place |
| `agent-docs/` | agents: long-term memory | agents, freely; it's theirs to maintain |
| every other `*.md` (README, design docs, module READMEs) | humans | agents edit only when a human asks in the current task |
| `agent-docs/human-doc-backlog.md` | the bridge between the two | agents log proposed fixes to human docs here |

`AGENTS.md` is short and stable. It covers what the project is, where
things live, the documentation rules, the integrity rules, and working
norms. It sends readers to `agent-docs/INDEX.md` for everything else.

### Suggested `agent-docs/` contents (adapt; reorganize when it stops serving)

- `INDEX.md`: the map. It lists the pages every task should read, has a
  topic → page table, defines the status words, and holds the
  end-of-task checklist and the housekeeping rules. Keep it accurate
  after any reorganization.
- `status.md`: current state only. What exists, what works, what's
  next, when housekeeping last ran, and a list of **finished but
  uncommitted work**. Agents commit only when asked, so the next agent
  needs to know what's sitting in the working tree.
- `decisions.md`: a **register, not a log**. Each entry is a few lines:
  the decision, why, and what it means for future work. Give each a
  stable ID (D1, D2, …) so pages can cross-reference it. When a decision
  changes, edit its entry. Delete entries that no longer matter. Mark
  where a decision came from and when ("owner, 2026-10-03"), and quote
  the owner when the wording carries intent.
- `open-questions.md`: questions that block work and wait on the owner.
  Once answered, the answer moves into `decisions.md` and the question
  is deleted.
- `ideas.md`: possible directions, each with why it might matter and a
  rough cost. The owner decides. Nothing here counts as planned.
- `project/`: goals, scope, plan, architecture, external sources.
- `modules/`: one page per code module. Purpose, key types, invariants,
  strategy, hard parts, failed approaches, performance notes.
- A **ledger of shortcuts and trust**: every assumption, stub, skipped
  check, suppressed lint, mocked dependency, unsafe block, or other
  escape hatch, each with its location, why it's there, and how it
  could be removed. Unrecorded shortcuts aren't allowed.
- **Correspondence pages**, if the code mirrors an external spec, paper,
  API, or reference implementation. One table row per external item,
  with the exact external name, the exact local name, its status, and
  any divergence with its reason. Use exact names on both sides so they
  can be grepped.
- `local-paths.md` (git-ignored): facts about this machine, such as
  absolute paths and installed tools. Committed docs never contain
  machine-specific facts. They use placeholders (`REPO`, `ROOT`, …)
  defined in a sources page.

## Rules for `agent-docs/`

1. **It's the source of truth for agents.** Every task starts by
   reading `INDEX.md` and the pages relevant to the task.
2. **Keep it true.** Code changes, decisions, and newly discovered facts
   get recorded in the same piece of work. A stale page is a bug, so
   fix it when you see it.
3. **Conflict rule.** For *what exists*, the code wins, so fix the doc.
   For *what was intended or decided and why*, the docs win. If the code
   contradicts a recorded decision, flag it to the owner instead of
   quietly "fixing" either side.
4. **Record only what a future agent needs.** That means current state,
   decisions with their reasons, and hard-won technical knowledge:
   exact names, commands, pitfalls, failed approaches. It does **not**
   mean conversation summaries, who said what, step-by-step accounts,
   changelogs, or superseded material. **Git is the history.** Commit
   messages say what changed and why.
5. **Be honest about certainty.** Mark claims `VERIFIED` (with the
   command, tool version, and date), `PARTIAL`, `ASSUMED` (and in the
   ledger), `PLANNED`, or `UNKNOWN`. Never write that something works or
   passes unless you ran it in this session.
6. **Use absolute dates** (YYYY-MM-DD). Only date decisions,
   observations of external state, and verification results.
7. **Size budget.** Keep pages to about 200 lines. Past that, tighten or
   split.
8. **Plain language here too.** Internal IDs are fine as
   cross-references between agent pages. Private jargon that only makes
   sense after reading ten other pages isn't. Write so a fresh agent
   can follow.

## Rules for human-facing docs

1. **Don't edit an existing human doc unless a human asks for that edit
   in the current task.** If you notice it's stale or wrong, add an
   entry to `human-doc-backlog.md` (file, what's wrong, proposed text,
   date) and tell the owner in plain words. Remove the entry once it's
   applied.
   *Why:* human docs are the owner's voice and the project's public
   face. Agents "helpfully" rewriting them causes slow drift the owner
   never approved and has to re-read everything to catch. The backlog
   keeps agents useful without letting them take over.
2. **Exception:** when a task the human asked for creates a new module
   directory, create that directory's short README and mention it in
   your report.
3. **Module READMEs serve both readers.** A few sentences for humans
   (what it does and why, and the single most important thing to look
   at, such as the main entry point or the function whose contract
   states the guarantee), then one line for agents:
   `Agent context: [agent-docs/modules/x.md](...)`. Aim for under 40
   lines. Depth goes in `agent-docs/`.
4. **Lead the reader to what matters most.** Don't catalogue everything.
   Link the one or two things a newcomer actually wants, such as the
   main function and its stated contract or the key example.
5. **Every mention of a file or directory is a relative link.** It's
   basic courtesy to the reader.
6. **Never put agent-only content in human docs:** todo lists, scratch
   notes, debugging logs, internal IDs.
7. If the owner keeps a personal plan or notes file they annotate
   inline, it's git-ignored. Read their comments and never overwrite
   them.

## Talking to the owner

- Plain words only. **Never** cite internal IDs (D17, Q4, T2.3) or
  other agent-docs terms in messages or human docs. Say what you mean.
- Lead with what matters: the result, the decision needed, the risk.
  Keep reports short.
- When explaining a distinction or how something works, start with one
  tiny concrete worked example with real values, then scale up in a
  sentence or two. Abstract bullet lists and comparison tables often
  fail. If the owner asks for clarification twice, switch to an example
  rather than rephrasing.
- Ask only about decisions that are really the owner's to make, and
  record the answer in `decisions.md`.

## Integrity and working norms

- Work only inside this repo. Everything outside it (other repos,
  upstream sources, vendored or submodule code) is read-only reference
  unless the owner says otherwise.
- Don't weaken a test, spec, or check to make something pass without
  recording the change and the reason.
- Report results faithfully. If something fails or times out, say so
  and show the output.
- Make small, verifiable increments. Leave the tree passing, or record
  exactly what's broken in `status.md`.
- Commit only when asked. When committing, make agent commits easy to
  tell apart (for example, author `<Agent name> (agent) <noreply@…>`
  plus a trailer naming the model), with the owner as committer.
- Use inclusive terminology.
- **Turn doc invariants into scripts once they rot.** Line anchors,
  dead links, and unlinked file references drift silently. A small
  checker script that agents run before finishing any doc-touching task
  (with a `--fix` mode where it can be done safely) beats relying on
  discipline.

## End of every task

1. `status.md` is true, and uncommitted work is listed there.
2. New decisions and answered questions are recorded by editing
   entries, not appending duplicates.
3. New shortcuts or trust are in the ledger. New external-to-local
   mappings are in the correspondence pages.
4. Doc checks (link checker and similar) pass.
5. Stale human docs found along the way are in the backlog, and you've
   told the owner.

## Housekeeping (on a fixed cadence, not "when it feels messy")

Trigger it when a milestone finishes, when `decisions.md` has gained
about 8 entries since the last pass, when any page goes over its size
budget, or when the owner asks. Record the date in `status.md`.

1. **True:** check every claim in status, plan, and module pages
   against the code. Rerun the build and tests.
2. **Prune:** delete superseded detail. Finished tasks shrink to one
   line. Merge duplicate decisions. Drop stale numbers and paths.
3. **Plain:** strip jargon that has crept in. Review the human-doc
   backlog.
4. **Reflect:** reread the goals, the decisions, and recent commits.
   Update `ideas.md` with what was learned, the risks, and new
   directions.
5. **Report to the owner** in about 10 plain lines or fewer: what
   changed, the 1–3 most interesting ideas, and any decision needed.
   No IDs, no tour of the docs.

## Why this works (and what goes wrong without it)

- **Separate ownership removes the tension.** Agents can be as verbose
  as they need in their own space without spending the owner's
  attention. Human docs stay short because nothing else needs to live
  there.
- **Registers beat logs.** Agent docs naturally turn into append-only
  diaries full of conversation summaries and private shorthand. That
  happened in the original project until the first housekeeping pass
  cut it back. A register of *current* truth, with git holding history,
  stays readable for the next agent.
- **The backlog is a pressure valve.** Agents notice stale human docs
  all the time. Without a sanctioned place to put that, they either
  overstep and edit, or say nothing.
- **Stating certainty and keeping a ledger make claims trustworthy.**
  The owner can believe "verified" or "passes" because every claim
  names its evidence, and every shortcut lives in one place.
- **Decisions keep their reasons.** Later agents don't reopen settled
  questions, and when circumstances change, it's clear which decisions
  depend on them.
- **The fixed cadence stops slow decay.** Docs rot gradually, not
  suddenly. Fixed triggers catch it before it compounds.

## Adopting this in an existing repo

1. Survey first. List every Markdown file and doc-like file and sort
   each as human-facing, agent-facing, or mixed. Look for existing agent
   instruction files (`CLAUDE.md`, `.cursorrules`, `AGENTS.md`,
   `.github/copilot-instructions.md`) and fold them into `AGENTS.md`.
2. Propose the plan to the owner in plain words before moving or
   rewriting any human-facing file: what moves where, what gets created,
   what you'd trim. Their approval counts only for the files they
   approve.
3. Create `AGENTS.md`, the `CLAUDE.md` shim, `agent-docs/INDEX.md`,
   `status.md`, `decisions.md`, `open-questions.md`,
   `human-doc-backlog.md`, the ledger, and `.gitignore` entries for
   local-only files. Seed `decisions.md` with the decisions you can see
   in the code and the existing docs, each marked with its source.
4. Move agent-type content (debugging notes, task lists, internal
   design rationale) out of human docs into `agent-docs/` only with
   approval. Otherwise, log it in the backlog.
5. Fill in project-specific sections of `AGENTS.md` (what the project
   is, its integrity rules, build and test commands), keeping
   project-specific detail in `agent-docs/`.
6. Report what you did in a few plain lines.
