# AGENTS.md — rust-mltl

Read this before you touch anything in `rust-mltl/`. Then read [`agent-docs/INDEX.md`](agent-docs/INDEX.md).

## 1. What this project is

`rust-mltl/` is a Rust + [Verus](https://github.com/verus-lang/verus) library that
re-establishes the existing Isabelle/HOL formalizations of the Mission-time LTL
(MLTL) ecosystem as **verified, executable Rust**. It replaces the current
workflow of "prove in Isabelle → extract SML/Haskell → write an untrusted parser
→ conformance-test against the real tool".

Goals (details and rationale: [`agent-docs/project/goals.md`](agent-docs/project/goals.md)):

1. **Faithful encoding.** Port the formalized MLTL ecosystem into Verus with
   specs that correspond, definition by definition, to the Isabelle sources:
   MLTL syntax/semantics (AFP `Mission_Time_LTL`), WEST (AFP
   `Mission_Time_LTL_to_Regular_Expression`), formula progression (AFP
   `Mission_Time_LTL_Formula_Progression`), language partitioning (AFP
   `Mission_Time_LTL_Language_Partition`), R2U2 (in-progress Isabelle work in
   the `MLTL_R2U2-` repo, `isabelle/`), and the MLTL SAT solver (verified, unpublished).
2. **Reusable library.** A modular core (syntax, semantics, traces, common
   lemmas) that future MLTL algorithms can build and verify against.
3. **Verify R2U2.** First an idealized version of its algorithm, verified
   here against MLTL semantics (the open research question, also pursued in
   Isabelle). Later, along a recorded path, its memory bounds and the real
   Rust monitor source (`r2u2_core`).
4. **Port and verify WEST.** A faithful port of the AFP WEST entry plus a
   fast bit-packed version proved equivalent; the upstream WEST repo
   (Zili Wang's) stays as is.
5. **Port and verify** formula progression and language partitioning in Rust.
6. **Remove the untrusted parser.** Parsing from concrete syntax to the
   verified AST is itself specified and verified.

## 2. Where things live

| Path | Audience | Who may write it |
|---|---|---|
| `AGENTS.md` (this file) | agents | humans; agents only when a human asks |
| [`README.md`](README.md), any other `*.md` outside [`agent-docs/`](agent-docs/) (incl. `src/**/README.md`) | **humans** | see §3.2 |
| `agent-docs/` | agents | agents, freely — it is ours to maintain |
| [`src/`](src/) | both | Rust code + Verus proofs, plus short READMEs |

Work **only inside this repo (`rust-mltl/`)**. Everything outside it
(the `MLTL_R2U2-` repo with its `isabelle/` and `r2u2/`, the AFP, …; paths in [`agent-docs/project/sources.md`](agent-docs/project/sources.md)) is read-only reference material unless
the human explicitly says otherwise.

## 3. Code of conduct for documentation

### 3.1 `agent-docs/` is the source of truth for agents

- It is the long-term memory of this project. Any agent starting a task MUST
  consult [`agent-docs/INDEX.md`](agent-docs/INDEX.md) and the pages relevant to the task first.
- Keep it **true**. If you change code, decisions, status, or discover a fact,
  update the relevant `agent-docs/` page in the same piece of work. A stale
  page is a bug; fix it when you see it.
- Conflict rule: for *what exists*, the code wins — fix the doc. For *what we
  intend / decided and why*, `agent-docs/` wins — if code contradicts a
  recorded decision, flag it rather than silently "fixing" either side.
- Be verbose where it helps the next agent: record paths, exact Isabelle
  lemma/definition names, commands, failed approaches and why they failed.
- Record uncertainty honestly: mark items as `VERIFIED`, `PARTIAL`,
  `ASSUMED`, `PLANNED`, or `UNKNOWN`. Never write that something is verified
  unless Verus actually accepted it, and say which command/version you ran.
- Structure is flexible; reorganize when it stops serving. Keep
  [`agent-docs/INDEX.md`](agent-docs/INDEX.md) an accurate map after any reorganization.
- Date log entries with absolute dates (YYYY-MM-DD).

### 3.2 Human-facing docs

Every Markdown file outside `agent-docs/` (except this file) is for humans.

- They MUST be readable by a human seeing the repo for the first time:
  short, plain, explain *what* and *why*, link out for depth.
- Agents MUST NOT edit an existing human-facing doc unless a human asks for
  that edit in the current task. If you notice one is stale or wrong, add an
  entry to [`agent-docs/human-doc-backlog.md`](agent-docs/human-doc-backlog.md) and tell the human.
- Exception: when a human-requested task creates a **new** directory under
  `src/`, the agent creates that directory's `README.md` (see §3.3) as part
  of the task and mentions it in its report.
- Never put agent-only context (todo lists, scratch notes, proof-debugging
  logs) in human-facing docs. That belongs in `agent-docs/`.

### 3.3 `src/**/README.md`

Each meaningful module directory under `src/` gets a short README that serves
two readers:

1. **Human:** a few sentences on what the module does, what it proves, and
   which Isabelle theory/definitions it corresponds to.
2. **Agent:** an "Agent context" line pointing to the exact `agent-docs/`
   pages to grep for detail, e.g.
   "Agent context: [agent-docs/correspondence/west.md](agent-docs/correspondence/west.md),
   [agent-docs/modules/west.md](agent-docs/modules/west.md)".

Keep these short (aim < 40 lines). Depth goes in `agent-docs/`.

## 4. Verification integrity rules

- Every `assume`, `admit`, `#[verifier::external_body]`,
  `#[verifier::external]`, axiom, or `uninterp` spec MUST be recorded in
  [`agent-docs/verification/trusted-base.md`](agent-docs/verification/trusted-base.md) with location and justification.
  Unrecorded trust is not allowed.
- Do not weaken a spec to make a proof go through without recording the
  change and why in `agent-docs/` (and, if it diverges from Isabelle, in the
  relevant [`agent-docs/correspondence/`](agent-docs/correspondence/) page).
- Specs should mirror the Isabelle definitions. When Rust needs a different
  shape (e.g. `Vec` vs `list`, `usize` vs `nat`, bounded integers), document
  the correspondence and the bridging lemma.
- Report results faithfully: if Verus fails or times out, say so with output.

## 5. Working norms

- Prefer small, verifiable increments; leave the tree in a state where
  verification passes, or record precisely what is broken in
  [`agent-docs/status.md`](agent-docs/status.md).
- Use inclusive terminology (no master/slave/whitelist/blacklist).
- Don't commit or push unless the human asks.
