# Decisions

What is currently decided, grouped by topic, with the reason. This is a
register, not a log: when a decision changes, edit the entry; delete entries
that no longer matter (git keeps the history). Each entry is a few lines:
the decision, why, and what it means for future work. IDs are stable anchors
for cross-references; give new entries the next free number (next: D33).

## Repository, docs and process

- **D1 — Who owns which docs.** `agent-docs/` belongs to agents. Every other
  Markdown file is for humans and is edited only when the owner asks; stale
  ones go to `human-doc-backlog.md`. `src/**/README.md` are short human
  pages that point into `agent-docs/`. `AGENTS.md` (rules) and `agent-docs/`
  are committed; `CLAUDE.md` (a one-line `@AGENTS.md` shim) and `PLAN.md`
  (the owner annotates it inline: read the comments, never overwrite them)
  are git-ignored. Agents maintain `.gitignore`.
- **D2 — Where agents may write.** Only inside this repo. Everything outside
  (the `MLTL_R2U2-` repo, AFP, the REU repo) is read-only reference.
  Third-party code we build against lives as git submodules under
  `external/`, also read-only. No machine paths in agent-docs: use the
  `REPO`/`ROOT`/`AFP`/`REU` placeholders from `project/sources.md`.
- **D7 — History lives in git.** No changelogs or conversation logs anywhere.
  Commit messages say what changed and why. Write dates only for decisions,
  observations of external state, and verification results (with the Verus
  version).
- **D8 — Commit identity.** Agent commits: author `Claude Code (agent)
  <noreply@anthropic.com>`, trailer `Agent: Claude Code (<model id>)`,
  committer = the owner (agents commit only when asked). Find them with
  `git log --author='(agent)'`.
- **D30 — Keep agent-docs small, plain and current; talk to the owner in
  plain words.** Owner's attention is the bottleneck. agent-docs records only
  what a future agent needs: current state, decisions with reasons, hard-won
  technical knowledge. It does not record conversations or who said what.
  No private jargon: plain words, plus the IDs above as cross-references
  only. Never use IDs or agent-docs terms when talking to the owner or in
  human docs. Housekeeping runs on a fixed cadence (see `INDEX.md`
  "Housekeeping").

## Scope and order

- **D9 — Toolchain and in-place verification.** Latest Verus release for this
  repo. R2U2 and WEST will be verified in place as forks added as git
  submodules; the fork URLs are deferred by the owner (open question Q10).
  For R2U2, first reproduce upstream's pinned verification setup (vstd
  2025-08-12, Rust 1.85.1). WEST upstream: https://github.com/zwang271/WEST.
- **D10 — Parser syntax.** AFP-style formulas (`F[0,3](p & q)`) with arbitrary
  identifiers as atoms. C2PO's input language is out of scope. The parser
  returns `usize` atoms plus a symbol table, and prints with the original
  names (see D19). Identifier rules: agent proposes, owner confirms (Q11).
- **D11 — R2U2 target theorem.** `r2u2_core`'s output equals `semantics_mltl`.
  Known bugs may falsify it; handle them when reached (precondition or fix in
  the fork). The Isabelle R2U2 theories guide invariants, not the statement.
- **D12 — Milestone order.** Toolchain → mltl-core → parser → formula
  progression → language partitioning → SAT solver; WEST and R2U2 once their
  forks exist. Reason: the core is shared; the parser makes test formulas
  easy; formula progression is the smallest algorithm.
- **D17 — Extra properties belong in mltl-core.** The non-R2U2 parts of
  `REU/isabelle/MLTL_Properties_Extended.thy` are ported into
  `properties.rs`. R2U2-specific parts (the r2u2-form section and the
  parse tree with auxiliary data, which exists to carry monitor state) wait
  for the R2U2 milestone.
- **D18 — SAT solver source.** The MLTL SAT solver formalization is in
  `REU/isabelle/` (`MLTL_SAT_Solver.thy`, `Fast_MLTL_To_SAT*.thy`, CNF and
  SAT-solver theories). Unpublished, read-only, not yet surveyed.

## Semantics and representation

- **D15 — One formula type.** `Mltl<A>` (in `mltl.rs`) serves spec and exec
  code; variants named after the Isabelle constructors. Bounds are `usize`
  (specs read them as `nat`), so formulas with bounds above `usize::MAX` are
  not covered. Accepted, since executable code can't hold them anyway.
- **D16 — Trace states are finite sets.** Spec traces are `Seq<Set<A>>`
  (finite), whereas Isabelle allows infinite states. Owner: MLTL is a finite
  logic; Isabelle's infinite states are a shortcoming. Every Isabelle theorem
  still ports (we state it for a subset of traces), but Isabelle definitions
  that *build* infinite states need a finite replacement. Record each in the
  correspondence page.
- **D19 — Executable atoms and traces.** Atoms are `usize`. Traces are
  `Vec<HashSet<usize>>`, whose vstd view is exactly `Seq<Set<usize>>`.
  `HashSet` rather than `BTreeSet`, because vstd specifies only
  `HashSet::contains`. Spec definitions stay generic in `A`.
- **D20 — Spec/exec pairs and naming.** A definition meant to run has a spec
  version, the Isabelle definition named `<name>_spec`, plus an exec
  version named `<name>` with `ensures result == <name>_spec(..)`, so every
  lemma about the spec applies to the exec output. Downstream specs refer to
  the spec version. Lemmas keep their Isabelle names. Definitions without an
  exec version keep the plain Isabelle name. Exec loops over intervals
  instead of recursing per time step (stack depth).
- **D22 — Strictly AFP semantics.** Every evaluator implements the AFP
  semantics exactly, including evaluating subformulas on the empty suffix
  past the end of the trace. Tools that stop at the trace end (libmltl) are
  wrong on short traces; we don't model them.

## Evaluators and benchmarks

- **D23 — Two verified evaluators.** `mltl-eval` has `mltl_eval` (top-down) and
  `mltl_eval_bottom_up` (tables per subformula over the positions that
  matter, plus next-true/next-false arrays). Both are proved equal to
  `semantics_mltl`. The owner-requested human doc `src/mltl-eval/EVAL_MLTL.md`
  explains both briefly, with one worked example each, and compares them
  with R2U2. Owner wants it short (about 100 lines). Depth (cost
  recurrences, R2U2 memory analysis) lives in agent-docs:
  `modules/mltl-eval.md`, `project/sources.md`, `project/m10-batched-eval.md`.
- **D24 — Benchmark suite.** `src/mltl-eval/benchmarks/` compares both
  evaluators with libmltl and R2U2's Rust monitor (submodules
  `external/libmltl`, `external/r2u2`) on identical input files.
  Python deps live in a local `.venv`. Results and plots are committed;
  workloads are regenerated. Method: only evaluation is timed. Formulas
  are parsed, or for R2U2 compiled with C2PO, beforehand, and R2U2's monitor
  re-initialisation is excluded. R2U2 is not run on libmltl's workload,
  because most of those formulas trigger its constant-operand hang. Heavy
  workloads (traces up to 2M steps, formulas up to ~1,400 nodes) are built
  so every clause holds everywhere, preventing early exits.
- **D31 — Evaluation is its own crate; optimise first, prove second.**
  `src/mltl-eval` holds the evaluators (top-down, bottom-up, and the
  planned bit-row bottom-up), the benchmark suite, and the human docs on
  algorithms and trace formats. It depends on `mltl-core`. Performance work
  goes: unverified prototype → benchmark → iterate until clearly faster and
  stable → prove. Reason (owner): don't spend proof effort on something that
  turns out slower or still improvable. Each iteration's lessons are kept in
  `modules/mltl-eval.md`, so that if a proof forces a change we know which
  fix costs the least speed.
- **D32 — Only the trace representation changes; no bitwise-over-time
  evaluation.** The next optimisation replaces how atoms are read from the
  trace (bit row per atom instead of a hash set per step). It does not
  change how tables or intervals are computed: no bit-packed tables, no
  shift-and-combine windows. Reason (owner): SABRe (R2U2 group, "Stream
  Analyzer via Bitwise Reasoning", `ROOT/sabre`) already evaluates MLTL with
  bitwise operations over words of time steps. We must not reproduce it,
  and we want to measure what the representation change alone buys.
- **D28 — Batched evaluator shelved.** The bit-parallel, many-traces-at-once
  evaluator is designed but shelved by the owner. Everything needed to
  resume is in `project/m10-batched-eval.md`. On resume, offer an unverified
  prototype first, to measure before proving.
