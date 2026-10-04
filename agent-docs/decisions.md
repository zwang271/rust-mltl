# Decisions

What is currently decided, grouped by topic, with the reason. This is a
register, not a log: when a decision changes, edit the entry; delete entries
that no longer matter (git keeps the history). Each entry is a few lines:
the decision, why, and what it means for future work. IDs are stable anchors
for cross-references; give new entries the next free number (next: D41).

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
  `external/`, also read-only. No machine-specific facts in anything committed (owner, 2026-10-03):
  no paths, user names or hardware. Use the `REPO`/`ROOT`/`AFP`/`REU`
  placeholders from `project/sources.md`; where they point on this machine,
  and other local facts, go in the git-ignored `local-paths.md`.
- **D7 — History lives in git.** No changelogs or conversation logs anywhere.
  Commit messages say what changed and why. Write dates only for decisions,
  observations of external state, and verification results (with the Verus
  version).
- **D8 — Commit identity.** Agent commits: author `Claude Code (agent)
  <noreply@anthropic.com>`, trailer `Agent: Claude Code (<model id>)`,
  committer = the owner (agents commit only when asked). Find them with
  `git log --author='(agent)'`.
- **D37 — READMEs lead to the guarantee** (owner, 2026-10-03). Each crate
  README links (file#Lline) to the main exec function, whose `ensures`
  states the correctness property itself, not just `r == <name>_spec(..)`.
  Beyond that it links only the definitions and lemmas needed to read that
  guarantee (semantics, terms in the statement, the main theorems). Line
  anchors rot: after editing any linked file run `scripts/readme_links.py`
  (`--fix` repairs line numbers). Done for formula_progression, mltl-core
  and mltl-eval (2026-10-03).
  **Every file reference is a link** (owner: "basic courtesy"): in every
  human doc (all `*.md` outside agent-docs/, plus `AGENTS.md`, `PLAN.md`),
  any mention of a file or directory in the repo is a relative link,
  including "Agent context" lines; a directory needs one link per doc.
  `scripts/readme_links.py` (no args) checks line links, dead relative
  links and unlinked file references. Run it before finishing any task that
  touches docs or linked code.
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
- **D10 — Parser syntax** (owner, 2026-10-02/03). The spec is
  `src/mltl-parse/GRAMMAR.md` (owner reviews it line by line; it is the only
  definition of "correct parser", so keep code and spec in lockstep).
  AFP-style formulas, plus `->`, `<->` (AFP `Implies_mltl`/`Iff_mltl`) and
  `^` (xor, libmltl; meaning `(a & !b) | (!a & b)`), all desugared to core
  constructors. Constants `true`/`false`; `t`/`tt`/`f`/`ff` are reserved
  keywords meaning the same (so libmltl formulas never silently read them
  as atom names). `&`, `^`, `|`
  chain left-associatively; `U`/`R` and `->`/`<->` chains need parentheses.
  Ill-formed intervals (`a > b`) are rejected by the parser. Identifiers:
  ASCII letter or `_` then letters/digits/`_`, case-sensitive; keywords
  `F G U R true false` are never names. `p<N>` names keep the libmltl/WEST
  meaning (atom N). C2PO's input language is out of scope. The parser
  returns names; a verified numbering step maps them to `usize` atoms plus a
  table (D19): `p<N>` (no leading zeros) is atom N; other names get the next
  free number in order of first appearance, after the largest `p<N>`.
  Tokens use longest match with no exceptions: libmltl's unspaced
  `p0U[0,2]` is the name `p0U` (owner, 2026-10-03; libmltl input needs a
  space before `U`/`R`).
- **D11 — R2U2 target theorem.** `r2u2_core`'s output equals `semantics_mltl`.
  Known bugs may falsify it; handle them when reached (precondition or fix in
  the fork). The Isabelle R2U2 theories guide invariants, not the statement.
- **D12 — Milestone order.** (Progression moved before the parser: D33.) Toolchain → mltl-core → parser → formula
  progression → language partitioning → SAT solver; WEST and R2U2 once their
  forks exist. Reason: the core is shared; the parser makes test formulas
  easy; formula progression is the smallest algorithm.
- **D17 — Extra properties belong in mltl-core.** The non-R2U2 parts of
  `REU/isabelle/MLTL_Properties_Extended.thy` are ported into
  `properties.rs`. The r2u2-form section waits for the R2U2 milestone. The
  parse tree with auxiliary data is ported (`mltl-core/src/parse_tree.rs`,
  D39), since language partitioning needs it.
- **D38 — Language partitioning before the parser** (owner, 2026-10-03).
  Like D33, supersedes D12's order for this step; the parser is being done
  in parallel by another session. Scope: the whole AFP entry (algorithm,
  union and both disjointness theorems); `Codegen.thy` waits for the
  verified printer (T5.6).
- **D33 — Formula progression before the parser** (owner, 2026-10-03).
  Supersedes the parser-first order in D12 for this one step. Scope: the
  AFP theory and the unpublished `Formula_Progression_Extended.thy`
  (simplifier, `prog`, `prog_early_eval`); owner: "definitely want it
  integrated with the simplifier". Reason: plain progression grows the
  formula without bound, so only `prog` is useful in practice.
- **D18 — SAT solver source.** The MLTL SAT solver formalization is in
  `REU/isabelle/` (`MLTL_SAT_Solver.thy`, `Fast_MLTL_To_SAT*.thy`, CNF and
  SAT-solver theories). Unpublished, read-only, not yet surveyed.

## Semantics and representation

- **D34 — Formula progression crate layout** (owner chose the directory,
  2026-10-03). Crate `src/formula_progression` (package `formula_progression`,
  not `mltl-*`: the owner kept the existing directory). It depends on
  `mltl-eval` only for the executable `Trace` / `trace_view` (and uses
  `mltl_eval` in tests). If more crates need traces, move `trace.rs` into
  `mltl-core` instead of depending on the evaluators.
- **D39 — `mltl_ext` is the parse tree** (owner's idea, 2026-10-03).
  Isabelle's `'a mltl_ext` (compositions on F/G/U/R) is
  `MltlParseTree<A, Seq<usize>>` (spec) / `MltlParseTree<usize, Vec<usize>>`
  (exec, viewed by `ext_view`), not a separate datatype. Reason: one
  formula-with-data type for language partitioning and, later, R2U2 monitor
  state. Consequences: data off temporal nodes is ignored (theorems hold for
  any), new nodes get `[]`; `convert_nnf_ext` must say whose data a rewritten
  node keeps (the replaced node's). Spec data is `Seq` so proofs never
  compare `Vec`s. Crate `src/language_partitioning` (package
  `language_partitioning`, the existing directory, as D34); `size_mltl`
  moved from formula_progression into `mltl-core/src/mltl.rs`, since the
  parse-tree size lemma needs it.
- **D40 — No differential test against Isabelle for language partitioning**
  (owner, 2026-10-03). Exec is proved equal to the spec, and the Isabelle
  `value` examples are runtime tests; no Haskell export, no benchmark.
- **D35 — Shared exec helpers live in mltl-core.** `take` (total, Isabelle
  `take`), `clone_mltl` (verified deep copy) and `eq_mltl` (verified
  structural equality) are in `mltl-core/src/mltl.rs`, since any algorithm
  that returns subformulas or compares formulas needs them. No `derive`s on
  `Mltl` (Verus's handling of derived impls unchecked).

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

- **D36 — Exec code that rebuilds formulas takes ownership.** Functions
  whose result reuses parts of the input (progression, simplifiers) take
  `Mltl<usize>` by value, move subformulas and reuse boxes (`*b = f(*b)`);
  borrowed wrappers (`prog(&f)`) copy once at the entry. Reason: measured
  2026-10-03, copying made the verified `prog` 3–5× slower than the
  Isabelle-exported Haskell, 75% of the time in malloc/free; moving fixed it.

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
