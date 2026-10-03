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

## D13 (2026-10-02) — Trace states are `ISet<A>` — SUPERSEDED by D16
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

## D15 (2026-10-02) — Formula type `Mltl<A>` (T2.1)
- Decision: one generic enum `Mltl<A>` in `src/mltl-core/src/mltl.rs`, used by
  both spec and exec code; named after Isabelle `'a mltl`, variants named after
  the constructors minus the `_mltl` suffix. Interval bounds are `usize`,
  read as `nat` in specs.
- Why: T1.4 spike showed a single enum works in spec and exec; a separate
  spec type with `nat` bounds would double every definition and need a view.
- Divergence: bounds above `usize::MAX` are unrepresentable (Isabelle `nat`
  is unbounded). Theorems quantify over `Mltl<A>`, so they cover only such
  formulas — acceptable since exec code can't hold larger bounds anyway.
  Arithmetic on bounds in specs is done in `nat`/`int` (no overflow); exec
  code needs overflow preconditions.

## D16 (2026-10-02) — Trace states are finite `Set<A>` (supersedes D13)
- Owner decision: Isabelle's `'a set list` admitting infinite states is a
  shortcoming of the formalization. Traces are finite lists of finite sets;
  MLTL is a finite logic and everything about it should be finite.
- Decision: spec traces are `Seq<Set<A>>` (vstd finite sets). Deliberate
  divergence from Isabelle, recorded in `correspondence/mission-time-ltl.md`.
- Consequences: Isabelle theorems quantifying over all traces still port (we
  state them for a subset of traces). Watch for Isabelle proofs/definitions
  that *build* traces with possibly-infinite states (complements, `UNIV`,
  set comprehensions over infinite types): those need a finite replacement —
  record each in the relevant correspondence page. Exec trace views must
  produce finite sets (e.g. `Seq::to_set`, or `Set::new(..)` which returns
  `Option` in this vstd). Lemma group: `vstd::set::group_set_lemmas`.

## D17 (2026-10-02) — Port MLTL_Properties_Extended into mltl-core, minus R2U2
- Owner: the extra properties in `REU/isabelle/MLTL_Properties_Extended.thy`
  belong in `properties.rs`; drop everything R2U2-related (it belongs with the
  R2U2 formalization).
- Agent judgement on what counts as R2U2: the `r2u2 Form` section and the
  `mltl_parse_tree` datatype + lemmas (its documentation says it exists to
  attach SCQ/observer state during monitoring). Everything else ported.
  Revisit the parse tree when starting M8.

## D18 (2026-10-02) — SAT solver source located (resolves Q3)
- Owner confirmed: the MLTL SAT solver formalization is in `REU/isabelle/`
  (`MLTL_SAT_Solver.thy`, `MLTL_To_SAT.thy`, `Fast_MLTL_To_SAT*.thy`, CNF/
  Tseytin/SAT-solver theories; commit `14fdbbe` surveyed 2026-10-02).
  Unpublished; read-only like all sources.
- Consequences: M7 is no longer blocked on a source; it keeps its place in the
  milestone order (after M5; D12 order otherwise unchanged). Its theories
  build on `MLTL_Properties_Extended` (already ported, D17). T7.1 survey still
  to do.

## D19 (2026-10-02) — Exec atoms are `usize`; exec traces are `Vec<HashSet<usize>>`
- Owner: `usize` atoms, provided verified parsing still reads nicely (parser
  must return a symbol table id ↔ identifier and print with names; M3 req).
- Exec trace type `Vec<HashSet<usize>>` (owner asked why not a set per
  step; agreed): its vstd view is exactly the spec trace `Seq<Set<usize>>`
  (no translation layer), compact for sparse/large ids, matches D16.
  `HashSet` over `BTreeSet` because vstd 0.0.0-2026-09-20 specifies
  `HashSet::contains` but not `BTreeSet::contains`. Relies on vstd's trusted
  std specs for `HashSet` (record in trusted-base when first used).
- Spec layer stays generic in `A`.

## D20 (2026-10-02) — Spec + exec pairs for executable definitions
- `convert_nnf`, `convert_bnf`, `mltl_eval` stay spec fns (Isabelle
  definitions; downstream specs/lemmas refer to them as terms). Each gets an
  exec fn with `ensures result == spec(...)` (refinement), so all proven
  properties transfer. Exec `mltl_eval` loops over intervals (no recursion
  per time step: stack depth would equal interval width).

## D21 (2026-10-03) — Naming: exec fn gets the plain name, spec gets `_spec`
- Owner: when a definition has an executable version, the exec fn is named
  plainly (`convert_nnf`) and the spec fn gets the suffix (`convert_nnf_spec`).
- Applied: `convert_nnf_spec`, `convert_bnf_spec`, `mltl_eval_spec`,
  `mltl_eval_unchecked_spec` (+ their `via` fns). Lemma names keep the
  Isabelle names (`convert_nnf_convert_nnf`, `mltl_eval_correct`, …).
  Definitions without an exec version keep the Isabelle name
  (`semantics_mltl`, `complen_mltl`, …) until they get one.

## D22 (2026-10-03) — Strictly AFP semantics; libmltl is wrong on short traces (resolves Q12)
- Owner: all evaluators implement AFP semantics exactly. libmltl's
  behaviour of clamping temporal windows at the trace end (no evaluation on
  the empty suffix) is a bug in an external tool that incorrectly
  implements MLTL semantics for short traces. No libmltl-compatible
  semantics will be specified.

## D23 (2026-10-03) — Two verified evaluators in `eval.rs`, documented in `EVAL.md`
- Owner: both evaluators live in `src/mltl-core/src/eval.rs`; the human doc
  `src/mltl-core/src/EVAL.md` explains the algorithms and complexities
  (academic quality, examples, not jargon-heavy).
- `mltl_eval` (top-down, loops over intervals) and `mltl_eval_bottom_up`
  (tables per subformula with horizons + next-true/next-false arrays). Both
  `ensures r == semantics_mltl(trace_view(t@), *f)`.

## D24 (2026-10-03) — Benchmarks in `src/mltl-core/benchmarks`, libmltl as submodule
- Owner: comprehensive benchmark + matplotlib plotting scripts in
  `src/mltl-core/benchmarks/`; libmltl pulled in as a git submodule at
  `external/libmltl` (new top-level `external/` for third-party code).
- Pinned at libmltl commit `19d8cfc`. Read-only reference / baseline; never
  modified (AGENTS.md workspace rule applies to its contents).
- Python deps in `benchmarks/requirements.txt`, installed into a local
  `.venv` (git-ignored, as are `workloads/` and `build/`). `results/` and
  `plots/` are outputs meant to be reviewed (not ignored).
- The old `examples/bench_libmltl.rs` is replaced by `benchmarks/driver.rs`
  (cargo example `bench_driver`).

## D25 (2026-10-03) — R2U2 in the benchmarks (`external/r2u2` submodule)
- Owner: add https://github.com/R2U2/r2u2 as submodule `external/r2u2`;
  benchmark the Rust monitor (not the C one) alongside the others.
- `external/r2u2` is a read-only benchmark dependency, distinct from the
  future in-place-verification fork (Q10, M8).
- Driver `src/mltl-core/benchmarks/r2u2_driver/`: separate crate (own
  `[workspace]`), R2U2's pinned toolchain 1.85.1, path dependency on
  `external/r2u2/monitors/rust/r2u2_core`, built with
  `R2U2_MAX_QUEUE_SLOTS=65536` (compile-time const via `const_env`).
- Methodology: one C2PO-compiled spec per formula (C2PO defaults:
  rewrites + CSE); per trace, re-initialise the monitor (untimed: cost is
  proportional to the configured arena, not the formula), stream steps,
  stop at the first output (its verdict covers time 0). No end-of-trace
  flush → "undecided" when the trace ends first. C2PO rejects constant
  formulas, and R2U2 loops forever on constant TL operands (bug, see
  sources.md) → both "unsupported", excluded from timing. Undecided and
  unsupported are counted as disagreement and reported separately.

## D26 (2026-10-03) — R2U2 benchmarked only on our constant-free workloads
- R2U2 hangs on ~1056/1662 libmltl formulas (constant-operand bug); empirical
  hang detection needs two process launches per formula per length, too slow
  here (endpoint-security agent inspects every process). Owner chose to omit
  R2U2 from the libmltl workload (option 2). `run.py` skips it there; hang
  detection stays in place for the other workloads (none hang).

## D27 (2026-10-03) — `EVAL.md` → `EVAL_MLTL.md`; R2U2 trade-off section
- Owner: rename `src/mltl-core/src/EVAL.md` to `EVAL_MLTL.md` and add an
  analysis of bottom-up evaluation vs R2U2 (new §6; old §6/§7 → §7/§8).
  References updated (eval.rs doc comment, benchmarks README, agent-docs).
  D23 text above still says `EVAL.md`; that is the historical name.
- Owner's premise was "R2U2 is bounded memory, bottom-up is not". The doc
  qualifies it: for the single verdict at position 0, bottom-up tables are
  also bounded by the formula (h_ψ ≤ 1 + Σ ancestor upper bounds). Bottom-up
  is unbounded only when producing verdicts at every position of a stream,
  and it needs the trace prefix in memory and heap-allocates.
- R2U2 facts used (checked 2026-10-03 against `external/r2u2`):
  - SCQ size per node (`compiler/c2po/scq.py`): `max(0, max sibling wpd −
    bpd) + 1` (+ `--scq-constant`); bpd/wpd from `cpt.py`
    (`TemporalOperator`: bpd += lb, wpd += ub). Arena fixed at compile time
    (`R2U2_MAX_QUEUE_SLOTS`, `r2u2_core/src/internals/bounds.rs`).
  - Operators are incremental (`engines/mltl.rs` `until_operator`: state is
    `previous`/`edge`/`next_time`, no window); `scq_write` compacts equal
    consecutive verdicts.
  - C2PO `--debug` totals: `F[0,1000] a0` → 3 (rewritten to `true U`),
    `a0 U[0,1000] a1` → 4, `(G[0,1000] a0) & a1` → 1005 (a1 queue 1001),
    `G[0,8] G[0,8] a0 --no-rewrite` → 4 (with rewrites C2PO merges nested
    G's into one `R[0,·]`).

## D29 (2026-10-03) — Heavy benchmark workloads
- Owner: longer traces and more complex formulas, ~100 ms–1 s per evaluation.
- Added `large-length` (G[0, n−64−4k] over a 7-clause group, n up to 2^21) and
  `large-size` (k = 1..32 shifted clause groups at n = 2^18). Traces are built
  so every clause holds everywhere (recurrence periods with windows ≥ 2·period),
  forcing full work. R2U2 built with R2U2_MAX_QUEUE_SLOTS=2^20,
  R2U2_MAX_TL_INSTRUCTIONS=8192 (run.py forces an r2u2_core rebuild, since
  const_env values are not tracked by cargo). R2U2 hang trial uses a 256-step
  prefix (full 2M-step traces exceeded the 1.5 s trial timeout and were
  misclassified as hangs).

## D28 (2026-10-03) — T10.2 (bit-parallel batched evaluator) shelved
- Owner discussed van Herk / Gil–Werman sliding folds + bit-sliced batching
  and its relation to R2U2, then shelved it: "record all the details, I'll
  come back to it".
- All details are in `project/m10-batched-eval.md`: algorithm, operator mapping,
  padding/guards, alive masks, speed estimate (ASSUMED, unmeasured),
  caveats, streaming-vs-R2U2 analysis, related work, pending follow-ups.
- Open offer on resume: unverified prototype in `benchmarks/` first, to
  measure before proving. Not decided.
