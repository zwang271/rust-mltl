# Detailed work plan (agent-facing)

Status: ACCEPTED by owner 2026-10-02 with changes D9–D12 (inline answers in
`PLAN.md`). Human summary: `../../PLAN.md`
(keep the two in sync — if you change milestones/order here, log a backlog item
in `../human-doc-backlog.md` for `PLAN.md`). Coarse phases: `roadmap.md`.

Conventions: task IDs `T<milestone>.<n>`; size S (≤1 day agent work), M (days),
L (week+), XL (multi-week, split further when started). "Exit" = the condition
that marks the milestone done. Every task ends with the INDEX.md maintenance
checklist.

## Ordering and dependencies

```
M1 toolchain ─> M2 mltl-core ─┬─> M3 parser ─> M4 progression ─> M5 lang-partition
                               ├─(Q10 fork)──> M6 WEST in place
                               ├─(after M5)───> M7 SAT
                               └─(Q10 fork)──> T8.1–T8.3 survey ─> M8 R2U2
M9 cross-cutting runs alongside from M2 on.
```

Order (D12): M1 → M2 → M3 parser → M4 → M5, with M6/M8 started once fork URLs
(Q10) exist; M7 after M5 (source: D18). Formula progression is the smallest algorithm
(2.3k Isabelle lines) and stress-tests the core before the big ones (LP proof
6.7k lines, WEST proofs 6k, R2U2).

## M0 — Owner decisions — DONE 2026-10-02
Resolved: D9 (Verus latest + reproduce pin; forks as submodules under
`vendor/`; WEST URL), D10 (parser syntax), D11 (R2U2 theorem), D12 (order).
Remaining: Q10 fork URLs (blocks M6/M8), Q11 identifier syntax (T3.1),
Q3 resolved (D18).

## M1 — Toolchain and skeleton — DONE 2026-10-02
- T1.1 DONE 2026-10-02 (`0.2026.09.27.3cf1832`). (S) Install the latest Verus release binary (bundles Z3) (D9); record exact
  version, install path, rustup toolchain in `../verification/verus-notes.md`.
- T1.2 DONE 2026-10-02 (`cargo verus verify --workspace` via `scripts/verify.sh`). (S) Decide `cargo verus` vs raw `verus` invocation; root `Cargo.toml`
  workspace with members under `src/`; a `scripts/verify.sh` that verifies all
  crates and exits non-zero on failure.
- T1.3 DONE 2026-10-02. (S) Trivial crate `src/mltl-core` with one verified lemma; verify
  passes. Create `src/mltl-core/README.md` (AGENTS.md §3.3).
- T1.4 DONE 2026-10-02 (results + gotchas in verus-notes; code in
  `verification/spikes/m1-semantics-spike.rs`). Generic exec atoms (`Vec<A>`,
  `A: Eq`) NOT tested — exec side specialised to `usize` atoms. (M) Feasibility spikes, each recorded in verus-notes (works / fails +
  error text):
  - recursive enum with `Box` children: spec fn with `decreases`, exec fn
    over it, `height`/`size` measures;
  - generic atom type `A` with `Set<A>` in spec and something executable
    (`Vec<A>` with `A: Eq`? bitset for `nat` atoms?);
  - spec fn over `Seq<Set<A>>` with nat arithmetic (truncating `b-1`);
  - `Vec<Vec<bool>>`/bitvector trace with `view()` to `Seq<Set<nat>>`.
- Exit: one command verifies the workspace; spike results documented.

## M2 — mltl-core (goal 1, 2)
Source: AFP `Mission_Time_LTL` (`MLTL_Encoding.thy`, `MLTL_Properties.thy`).
Create `../correspondence/mission-time-ltl.md` and `../modules/mltl-core.md`
at T2.1.
- T2.1 DONE 2026-10-02 (D15). (S) Design decision (record as D-entry): one `Formula<A>` enum used in
  both spec and exec, bounds `usize`/`u64` viewed as `nat`, vs. separate
  spec/exec types with `view`. Prefer one type unless T1.4 shows a problem.
  T1.4 evidence: one generic enum with `usize` bounds works in spec and exec;
  `view_f` maps `Formula<usize>` atoms to `Formula<nat>`. Traces: D16 (finite `Set`).
- T2.2 DONE 2026-10-02 (`mltl.rs`; also `atoms_mltl`). (S) Syntax: 10 constructors mirroring `'a mltl`; `implies_mltl`,
  `iff_mltl` as spec fns (Isabelle definitions, not constructors).
- T2.3 DONE 2026-10-02 (+ Until/Release sanity checks). (M) `semantics_mltl` spec over `Seq<Set<A>>`, case-for-case (incl.
  `Prop` needs nonempty trace, F/U need `len > a`, G/R vacuous when `len ≤ a`,
  R's `b-1`). Port the `value`/example lemmas from `MLTL_Encoding.thy` as
  proof tests.
- T2.4 DONE 2026-10-02 (`properties.rs`). (M) Spec fns: `intervals_welldef`, `semantic_equiv`, `depth_mltl`,
  `subformulas`, `convert_nnf`, `complen_mltl`, `make_empty_trace`.
- T2.5 PARTIAL 2026-10-02: usage counts per `MLTL_Properties` name in
  `correspondence/mission-time-ltl.md`; still to do: inventory of lemmas the
  downstream theories need that are NOT in `MLTL_Properties` (do per milestone).
  (M) Downstream lemma inventory: grep `WEST_Proofs`,
  `MLTL_Formula_Progression`, `MLTL_Language_Partition_Proof`, and local
  `ROOT/isabelle/*.thy` for uses of `MLTL_Properties` lemmas; list them in the
  correspondence page with a priority (used by N downstream theories).
- T2.6 DONE 2026-10-02: ported the *whole* theory, nothing skipped.
  T2.6b DONE 2026-10-02 (D17): REU `MLTL_Properties_Extended` minus R2U2 parts. (L) Port prioritized lemmas; must-haves: `convert_nnf` preserves
  semantics + well-definedness, `semantic_equiv` is an equivalence, complen
  facts. Lemmas never used downstream → SKIPPED unless cheap.
- T2.7 DONE 2026-10-03 (D20, D21): exec `convert_nnf`, `convert_bnf`
  (properties.rs), exec `mltl_eval` (eval.rs). (M) Exec: `convert_nnf` exec ensures `== spec`; `eval(trace, f) -> bool`
  proved equal to `semantics_mltl` (first real exec-vs-spec proof; also a test
  oracle for everything after). Overflow preconditions on bounds documented.
- T2.8 (S) Generic-vs-`nat` instantiation story written down (WEST/R2U2 use
  `nat` atoms).
- Exit: all `MLTL_Encoding` + listed `MLTL_Properties` items `VERIFIED` or
  `SKIPPED` with reason; zero unrecorded trust.

## M3 — Verified parser/printer (goal 6)
Syntax per D10 (AFP-style, arbitrary identifiers). Create `correspondence/parser.md`, `modules/mltl-parse.md`.
- T3.1 (S) Write the grammar (precedence, associativity, interval syntax,
  identifier rules → propose answer to Q11, whitespace) as a doc page; decide
  the atom type the parser produces (D10 consequences); compare with the lark grammar in
  `ROOT/experiments/run_r2u2_sml.py` and whatever WEST/C2PO accept.
- T3.2 (M) Spec: spec printer `print(f): Seq<char>` (fully or minimally
  parenthesised) + spec of the accepted language. Correctness statements:
  (a) `parse(print(f)) == Some(f)`; (b) `parse(s) == Some(f) ==> s` is in the
  language and denotes `f` (soundness); (c) completeness for the grammar.
- T3.3 (M) Exec lexer + recursive-descent parser over `&[u8]`/`&str`;
  termination via input length; error type.
- T3.4 (L) Proofs of (a)–(c). Fallback if (c) is costly: prove (a)+(b), record
  (c) as PLANNED.
- T3.5 (S) Exec printer proved equal to spec printer.
- T3.6 (S) Differential test vs the lark parser on a corpus (existing
  experiment formulas + random generation).
- Exit: parser/printer `VERIFIED` for (a),(b); goal 6 done for text syntax.
  R2U2 binary format is T8.9.

## M4 — Formula progression (goal 5)
Source: AFP `MLTL_Formula_Progression.thy` (2285 lines); also local
`ROOT/isabelle/Formula_Progression_Extended.thy` (1612, sorry-free).
- T4.1 (S) Correspondence page; list defs: `weight_operators`,
  `formula_progression_len1`, `formula_progression`; theorems:
  `formula_progression_decomposition`, `satisfiability_preservation`,
  `formula_progression_correctness(_alt)`.
- T4.2 (M) Spec fns, with the same termination measure as Isabelle's
  `function` proof (check its `termination` block).
- T4.3 (M) Exec impl, proved equal to spec; avoid exponential cloning
  (consider `Rc`/arena only if Verus supports it — record).
- T4.4 (L) Port the main theorems (and helper lemmas they need).
- T4.5 (S) Optional: port useful lemmas from `Formula_Progression_Extended`.
- T4.6 (S) Benchmark vs `ROOT/formula_progression_api` exported code.
- Exit: correctness theorem `VERIFIED` against `mltl-core` semantics.

## M5 — Language partitioning (goal 5)
Source: AFP `MLTL_Language_Partition_*` (Algorithm 241 lines, Proof 6671).
Large: split into sub-milestones.
- T5.1 (S) Decide where `mltl_ext` lives (own crate vs core); record decision.
- T5.2 (M) `mltl_ext`, `to_mltl`, `semantics_mltl_ext`, `convert_nnf_ext`;
  lemma that `semantics_mltl_ext` agrees with core semantics via `to_mltl`.
- T5.3 (M) Compositions: `partial_sum`, `interval_times`, `is_composition*`,
  list builders (`And_mltl_list`, …), `Mighty_Release_mltl_ext`,
  `Global_mltl_decomp`, `LP_mltl_aux`, `LP_mltl` — spec + exec.
- T5.4 (XL) `LP_mltl_language_union(_explicit)`. Read the Isabelle proof
  structure first and write a proof outline into `modules/lang-partition.md`.
- T5.5 (XL) `LP_mltl_language_disjoint(_k)`.
- T5.6 (S) Replace `MLTL_Language_Partition_Codegen` string printing with the
  M3 printer.
- Exit: union + disjointness `VERIFIED`.

## M6 — WEST in place (goal 4)
Upstream https://github.com/zwang271/WEST; blocked by Q10 (fork). Source: AFP `WEST_Algorithms.thy` (744),
`WEST_Proofs.thy` (6024), `Regex_Equivalence.thy` (1202).
- T6.1 (M) Add the fork as submodule `vendor/WEST` (D9); build it; survey its structure and map
  each Rust fn to its `WEST_Algorithms` counterpart (or note divergence) in
  `correspondence/west.md`. Note any input parser it has (goal 6 overlap).
- T6.2 (M) Spec layer: Verus spec fns mirroring `WEST_Algorithms` (`WEST_bit`,
  `match_timestep`, `match_regex`, `match`, `WEST_and*`, `WEST_simp*`,
  `shift`, `pad`, `WEST_global/future/until/release`, `WEST_reg_aux`,
  `WEST_reg`).
- T6.3 (L) Refinement proofs bottom-up: bitwise → state → trace → regex →
  simp → temporal ops → `WEST_reg`. Minimal, behavior-preserving source edits;
  log every edit.
- T6.4 (XL) Port the `WEST_Proofs` main correctness theorem (`WEST_reg`
  matches exactly the traces satisfying the formula) against core semantics.
- T6.5 (M, optional) `Regex_Equivalence`.
- Exit: real WEST code `VERIFIED` correct w.r.t. `semantics_mltl`.

## M7 — MLTL SAT solver
Source: `REU/isabelle/` (D18). T7.1 survey + correspondence page; then the same
spec → exec → main-theorem pattern as M4. Sized after survey.

## M8 — R2U2 in place (goal 3)
Blocked by Q10 (fork). Target theorem: D11. Sources: `ROOT/r2u2/monitors/rust/r2u2_core`,
`ROOT/isabelle/R2U2_*.thy`, `ROOT/isabelle/explain_r2u2.md`, `ROOT/*_BUG.md`.
- T8.1 (S) Add fork as submodule `vendor/r2u2` (D9). Reproduce upstream
  verification with its pinned toolchain and recipe (`r2u2/monitors/rust/docs/dev/verification.md`); record pass/fail.
- T8.2 (S) Audit existing specs. Known 2026-10-02: specs are per-operator
  local properties (`previous.time`/`next_time` bookkeeping, `not` flips
  truth) in `engines/mltl.rs` + `booleanizer.rs`; no link to MLTL semantics;
  27 `#[verifier::external*]` (floats, div/mod, `&mut` arena deref,
  `value_buffer` writes). Classify each external: removable / refactor needed /
  must stay trusted. Copy into `verification/trusted-base.md` upstream section.
- T8.3 (M) Read `explain_r2u2.md` + all `*_BUG.md`; write
  `correspondence/r2u2.md` mapping `R2U2_Verdicts`, `R2U2_SCQ`,
  `R2U2_Operators`, `R2U2_Function`, engine-step theories to Rust items.
- T8.4 (S) Scope decision: MLTL engine first; booleanizer (floats) stays
  trusted/out of scope initially.
- T8.5 (L) Discharge `&mut` arena externals by minimal refactor (or newer Verus
  support); SCQ invariants following `R2U2_SCQ.thy`.
- T8.6 (L) Operator correctness on real code following `R2U2_Operators.thy`
  (LOAD/NOT/AND/UNTIL, then release/since/trigger).
- T8.7 (XL) Engine step + whole-monitor theorem: output matches
  `semantics_mltl` (D11). Where documented bugs falsify it, record the
  counterexample and decide (with owner) between fix-in-fork or precondition.
- T8.8 (S) Bridge lemma from R2U2 verdict streams to `mltl-core` semantics.
- T8.9 (L) Spec the C2PO binary format; verify `internals/process_binary.rs`
  decoding (goal 6 for R2U2).
- T8.10 (M) Upstream PRs to R2U2 (owner-driven).
- Exit: MLTL engine of `r2u2_core` `VERIFIED` against the chosen theorem;
  remaining externals all in the ledger with justification.

## M9 — Cross-cutting (continuous)
- T9.1 Differential testing: random formula + trace generator; compare our
  exec code against Isabelle-exported SML/Haskell (`ROOT/experiments/`) — cheap
  confidence before proofs land, and catches spec-transcription errors.
- T9.2 CI (GitHub Actions or similar) running `scripts/verify.sh` + tests,
  once a remote exists (owner).
- T9.3 Trusted-base audit at each milestone exit.
- T9.4 Verification-time budget: record per-crate times; split slow proofs.
- T9.5 Benchmarks vs Isabelle-exported code for each algorithm.

## M10 — Fast verified evaluator (IN PROGRESS, owner interest)
T10.2 SHELVED 2026-10-03 by owner (D28). Full design, estimates, caveats and the
R2U2 comparison: `m10-batched-eval.md`. Read it before resuming.
Status 2026-10-03: T10.1 DONE (scalar `mltl_eval_bottom_up`, horizons +
next arrays, VERIFIED); T10.3 DONE for scalar evaluators (D24: `src/mltl-core/benchmarks`,
identical inputs to all three, growth-exponent plots; results in its README). Finding: on libmltl's random-trace workload the
verified top-down evaluator beats libmltl from length 128; scalar bottom-up
is linear but ~2–10× slower than top-down up to length 1024 (allocation +
hash lookups, no early exit). The win must come from T10.2 (batching).
Cheap scalar improvements to try: reuse table buffers, bitset trace view
instead of HashSet lookups, skip next-array builds for width-1 intervals.
Context: `goals.md` "Owner interest". Reference oracle = exec `mltl_eval`
(T2.7). Analysis 2026-10-02:
- Naive (`mltl_eval`) cost at one position: T(F/G[a,b]φ) = (b-a+1)·T(φ),
  T(φ U/R[a,b] ψ) = (b-a+1)·(T(φ)+T(ψ)), Boolean ops add. Worst case
  O(|φ|·W^d), W = max interval width, d = temporal nesting depth;
  independent of trace length (only positions < complen are read).
- DP alternative: per subformula ψ compute sat[ψ][i] for i in 0..m, m =
  min(len, complen φ), plus one "empty suffix" value sat[ψ][len] (MLTL
  evaluates children on the empty suffix when i+k ≥ len; all such positions
  share that value). Boolean ops = bitwise. F/G[a,b] = sliding-window OR/AND
  over [i+a, min(i+b, len)]. U[a,b]: the pair (P,Q) ↦ (acc ↦ Q ∨ (P ∧ acc))
  forms a monoid with (P1,Q1)·(P2,Q2) = (P1∧P2, Q1∨(P1∧Q2)), so U is also a
  sliding-window fold; R by duality. Sliding-window folds of any monoid are
  O(1) amortized per position (van Herk / Gil-Werman block prefix/suffix
  scans). Total O(|φ|·m), independent of interval widths.
- Batch across traces (the GA case): bit i of a word = trace i, so every
  operation above processes 64 (u64) or more (SIMD lanes) traces at once;
  per-trace lengths handled by "alive" masks + broadcast empty-suffix
  values. Fitness = popcount over positive/negative masks.
- Outside the verified kernel: hash-consing/memoizing sat-vectors of shared
  subformulas across a GA population.
- Proof plan: T10.1 scalar per-trace DP proved = spec `mltl_eval`/
  `semantics_mltl` (uses unrolling/shift lemmas in properties.rs);
  T10.2 bit-parallel batch proved = per-trace DP (Verus `by (bit_vector)`);
  T10.3 benchmarks + differential tests vs exec `mltl_eval`. Performance
  target: beat libmltl (owner's current engine, see sources.md) on its own
  `tests/perf_compare/benchmark.cc` workload; AFP semantics (D22). Write plain u64
  loops (let LLVM vectorize); SIMD intrinsics would not be verifiable.
