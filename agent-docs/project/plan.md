# Work plan

Milestones and tasks. Owner's plain-language summary: `../../PLAN.md` (if
the order or scope here changes, add a `human-doc-backlog.md` entry for it).
Task IDs `T<milestone>.<n>`. Sizes: S ≈ a day, M days, L a week+, XL weeks.
Order and reasons: D12.

```
M1 toolchain ─> M2 mltl-core ─┬─> M3 parser ─> M4 progression ─> M5 lang-partition ─> M7 SAT
                               ├─(fork URLs)─> M6 WEST in place
                               └─(fork URLs)─> M8 R2U2 in place
M9 cross-cutting, alongside.   M10 fast evaluator: scalar part done, batching shelved.
```

## Done
- **M1 toolchain** (2026-10-02): Verus installed, `scripts/verify.sh`
  verifies the workspace; feasibility spike in `verification/spikes/`.
- **M2 mltl-core** (2026-10-03): `MLTL_Encoding`, all of `MLTL_Properties`,
  non-R2U2 `MLTL_Properties_Extended`; executable `convert_nnf`,
  `convert_bnf`, evaluators. Details: `correspondence/mission-time-ltl.md`,
  `modules/mltl-core.md`. Left over:
  - T2.5: inventory of lemmas the downstream theories need beyond
    `MLTL_Properties`. Do it per milestone, at its start.
  - T2.8: write down how generic atoms meet `usize` atoms (mostly settled
    by D19).

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

## M10 — Fast verified evaluator
- Done: verified scalar bottom-up evaluator (`mltl-eval`) and the benchmark
  suite (`src/mltl-eval/benchmarks/`, results in its README). Bottom-up is
  linear in trace length and formula size, and 2.6–9× faster than libmltl,
  R2U2 and top-down on heavy workloads. On random traces with wide windows,
  early-exit evaluators win on constants.
- Shelved: T10.2, the bit-parallel batch over many traces (D28; design in
  `m10-batched-eval.md`).
- **T10.4 (next): bit-row trace representation** in `src/mltl-eval` (D31,
  D32): atoms read from a bit row per atom, built once per trace with a
  proof that it denotes the same spec trace. Tables and interval logic
  unchanged. Order: profile → prototype → benchmark → iterate → prove;
  lessons in `modules/mltl-eval.md`.