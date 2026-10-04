# Work plan

Milestones and tasks. Owner's plain-language summary: `../../PLAN.md` (if
the order or scope here changes, add a `human-doc-backlog.md` entry for it).
Task IDs `T<milestone>.<n>`. Sizes: S ≈ a day, M days, L a week+, XL weeks.
Order and reasons: D12.

```
M1 toolchain ─> M2 mltl-core ─┬─> M4 progression (done) ─> M3 parser, M5 lang-partition (done) ─> M7 SAT
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

## M3 — Verified parser/printer (goal 6) — done 2026-10-03
Crate `src/mltl-parse`; details `modules/mltl-parse.md`. Verified: lexer,
grammar relations, parser sound + complete (hence unambiguous), printer
with round trip, numbering (injective, `pN` kept, truth-preserving), AFP
binding examples. Cargo-style error reports done (D42; iterate with the owner's use).
Open:
differential test against other parsers (the lark parser is no longer on
this machine).

## M4 — Formula progression (goal 5) — done 2026-10-03, ahead of M3 (D33)
Both theories ported and verified (`correspondence/formula-progression.md`,
`modules/formula-progression.md`). Left over:
- T4.6 done 2026-10-03 (`modules/formula-progression.md`, Performance).

## M5 — Language partitioning (goal 5) — done 2026-10-03, before the parser (D38)
Whole AFP entry ported and verified (`correspondence/language-partitioning.md`,
`modules/language-partitioning.md`); mltl_ext is the core parse tree (D39).
Left over:
- T5.6 (S) Port `MLTL_Language_Partition_Codegen` (string printing) on top
  of the verified printer of `mltl-parse`.
- Possible (owner's call): ownership passing in exec (D36) to cut copies;
  a benchmark (no Haskell comparison, D40).

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
Source: `REU/isabelle/` (D18). Approach D45, crates D46; details `m7-sat.md`,
`../correspondence/mltl-sat.md`. Done 2026-10-04: propositional layer + LRAT
checker, fast translation + soundness theorem, verified encoder and checked
`decide`, completeness (a CNF model decodes to a satisfying trace; CNF ⟺
MLTL equisatisfiable), verified `solve`, CaDiCaL glue, benchmark on the REU
formulas. Open:
- T7.11 (L, owner's call) slow translation, `fs_eq_slow`, encoding-length
  theorems; Isabelle's naive/Tseytin CNF.
- T7.12 (S) in-process CaDiCaL (crate) instead of a subprocess; deferred
  until WASM matters (owner, 2026-10-04).

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
- **T10.4 done (2026-10-03): bit-row trace representation**, verified
  (`mltl_eval_bottom_up_bits`, `BitTrace::from_sets`). ~4× faster verified on
  the heavy benchmark; prototype shows ~6× is reachable. Lessons in
  `modules/mltl-eval.md`.
- Possible next (owner's call): tune the verified table/next-array code
  (`vec![x; n]`, fewer pushes) to close the 1.8× gap to the prototype; a
  faster verified `from_sets`.