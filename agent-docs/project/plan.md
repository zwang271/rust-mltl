# Work plan

Milestones and tasks. Owner's plain-language summary: `../../PLAN.md` (if
the order or scope here changes, add a `human-doc-backlog.md` entry for it).
Task IDs `T<milestone>.<n>`. Sizes: S ≈ a day, M days, L a week+, XL weeks.
Order and reasons: D12.

```
M1 toolchain ─> M2 mltl-core ─┬─> M4 progression (done) ─> M3 parser, M5 lang-partition (done) ─> M7 SAT
                               ├─> M6 WEST port (D43)
                               └─> M8 R2U2 (idealized first, D48)
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

## M6 — WEST port (goal 4, D43) — done 2026-10-04
Crate `src/west`; details `modules/west.md`, `correspondence/west.md`.
Done: spec of `WEST_Algorithms`, `WEST_correct(_v2/_pad)`, faithful exec
(= spec; differential test vs the Isabelle export), fast packed exec proved
equivalent (`fast_reg`, `fast_reg_checked`, text output), benchmarks vs
upstream Rust/C++. Left over:
- T6.5 (optional) `Regex_Equivalence.thy`.
- T6.6 Website/CLI entry for mltl.temporallogic.org (D44), when asked.
- Possible: faster simplification (hashing), subsumption.

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

## M8 — R2U2 (goal 3, D48)
Facts and options: `m8-r2u2-assessment.md`. Sources: `ROOT/isabelle/R2U2_*.thy`,
`ROOT/isabelle/explain_r2u2.md`, `ROOT/*_BUG.md`, `ROOT/r2u2/monitors/rust/r2u2_core`.

### Stage 1 — idealized algorithm, in this repo (current)
Theorem: every verdict the idealized monitor emits for position i equals
`semantics_mltl (drop i π) φ` (and, separately, it eventually emits every
position the trace length decides). Divergence from C2PO is allowed;
record each one with the path back (D48).
Progress 2026-10-04: T8.1 done (`../correspondence/r2u2.md`), T8.2 done
(`../modules/r2u2.md` Design; owner agreed: full histories first), T8.3 done,
T8.4 done: LOAD/NOT/AND (with completeness), UNTIL (soundness); T8.5 soundness part done (`r2u2_sound`). T8.6 done (promptness within `wpd`, D49). T8.8 done 2026-10-04 (ring layer `r2u2_ring_eq`; sizes first uniform `wpd(operands)+1`, then tightened per child to `max(wpd(operands) − bpd(c), 0)+1` with NOT child and root 1, D50). T8.7 done 2026-10-04 (tree layout). Next: Isabelle port (`m8-isabelle-port.md`), flat layout.
- T8.1 (M) Inventory + `correspondence/r2u2.md`: Isabelle definitions
  (`SCQ`, `observer`, `verdict`, `deaggregate`, operators, `mltl_update`,
  `r2u2_engine_step`, invariants `valid_scq`/`valid_parent_child`/`valid_tree_at`),
  what is proved vs sorry, which proofs are worth following.
- T8.2 (S) Design note: formula representation (tree vs instruction list
  over `Mltl`), operator set (Isabelle's LOAD/NOT/AND/UNTIL via BNF vs
  native OR/RELEASE as in Rust), queue model (unbounded ghost history
  first, bounded ring later), time as `nat` in spec. Owner reviews.
- T8.3 (M) Spec layer: compressed verdict streams + `deaggregate` and its
  lemmas; the per-node correctness invariant (queue contents = semantics
  of the child at those times).
- T8.4 (L) Operators one by one preserve the invariant (LOAD, NOT, AND,
  UNTIL, then the rest).
- T8.5 (L) Engine step: reloop terminates, invariant holds after each time
  step; whole-monitor soundness.
- T8.6 (M) Completeness/promptness (verdicts appear once decidable).
- T8.7 (M) Executable version (machine ints, arrays) proved equal to the
  spec; differential test vs `r2u2_core` and the Isabelle SML export,
  with the known bugs as expected differences.
- T8.8 (M) Bounded memory: a queue-capacity rule proved sufficient (fixes
  the shared nested-until bug), then a ring buffer refinement.

### Stage 2 — later
- Fork (Q10) as submodule; refine `r2u2_core` to the stage-1 model
  (instruction-table decoding, `&mut` arena, u32 time). Upstream specs
  reproduce on current Verus (35 verified) but are not built on.
- Binary spec decoder (`internals/process_binary.rs`, goal 6).
- Port closed proofs to Isabelle (owner's group).
- Afterwards, possibly C2PO (`../ideas.md`).

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