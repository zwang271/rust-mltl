# M8 assessment: can R2U2 be verified in place? (2026-10-04)

Deep dive asked for by the owner before any M8 work. Facts first, then the
options. **Decided 2026-10-04: option C's first layer, in this repo (D48).**

## What upstream `r2u2_core` verifies (VERIFIED 2026-10-04)
- Every upstream branch (main, develop, rust-develop, div-zero, simulator,
  inspecta, c2po-develop; fetched 2026-10-04) has the same Verus content:
  27 `ensures`, 5 `requires`, 28 `#[verifier::external*]`, 1 spec fn,
  0 proof fns. Local submodule is at `f4ae1358` (clean).
- Reproduced on our Verus 0.2026.09.27.3cf1832 in a throwaway copy
  (`/tmp/r2u2_verify/r2u2_core`, vstd dep swapped to ours): **35 verified,
  0 errors** after two mechanical fixes: (1) postconditions on `&mut`
  params need `final(queue_ctrl)` (new mut-ref rules); (2) delete
  `ex_saturating_sub` (vstd now specifies `saturating_sub`). Original pinned
  recipe (vstd 2025-08-12) not tried.
- What the 35 cover: only the pure per-operator helpers in
  `engines/mltl.rs` (`until/release/since/trigger/not/and/or/equivalent_operator`,
  `min`, `max`). Their contracts are large case splits that restate the code
  (timestamp arithmetic, `previous`/`next_time`/`edge` bookkeeping, truth
  value per case). No spec mentions a trace, a formula, or MLTL semantics.
- Unverified: everything stateful. `mltl_update`, `check_operand_data`,
  `push_result`, `scq_read`, `scq_write` are `external`; `engines/mod.rs`
  (`r2u2_engine_step`, the fixed-point reloop), `lib.rs`, `monitor.rs`,
  `process_binary.rs`, `instructions/*` are outside `verus!` entirely.
  No termination, no array-bounds, no SCQ invariant.

## The encoding gap (what "doesn't match our crates")
| Layer | r2u2_core | Our crates | Bridge |
|---|---|---|---|
| Formula | C2PO instruction table: flat array, topological order, shared subterms (DAG), operands `ATOMIC`/`DIRECT`/`SUBFORMULA`, queue per node via `memory_reference` | `Mltl<A>` tree (AFP) | spec fn decoding a well-formed table to `Mltl` |
| Operators | LOAD, NOT, AND, OR, EQUIV, UNTIL, RELEASE, SINCE, TRIGGER (F, G, IMPLIES, XOR, ONCE, HIST are no-ops: C2PO rewrites them) | AFP ops, no past time | future fragment maps directly; past time needs a new AST + semantics (Isabelle also excludes it) |
| Output | per-node compressed stream of `(time: u32, truth)`; entry covers `(prev, time]` | `semantics_mltl (drop i π) φ` | `deaggregate` (Isabelle `R2U2_Verdicts.deaggregate`) |
| Machine | u32 time (overflow → `clock_reset`), fixed arrays (256 instrs, 2048 queue slots), queue sizes from C2PO | `nat` | bounds as preconditions |
| Atoms | `atomic_buffer[i]` (or booleanizer, floats) | `Prop(usize)` | direct; booleanizer stays trusted |

The gap is bridgeable with ordinary spec functions; it is not the real blocker.

## Real blockers
1. **The target theorem (D11) is false for the real monitor.**
   `ROOT/SHARED_NESTED_UNTIL_SOUNDNESS_BUG.md`: C2PO-sized one-slot SCQs let a
   child overwrite a verdict its parent still needs. Formula
   `a0 U[0,0] ((a1 U[1,1] a0) U[0,2] a1)`, trace `[{}, {a0}, {a1}]`: C, Rust
   and Isabelle emit True at time 1, semantics says False. Refuted
   sorry-free in `ROOT/isabelle/R2U2_Bugs.thy:87-148`. Unresolved upstream;
   needs a proven queue-capacity rule (C2PO `compute_scq_sizes`, Isabelle
   `queue_size_sibling_nodes`).
2. **No algorithm-level proof exists anywhere.** Isabelle top theorem
   `r2u2_soundness_alt_style` (`R2U2_Function.thy:1923`) ends in `oops`
   (and is false, above). ~68 sorries in `R2U2_Function`, ~83 in
   `MLTL_Update_and_R2U2_Engine_Step` (incl. engine termination, update
   preserves `valid_tree_at`). Proved: operator-local validity preservation
   (`LOAD/NOT/AND/UNTIL_preserves_valid_tree`), SCQ basics, `convert_r2u2_form_equiv`.
   Isabelle models only LOAD/NOT/AND/UNTIL over a parse tree (Or/F/G/R via
   BNF rewrite), not the instruction table, not RELEASE/SINCE/TRIGGER/EQUIV
   as native ops (Rust has native RELEASE, OR, EQUIV).
3. **`ROOT/C_RUST_DIRECT_TEMPORAL_BUG.md`** says a fix to `mltl.rs` is in
   "the working tree", but the submodule is clean at `f4ae1358` and
   `check_operand_data`'s DIRECT branch still lacks the `next_time` check.
   The patch seems lost (UNKNOWN where it went; ask the owner).

## Reusability verdict
- Upstream Rust specs: not reusable for the semantic theorem. They are
  local, code-restating contracts; the needed invariant (SCQ contents ↔
  deaggregated semantics of the child at those times) is absent. At best
  they survive as lemmas inside new proofs.
- Isabelle R2U2: reusable as **design** (invariants `valid_scq`,
  `valid_parent_child`, `valid_tree_at`, observer record, `deaggregate`),
  not as finished proofs.
- In-place Verus feasibility: plausible. New Verus mut-ref support may
  remove the `&mut` arena externals; loops need invariants and the reloop
  needs a termination measure (the DIRECT bug was a nontermination).

## Options (for the owner)
- A. In place now: specs + proofs directly on the fork. Theorem needs a
  queue-capacity precondition that C2PO currently violates.
- B. Rebuild: verified R2U2-style monitor in this repo over `Mltl`, own
  proven queue sizing; real `r2u2_core` only differential-tested. Drops goal 3.
- C. (recommended) Two layers: first a Verus spec-level model of the SCQ
  algorithm (port Isabelle invariants, finish the proofs, fix capacity),
  proved against `semantics_mltl`; then refine the fork's code to that
  model (abstraction from instruction table + arena to the model). Layer 1
  is needed by A anyway; it also gives B for free if layer 2 stalls.
