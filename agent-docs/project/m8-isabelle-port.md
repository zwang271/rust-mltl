# Plan: port the R2U2 proofs (`src/r2u2`) to a fresh Isabelle theory

Owner asked 2026-10-04 for a plan ("later on"). Status: PLANNED, nothing
written in Isabelle yet. Target: a new session in `ROOT/isabelle/` (or a new
directory beside it), importing AFP `Mission_Time_LTL` and the parse tree
from `MLTL_Properties_Extended`, independent of the existing
`R2U2_*.thy` (which stay as they are).

## Why a fresh theory
The existing development mixes meaning, ring shape and sizes in one model,
lacks an exact ring↔history link, and states a false top theorem
(`../correspondence/r2u2.md`, `m8-r2u2-assessment.md`). The Verus proof is
layered; each layer only uses the previous layer's statements, so the
Isabelle port can follow it theory by theory.

## Theories (in order; Rust file → theory; rough size from the Verus side)
1. `R2U2_Streams` ← `verdict.rs` (~380 lines). `verdict = (val :: bool,
   time :: nat)`, `next_after`, `first_idx` (use `find_index` from
   `List-Index`, already in the session), `first_from`, `value_at`,
   `compact` (snoc recursion, or `foldl`), `deaggregate`. Key lemmas:
   `compact_value_at`, `compact_shape`, `deaggregate_correct`.
   Strictly increasing = `sorted_wrt (<) (map time L)`.
2. `R2U2_Hist_Queue` ← `scq.rs`. `scq = (all_values, next_time)`,
   `scq_read = first_from (compact all_values) next_time`;
   `scq_read_sound`, `scq_read_some`.
3. `R2U2_Ops` ← `operators.rs`, `observer.rs`. `LoopProgress`,
   `propagate_progress` (reuse Isabelle's), `load`, and `not_core`,
   `and_core`, `until_core` taking the *read results* (`verdict option`).
   Copy branch structure from `R2U2_Operators.thy` `NOT`/`AND`/`UNTIL`
   (they already match); `undecidedV` becomes `None`.
   Bridge lemma (optional, recommended): old operator = new core on the
   mapped values, so results relate back to the existing theories.
4. `R2U2_Engine` ← `engine.rs`. Parse tree with node data,
   `parse_tree_with_scq`, `mltl_update`, `repeat_mltl_update` **with fuel**
   (primrec on fuel; no termination proof needed), `engine_step`, `run`
   (primrec on the step count), `r2u2`, `wpd`.
5. `R2U2_Soundness` ← `soundness.rs`, `until.rs` (~1100 lines). `hist_sound`
   (via `value_at`), `hist_inv`, `tree_inv`, `until_inv` (the gap
   invariant: `P + a ≤ τ ≤ P + b`, ψ false and φ true on `[P+a, τ)`),
   operator step lemmas (one per UNTIL branch, witness `max (i+a) τ`),
   pass/step/run lemmas, `r2u2_sound` (= `r2u2_soundness_alt_style` for
   unbounded queues). Uses `convert_r2u2_form_equiv` (exists).
6. `R2U2_Promptness` ← `promptness.rs` (~500). `tree_measure`, progress ⇒
   write ⇒ measure drops (`scq_step_ok`), fuel suffices, `untils_ready`,
   `lemma_last_pass` ("last pass writes nothing"), `tree_prompt`,
   `r2u2_prompt`, `r2u2_correct`. Replaces `r2u2_promptness` (sorried;
   different, weaker statement, D49) and the engine termination sorries.
7. `R2U2_Queue_Size` ← `queue_size.rs` (~550). `backlog`,
   `backlog_bound` (distinct times), `nodes_ready`, `reads_fit`,
   `until_c`, `lemma_last_ready`, `r2u2_queue_sizes`.
8. `R2U2_Ring` ← `ring.rs`, `ring_engine.rs`, `ring_sim.rs` (~1500).
   Ring as a list + write pointer, `ring_write` (= Isabelle `scq_write`
   ring part), `ring_scan`/`ring_read` (= `scq_read_aux`, fuel instead of a
   measure), `ring_abs` (entry `i` of the compacted history in slot
   `i mod N`), `ring_write_abs`, `ring_read_abs`, pointer invariant
   (`ptr_room`, three cases), per-pass simulation, `r2u2_ring_eq`,
   `r2u2_ring_correct` with sizes `wpd(operands) + 1`.
9. (Optional) `R2U2_Code`: `export_code` the ring engine; differential test
   against `src/r2u2` exec (`monitor_trace`) and `r2u2_core`.

## Translation notes (Verus → Isabelle)
- Verus `Seq` + index quantifiers → lists with `!`; many index proofs become
  induction on lists (snoc induction for `compact`, `rev_induct`).
- `first_idx` uniqueness (`lemma_first_idx_unique`) is the workhorse in
  Verus; in Isabelle prove `find_index` characterization once.
- Modular arithmetic in `ring.rs` (`lemma_mod_succ`, `lemma_mod_distinct`)
  is easy with `mod` simp lemmas / `presburger`.
- Verus proofs needed explicit equality chains for tree updates
  (`ring_sim.rs`); in Isabelle `simp` with the update equations should do.
- Fuel: keep the fuel-bounded loop (total functions, no `function`
  package); the promptness theory proves fuel never runs out.
- `nat_sub` ↔ Isabelle `-` on `nat` (already truncating).
- Keep names of Verus lemmas so the correspondence table is mechanical.

## Effort and order
Layers 1–5 first (soundness: the result Isabelle lacks most), then 6
(promptness), 7–8 (bounded memory). Rough guess: 1–4 small, 5 medium (the
UNTIL branches are the work), 6–7 medium, 8 large (ring/pointer
bookkeeping). With an agent doing the drafting, Sledgehammer should close
most arithmetic; the invariants are already found, which was the hard part.

## Fidelity checks to keep
- Each new definition next to the old one it replaces, with a bridge
  lemma where practical (operators especially).
- Re-run the mutation checks of `../modules/r2u2.md` in Isabelle form
  (e.g. `value` counterexamples) for the UNTIL branches and queue sizes.
