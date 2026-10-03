# Correspondence: AFP `Mission_Time_LTL` ↔ `src/mltl-core`

Isabelle source: `AFP/thys/Mission_Time_LTL/` (`MLTL_Encoding.thy`,
`MLTL_Properties.thy`). Rust: `src/mltl-core/src/mltl.rs` (this page's file
column is relative to `src/mltl-core/src/`). Status column per INDEX.md.
VERIFIED rows: `scripts/verify.sh`, Verus 0.2026.09.27.3cf1832, 2026-10-02.

## MLTL_Encoding.thy

| Isabelle (theory : name) | Rust (file : item) | Kind | Status | Divergence / bridging notes |
|---|---|---|---|---|
| `datatype 'a mltl` | `mltl.rs : Mltl<A>` | exec type | VERIFIED (compiles under Verus) | Constructors `True_mltl…Release_mltl` → `Mltl::True…Mltl::Release`, same order and argument order. Bounds `nat` → `usize` (D15): formulas with bounds > `usize::MAX` are not representable. Specs read bounds as `nat`. |
| `atoms_mltl` (datatype set fn) | `mltl.rs : atoms_mltl` | spec | VERIFIED (well-founded) | Returns finite `Set<A>` (formulas are finite, so no loss). |
| `Implies_mltl` | `mltl.rs : implies_mltl` | spec | VERIFIED | Definition, not a constructor, as in Isabelle. |
| `Iff_mltl` | `mltl.rs : iff_mltl` | spec | VERIFIED | |
| binding examples (`value` lines) | — | — | SKIPPED | About concrete-syntax precedence; belong to the parser (M3, T3.1). |
| `semantics_mltl` (`π ⊨_m φ`) | `mltl.rs : semantics_mltl` | spec | VERIFIED (well-founded) | **Divergence:** trace `'a set list` → `Seq<Set<A>>`, finite states only (D16; owner: infinite states are a shortcoming of the Isabelle encoding). `drop` → `mltl.rs : drop` (total, `[]` past end). Release's `b-1` → `nat_sub(b, 1)` (truncating, as Isabelle `nat` minus). Quantifier bounds written `a <= i && i <= b` exactly as Isabelle. No explicit triggers (Verus gotcha, see verus-notes). |
| example lemma 1 (`Not (F[0,2] Prop 0)`) | `mltl.rs : example_not_future` | proof | VERIFIED | Isabelle states `... = False`; Rust states `!semantics_mltl(...)`. |
| example lemma 2 (`F[0,2] (Not Prop 0)`) | `mltl.rs : example_future_not` | proof | VERIFIED | |
| example lemma 3 (`G[0,2] Prop 0`) | `mltl.rs : example_global` | proof | VERIFIED | |
| (List library) `drop`, `length (drop i xs)`, `drop_drop` | `mltl.rs : drop, lemma_drop_len, lemma_drop_drop, lemma_drop_past_end, lemma_drop_zero` | spec/proof | VERIFIED | Isabelle gets these from `List`; Verus `Seq::skip` is partial, hence our wrappers. `nat_sub` mirrors `nat` minus. |
| — | `mltl.rs : sanity_until, sanity_release_zero_bound` | proof | VERIFIED | Not in Isabelle. Exercise Until and Release incl. the `b = 0` truncation case. Negative test (flipping a claim) fails as expected, 2026-10-02. |

## MLTL_Properties.thy

Rust file: `properties.rs`. All rows VERIFIED 2026-10-02 (47 items in crate,
`scripts/verify.sh`, Verus 0.2026.09.27.3cf1832, ~2 s). Every Isabelle
definition and lemma in the theory is ported; none SKIPPED. Statements use
`Seq<Set<A>>` traces (D16); `semantic_equiv` therefore quantifies over
finite-state traces only.

"Uses" = occurrences downstream (grep 2026-10-02) in AFP WEST / FP / LP and
local `ROOT/isabelle` R2U2 theories — guides what later milestones rely on.

| Isabelle name | Rust item | Kind | Uses W/FP/LP/R2U2 | Divergence / notes |
|---|---|---|---|---|
| `intervals_welldef` | `intervals_welldef` | spec | 23/74/181/120 | |
| `semantic_equiv` (`≡_m`) | `semantic_equiv` | spec | 0/13/1/0 | `forall pi: Seq<Set<A>>`, trigger `semantics_mltl(pi, phi)`. |
| `depth_mltl` | `depth_mltl` | spec | 4/0/26/9 | Isabelle `max` → `max_nat`. |
| `subformulas` | `subformulas` | spec | 17/0/0/0 | Finite `Set<Mltl<A>>`. |
| `future_or_distribute` | same | proof | | |
| `global_and_distribute` | same | proof | | |
| `not_not_equiv` | same | proof | 0/2/0/0 | |
| `demorgan_and_or`, `demorgan_or_and` | same | proof | | |
| `future_as_until`, `globally_as_release` | same | proof | 0/0/0/1, 0/0/0/2 | `requires a <= b` (Isabelle `assumes`). |
| `until_or_distribute`, `until_and_distribute`, `release_or_distribute` | same | proof | | `until_and_distribute` takes the smaller of the two witnesses explicitly (Isabelle: smt). |
| `different_next_operators` | same | proof | | Witness: empty trace. |
| `globally_future_dual`, `future_globally_dual` | same | proof | | |
| `release_until_dual1` | same | proof | | Per-trace, no `a ≤ b`, as Isabelle. |
| `release_until_dual2` | same (+ helper `not_until_not_unfold`) | proof | | Uses new helper `lemma_first_failure` (first index where a predicate fails) instead of Isabelle's linorder/smt steps. |
| `release_until_dual`, `until_release_dual` | same | proof | 0/0/0/4, 0/0/0/1 | |
| `release_and_distribute` | same | proof | | Via the duals + `until_or_distribute`, as Isabelle. |
| `convert_nnf` | `convert_nnf_spec` (spec, D20); exec `convert_nnf` (+ helper `convert_nnf_not`) with `ensures r == convert_nnf_spec(*f)` | spec + exec | | Termination of spec: `decreases depth_mltl(f) via convert_nnf_spec_decreases`. Exec on `Mltl<usize>` (D19); `convert_nnf_not` computes `convert_nnf (Not g)` without cloning. |
| `convert_nnf_preserves_semantics` | same | proof | 1/0/6/0 | `requires intervals_welldef(f)`; per-trace. |
| `convert_nnf_form_Not_Implies_Prop` | `convert_nnf_form_not_implies_prop` | proof | 0/0/7/0 | snake_case name. |
| `convert_nnf_convert_nnf` | same | proof | 26/0/0/0 | |
| `nnf_subformulas` | same | proof | 4/0/0/0 | Returns the witness `init_G` (stronger than Isabelle's `∃`). |
| `complen_mltl` | `complen_mltl` | spec | 118/272/0/3 | `(complen φ) - 1` → `nat_sub`. |
| `complen_geq_one` | same | proof | 15/6/0/1 | |
| `make_empty_trace` | `make_empty_trace` | spec | 0/0/0/0 | States are `Set::empty()`. |
| `length_make_empty_trace` | same | proof | | |
| `semantics_of_not_a_lteq_b`, `..._b2` | same | proof | | |
| `MLTL_induct` | `mltl_induct` | proof | 0/0/0/0 | Induction rule → lemma over `p: spec_fn(Mltl<A>) -> bool`; each Isabelle case is a quantified `requires`. PProp phrased with `semantic_equiv`. |
| `nnf_induct` | `nnf_induct` | proof | 2/0/0/0 | Same encoding; NNF assumption as `f == convert_nnf(init_f)` with explicit `init_f`. |
| — | `max_nat`, `lemma_first_failure` | spec/proof | | Helpers, not in Isabelle. |

## MLTL_Properties_Extended.thy (unpublished, `REU/isabelle/`)

Source: `REU/isabelle/MLTL_Properties_Extended.thy` at commit `14fdbbe`
(2479 lines; `REU` defined in `project/sources.md`). Not the same file as
`ROOT/isabelle/MLTL_Properties_Extended.thy` (older, 583 lines). Ported into
`properties.rs` (owner request 2026-10-02, D17). All rows VERIFIED
2026-10-02 (crate 127 items, ~3 s). Isabelle imports formula progression,
but nothing ported here uses it.

**Omitted as R2U2-specific (D17)** — belong with the R2U2 formalization (M8):
- `datatype mltl_parse_tree` (doc: "for attaching execution state (SCQ,
  observer) during monitoring"), `mltl_parse_tree_to_mltl`, `get_aux_data`,
  `get_child_trees`, `update_aux_data`, `map_aux_data`,
  `mltl_parse_tree_preserves_size`, `mltl_parse_tree_{true,false,prop,not,and,or,global,future,until,release}_inv`.
- `is_r2u2_form`, `convert_r2u2_form`, `convert_r2u2_form_is_r2u2_form`,
  `convert_r2u2_form_equiv`, `convert_r2u2_form_welldef_intervals`.

| Isabelle name | Rust item | Kind | Divergence / notes |
|---|---|---|---|
| `globally_true`, `future_false`, `false_until`, `until_false`, `true_release`, `release_true` | same | proof | |
| `globally_false_is_not_false`, `future_true_is_not_true`, `until_true_is_not_true`, `release_false_is_not_false` | same | proof | Witness: empty trace. |
| `semantic_equiv_reflexive/symmetric/transitive` | same | proof | |
| `not_CE`, `and_CE_left/right`, `or_CE_left/right`, `globally_CE`, `future_CE`, `until_CE_left/right`, `release_CE_left/right` | `not_ce`, `and_ce_left`, … (snake_case) | proof | Helper `lemma_equiv_suffixes` (not in Isabelle) instantiates `≡_m` on suffixes. |
| `inductive is_bnf` + `inductive_simps` | `is_bnf` | spec | Inductive predicate → recursive spec fn following the `inductive_simps` equations (Verus has no inductive predicates). |
| `is_bnf.induct` (auto-generated) | `is_bnf_induct` | proof | Lemma over `p: spec_fn`, one `requires` per intro rule (with `is_bnf` premises, as the generated rule). |
| `convert_bnf` | `convert_bnf_spec` (spec, D20); exec `convert_bnf`, `ensures r == convert_bnf_spec(*f)` | spec + exec | |
| `convert_bnf_is_bnf`, `convert_bnf_welldef`, `convert_bnf_equiv`, `convert_bnf_complen`, `bnf_convert_bnf`, `convert_bnf_convert_bnf` | same | proof | |
| `{until,future,global,release}_base_mltl_semantics` | same | proof | |
| `{until,future,global,release}_unrolling_mltl_semantics` | same | proof | `a+1` → `(a + 1) as usize` (fits since `a < b`). Helper `lemma_complen_bound`. |
| `bounded_exists_shift`, `bounded_forall_shift`, `bounded_until_shift` | same | proof | `P`/`Q` → `spec_fn(nat) -> bool`. |
| `semantic_shift_F/U/G/R` | `semantic_shift_f/u/g/r` | proof | `b-k` → `(b - k) as usize`. |
| `semantic_unroll_F/U/G/R` | `semantic_unroll_f/u/g/r` | proof | |
| `mltl_eval_interval_width` | same | spec | `b - a` → `nat_sub`. |
| `function mltl_eval` / `mltl_eval_unchecked` | `mltl_eval_spec` / `mltl_eval_unchecked_spec` (D20); exec `mltl-eval : mltl_eval` | spec (+ exec) | Mutual recursion; termination measure (`depth_mltl`, width, 1/0) — Isabelle uses `size` instead of `depth_mltl`. `Suc a` → `(a + 1) as usize` (only reached when `a < b`). Prop case: `pi.len() != 0 && pi[0].contains(q)` (Isabelle: `case π of [] ⇒ False | s#ss ⇒ q ∈ s`). |
| `mltl_eval_{future,global,until,release}_base` / `_unrolling` | same | proof | |
| `mltl_eval_unchecked_{future,global,until}_interval`, `mltl_eval_unchecked_release_dual` | same | proof | By recursion on `b - a` (Isabelle: `inc_induct`). |
| `bounded_forall_unroll`, `bounded_until_unroll` | same | proof | Ported for completeness; the interval proofs don't call them. |
| `mltl_eval_correct` | same (+ case helpers `mltl_eval_correct_{future,global,until,release}`, spec `eval_agrees_on_suffixes`) | proof | Split per operator to stay under rlimit. |
| `MLTL_SAT`, `MLTL_SAT_LEN` | `mltl_sat`, `mltl_sat_len` | spec | ∃ over finite-state traces (D16). |
| `unsat_is_false` | same | proof | |
| `atomic_props` | same | spec | Equal to `mltl.rs : atoms_mltl` — proved by new lemma `atomic_props_eq_atoms_mltl`. |
| `atomics_agree` | same | spec | |
| `atomics_agree_semantics` | same (+ helper `lemma_atomics_agree_drop`) | proof | Isabelle proof ~650 lines; here structural recursion on `f` with per-suffix IH. |

## Executable evaluators — `mltl-eval` (not in Isabelle beyond `mltl_eval`)

VERIFIED 2026-10-03 (crate 169 items). See `src/mltl-eval/EVAL_MLTL.md`.

| Rust item | Kind | Specification | Notes |
|---|---|---|---|
| `trace_view`, type `Trace = [HashSet<usize>]` | spec / type | `Seq<HashSet<usize>> → Seq<Set<usize>>` | D19. |
| `mltl_eval` (+ `eval_at`, `eval_future/global/until/release`) | exec | `== semantics_mltl(trace_view(t@), *f)` and `== mltl_eval_spec(*f, trace_view(t@))` | Top-down; loops over `[a, min(b, rem)]` (positions past the end = empty suffix). Differs structurally from Isabelle's per-step recursion (D20). |
| `mltl_eval_bottom_up` (+ `sat_table`, `sat_future/global/until/release`, `build_next`) | exec | `== semantics_mltl(trace_view(t@), *f)`; requires `t.len() < usize::MAX` | Tables `sat_ok`, horizons `child_horizon`, next arrays `next_ok`; window lemmas `lemma_{future,global,until,release}_window`, `lemma_window`, `lemma_window_sem`. |

