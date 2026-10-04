# Correspondence: formula progression ↔ `src/formula_progression`

Isabelle sources: `AFP/thys/Mission_Time_LTL_Formula_Progression/MLTL_Formula_Progression.thy`
(2285 lines) and the unpublished `ROOT/isabelle/Formula_Progression_Extended.thy`
(1612 lines, simplifier + `prog`). Rust files are relative to
`src/formula_progression/src/`. All rows VERIFIED: `scripts/verify.sh`,
Verus 0.2026.09.27.3cf1832, 2026-10-03 (crate: 91 items). Every Isabelle
definition and lemma of both theories is ported; nothing SKIPPED except
`value` lines, which are runtime tests in `tests/progression.rs`.

Common divergences: traces `Seq<Set<A>>` with finite states (D16); Isabelle
`take`/`drop` → total `take`/`drop` from `mltl-core/mltl.rs`; `π ≠ []` →
`pi.len() != 0`; `π @ ζ` → `pi + zeta`; `tr ! 0` → `tr[0]`. Spec/exec pairs
follow D20 (`<name>_spec` + exec `<name>`); exec code takes `Mltl<usize>`
and `mltl-eval`'s `Trace` (D19, D34).

## MLTL_Formula_Progression.thy (AFP)

| Isabelle | Rust | Kind | Notes |
|---|---|---|---|
| `weight_operators` | `algorithm.rs : weight_operators` | spec | Same weights. |
| `formula_progression_len1` | `algorithm.rs : formula_progression_len1_spec`; exec `formula_progression_len1` (borrows, copies operands) and `formula_progression_len1_owned` (moves them) | spec + exec | Spec: `decreases weight_operators(f) via …_decreases`, as Isabelle's `termination`. Exec computes the Release/Global cases from the operands directly (structural recursion); proof unfolds the spec on the rewritten formula. `a-1`, `b-1` are guarded, so `usize` subtraction is exact. Clones operands that reappear in the output (`clone_mltl`). |
| `formula_progression` | `algorithm.rs : formula_progression_spec`; exec `formula_progression` | spec + exec | Spec recursive on `drop 1`, incl. the redundant `length = 1` case. Exec is a loop (fold form); its `ensures` also states Theorems 2 and 3 for the result (D37). |
| `formula_progression_alt` (lemma, fold) | `algorithm.rs : formula_progression_alt` | proof | `fold` → vstd `fold_left` with `fp_step()`. |
| — | `formula_progression_snoc`, `formula_progression_append_traces` | proof | Helpers: progression over `π @ [s]` / `xs @ ys`. All of Theorem 1 follows. |
| `semantics_global`, `semantics_future` | same | proof | |
| `formula_progression_well_definedness_preserved(_len1)` | same | proof | |
| `formula_progression_identity` | same | proof | `[π ! k]` → `seq![tr[k]]`. |
| `formula_progression_decomposition` (Theorem 1) | same | proof | Via `formula_progression_append_traces`. |
| `satisfiability_preservation_len1` | same (+ `…_future`, `…_until`, `future_step0`, `until_step0`) | proof | Isabelle: ~700 lines by induction on φ. Here: measure `weight_operators`; Global/Release apply the hypothesis to the rewritten formula, then `globally_future_dual` / `release_until_dual`. Step lemmas need only `length π > 1` (core's unrolling lemmas need complen). |
| `satisfiability_preservation` (Theorem 2) | same | proof | Induction on k with `formula_progression_snoc`. |
| `theorem2_cexa`, `theorem2_cexb` | same | proof | Concrete `nat` atoms. |
| `complen_geq_1` | same (calls core `complen_geq_one`) | proof | |
| `complen_bounded_by_1` | same | proof | Derived from the stronger helper `complen_one_len1_value(_at)`: with complen 1, one step gives a formula whose value on *every* trace is `[s] ⊨ φ`. |
| `complen_temporal_props` | same | proof | Four implications as four `ensures`. |
| `complen_one_implies_one(_base)`, `formula_progression_decreases_complen(_base)` | same | proof | Derived from helpers `complen_len1_bound` (`complen(len1 φ s) ≤ max(1, complen φ − 1)`) and `complen_progression_bound` (`… ≤ max(1, complen φ − |π|)`). |
| `formula_progression_correctness_len1_helper(_alt)`, `…_len1(_alt)` | same | proof | |
| `formula_progression_correctness` (Theorem 3), `…_alt` | same | proof | Both from helper `formula_progression_value`: over a long-enough trace the result has value `π ⊨ φ` on every trace; plus `constant_equiv`. Much shorter than Isabelle's proof. |
| `formula_progression_true_or_false`, `formula_progression_append(_converse)`, `complen_property` | same (+ helper `formula_progression_extend`) | proof | `complen_property` also has an independent, progression-free proof in mltl-core: `complen_property_via_atomics`. Isabelle's `atomics_agree_semantics` (REU `MLTL_Properties_Extended.thy`) imports the FP entry but uses none of its lemmas (checked 2026-10-03). |
| examples (`value`), `export_code` | `tests/progression.rs : afp_examples` | runtime test | |

## Formula_Progression_Extended.thy (unpublished)

| Isabelle | Rust | Kind | Notes |
|---|---|---|---|
| `size` (datatype) | `mltl-core/src/mltl.rs : size_mltl` (moved from `simp.rs`, D39) | spec | One per constructor node incl. leaves; bounds not counted. Checked in Isabelle2025-2 on a same-shape datatype (`size (U T 3 4 (P 0)) = 3`, `size (F 3 4 (P 0)) = 2`). |
| `simp_mltl_aux` | `simp.rs : simp_mltl_aux_spec`; exec `simp_mltl_aux` (takes ownership) | spec + exec | Clauses in Isabelle's first-match order. Formula equality `φ = ψ` → exec `eq_mltl` (mltl-core). |
| `simp_mltl_aux_welldef`, `simp_mltl_aux_correct` | same (+ `…_correct_{not,or,and,until,release}`) | proof | Via the core `*_ce` congruence lemmas and dualities. |
| `simp_size_nondec`, `simp_size`, `simp_mltl_nosimp` | same, all from helper `simp_mltl_aux_size` | proof | |
| `simp_mltl` | `simp.rs : simp_mltl_spec`; exec `simp_mltl` | spec + exec | Spec `decreases size_mltl(f)` (Isabelle: `measure size`). Exec is a loop, measure `size + changed`. |
| `simp_mltl_correct`, `simp_mltl_welldef` | same | proof | |
| `simp_duals` | `simp.rs : simp_duals_spec`; exec `simp_duals` (takes ownership; helper `is_dual_shape`/`dual_shape` decides first, so unmatched input is returned without copying) | spec + exec | Clause order as Isabelle; catch-all returns the input. |
| `simp_duals_correct` | same | proof | |
| `formula_progression_CE_nonempty`, `fp_len1_nonempty_equiv`, `fp_nonempty_taut`, `fp_nonempty_contradict` | `extended.rs : same` | proof | All from helper `formula_progression_semantics`: for `ρ ≠ []`, `ρ ⊨ fp φ π ⟺ π @ ρ ⊨ φ`. |
| `fun formula_progression_alt` | `extended.rs : formula_progression_alt_spec`; exec `formula_progression_alt` | spec + exec | **Name clash:** same name as AFP's *lemma* `formula_progression_alt` (Isabelle keeps constants and facts apart). Rust: exec in `extended`, lemma in `algorithm`; `extended.rs`'s own item shadows the glob import. Exec loop returns early on True/False. |
| `fp_alt_welldef`, `formula_progression_alt_equiv_nonempty` | same (+ helpers `formula_progression_constant`, `formula_progression_cons`) | proof | |
| `prog` | `extended.rs : prog_spec`; exec `prog` (borrows) and `prog_owned` | spec + exec | Exec `ensures` also states the guarantee (continuation agreement + final True/False verdict, via `prog_semantics`), D37. Likewise `formula_progression_alt` / `formula_progression_alt_owned`. |
| `prog_early_eval` | same (+ helper `prog_semantics`) | proof | Four conjuncts as four `ensures`. Proof is semantic only (no need for "simp_duals never returns a constant"). |
| examples (`value`), `export_code` | `tests/progression.rs : extended_examples` | runtime test | |
