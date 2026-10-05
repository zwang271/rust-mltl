# Module: language_partitioning (`src/language_partitioning`)

Language partitioning: split a formula into formulas whose languages
partition its language (on traces of length ≥ `wpd`). Isabelle mapping:
`../correspondence/language-partitioning.md`. Decisions: D38–D40.

## Files
- `src/ext.rs`: `MltlExt<A>` (= core parse tree with `Seq<usize>` data,
  D39), spec constructors, `to_mltl`, semantics, `language_mltl_r`,
  `convert_nnf_ext_spec` + lemmas, `wpd_mltl` + lemmas.
- `src/composition.rs`: `sum_list`, `partial_sum`, `interval_times`,
  `is_composition*` and their lemmas; `interval_times_facts` bundles the
  block bounds.
- `src/algorithm.rs`: the list builders, `Global_mltl_decomp_spec`,
  `LP_*_piece`, `LP_mltl_aux_spec`, `LP_mltl_spec`, `Ands_mltl_ext`.
- `src/lists.rs`: membership lemmas (`pairs`, builders, `concat`),
  `sat_some`, `disjoint_on` and combinators (`disjoint_append`,
  `disjoint_concat`, `And_mltl_list_disjoint`).
- `src/blocks.rs`: `agrees_on`; lifting lemmas `*_list_sat`,
  `Global_mltl_decomp_sat`; block formulas `future/until/release_block`,
  `blocks_ok`, block semantics, `*_partition`, `*_blocks_exclusive`.
- `src/structure.rs`: well-definedness, `wpd` bound, non-emptiness,
  `LP_mltl_element`, `Ands_mltl_semantics`, `in_Global_mltl_decomp*`;
  `lp_{or,future,until,release}_list` (one `LP_mltl_aux` case each, used by
  the later proofs and exec).
- `src/union.rs`, `src/disjoint.rs`: the main theorems.
- `src/exec.rs`: `MltlExtExec`, `ext_view`, exec builders, `LP_mltl_aux`,
  `LP_mltl` (guarantees in `ensures`), `check_composition`, `check_lp_input`.
- `src/splits.rs` (2026-10-04, D47): building `LP_mltl` input from a plain
  `Mltl<usize>`: `with_width(f, w)` (blocks of width `w`, last shorter;
  `w = 1` ⇒ all-ones) and `with_compositions(f, comps)` (one composition per
  temporal operator in reading order, checked with `check_lp_input`). Both
  `ensures` `to_mltl(ext_view(r)) == f`, `intervals_welldef(f)`,
  `is_composition_MLTL`. `None` for `a > b` and for `[0, usize::MAX]`
  (length doesn't fit; `blocks`). No composition syntax in the grammar
  (owner, 2026-10-04: other tools must not accept it; revisit later).
- `tests/partition.rs`: Isabelle examples, input checks, random union and
  disjointness checks against `mltl-eval` (10,000 trace checks, ~0.05 s).
- Crate: 215 VERIFIED (2026-10-03). No trusted items.

## Proof structure (worth reusing)
- Statement shape: `sat_some(LP(φ, k), π) == π ⊨ φ` for `|π| ≥ wpd φ`, one
  induction on `k`, mutual with a child helper (`lp_child_agrees`) that
  applies it on every suffix `drop π t`, `t ∈ [a,b]` (`agrees_on`).
  Measures: main `decreases k, 0nat`, helper `decreases k, 1nat` (the
  helper calls the main lemma at the same `k`).
- Lifting: "D agrees with x on [lo,hi]" ⟹ "some formula of
  `Future_mltl_list D lo hi` holds ⟺ `F[lo,hi] x` holds" (same for G at a
  point, U, mighty release). No non-emptiness of `D` needed.
- Partition: `F[a,b] x ⟺ ∃ block i` and blocks pairwise exclusive (first
  witness via `exist_first`); same for U and R (R also has
  `G[a,b](¬x ∧ y)` as block −1). Note `R` uses `nat_sub(b,1)`, so
  `R[0,0]` allows the witness `j = 0`; the proofs case-split on
  `t ≤ nat_sub(e,1)`.
- Disjointness: one induction under `disjoint_ok φ k` (all-ones, or
  `k ≤ 1`). Within a block the child list either has one element (`k ≤ 1`
  ⟹ children computed at depth 0) or the block is one step (all ones).
  Across blocks: exclusivity. Elements of the child list imply the child
  (from the union theorem).

## Exec notes
- Copies subformulas (`clone_ext`) wherever the output repeats them;
  ownership passing (D36) not done. Output size is inherently exponential
  (`G` with |D| > 1 gives |D|^(b−a+1) formulas). Not benchmarked; the owner
  skipped the Haskell comparison (D40).
- Block bounds are computed without reaching `b + 1`
  (`end = start + (L[i] − 1)`), so `b = usize::MAX` is fine.
- `check_composition` uses `u128` for the remaining width.
