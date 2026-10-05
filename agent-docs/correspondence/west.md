# Correspondence: WEST ↔ `src/west`

Isabelle: `AFP/thys/Mission_Time_LTL_to_Regular_Expression/` —
`WEST_Algorithms.thy` (744 lines), `WEST_Proofs.thy` (6024),
`Regex_Equivalence.thy` (1202, not ported). Rust files relative to
`src/west/src/`. All rows VERIFIED: `scripts/verify.sh -p west`, Verus
0.2026.09.27.3cf1832, 2026-10-04 (crate: 143 items, nothing trusted), unless
marked otherwise.

Common divergences:
- Lists are `Seq`; recursive list functions recurse on `s[0]` /
  `s.drop_first()` like Isabelle's `h#t` equations, in Isabelle's equation
  order. `map f [0..<n]` is `Seq::new(n, f)`; `take`/`drop` are core's
  total versions.
- Atoms are `usize`, formulas `Mltl<usize>`, traces `Seq<Set<usize>>`
  (D19). `match_timestep` quantifies over `nat` positions as Isabelle does;
  a position past `usize::MAX` is never "in" a state (`atom_in`). So a
  `usize` trace is an Isabelle trace whose atoms are all ≤ `usize::MAX`.
- Exec follows D20 (`<name>_spec` + exec `<name>`), regexes
  `Vec<Vec<Vec<WestBit>>>` read by `exec.rs : rview`.
- Proofs are not line-by-line: AND and simp go through index
  characterizations, temporal operators are stated over `shifted π L i`
  (`temporal.rs`), so the formula induction only adds the hypothesis.

## WEST_Algorithms.thy

| Isabelle | Rust | Kind | Notes |
|---|---|---|---|
| `WEST_bit`, `state`, `trace`, `state_regex`, `trace_regex`, `WEST_regex` | `algorithms.rs : WestBit`, `WestTrace`, `StateRegex`, `TraceRegex`, `WestRegex` | type | `WestBit` derives `Clone, Copy, PartialEq, Eq, Debug` (exec compares by `match`, never `==`). |
| `WEST_get_bit`, `WEST_get_state` | same | spec | |
| `match_timestep` | same (+ `atom_in`) | spec | See divergences. |
| `trim_reversed_regex`, `trim_regex` | same | spec | Unused by the algorithm. |
| `match_regex` | same | spec | |
| `match` | `west_match` | spec | Renamed: `match` is a Rust keyword. |
| `regex_equiv` | same | spec | |
| `match_example`, the `regex_equiv` example | — | SKIPPED | Covered by runtime tests. |
| `WEST_and_bitwise`, `WEST_and_state`, `WEST_and_trace`, `WEST_and_helper`, `WEST_and` | `<name>_spec`; exec `exec.rs : <name>` | spec + exec | |
| `WEST_simp_bitwise`, `WEST_simp_state`, `WEST_simp_trace` | `<name>_spec`; exec same | spec + exec | Exec `WEST_simp_state` requires `len s1 ≤ len s2` (Isabelle's `s2 ! k` past the end is unspecified); `WEST_simp_trace` requires `num_vars`-wide states. |
| `count_nonS_trace`, `count_diff_state`, `count_diff` | same | spec | Exec only for equal lengths (inside `check_simp`). |
| `check_simp` | `check_simp_spec`; exec `check_simp` | spec + exec | Exec requires `num_vars`-wide states; early exit once the count passes 1. |
| `enumerate_pairs`, `enum_pairs`, `remove_element_at_index`, `update_L` | same; exec `update_L_exec` (in place: `Vec::remove` twice, push) | spec + exec | `[0..<n]` = `upt n`; `upt_from lo n` added for induction. |
| `length_enumerate_pairs`, `length_enum_pairs`, `enumerate_pairs_fact`, `enum_pairs_fact`, `enum_pairs_bound_snd`, `enum_pairs_bound` | `algorithms.rs : enumerate_pairs_facts`, `enum_pairs_facts` | proof | Merged. |
| `WEST_simp_termination1_bound`, `WEST_simp_termination1` | `algorithms.rs : WEST_simp_helper_decreases` (`via` fn) | proof | Measure `simp_measure` = Isabelle's `length L^3 + length idx - i`. |
| `WEST_simp_helper`, `WEST_simp` | `<name>_spec`; exec `WEST_simp` | spec + exec | Exec scans pairs `(a, b)` in `enum_pairs` order without building the list; `exec.rs : pair_off`, `enumerate_pairs_at` place pair `(a,b)` at index `pair_off 0 a n + (b-a-1)`. Restarts at `(0,1)` after a merge, as Isabelle. |
| `WEST_and_simp`, `WEST_or_simp` | `<name>_spec`; exec same | spec + exec | Exec `WEST_or_simp` takes ownership (D36) and appends. |
| `arbitrary_state`, `arbitrary_trace` | same; exec `arbitrary_state_exec` | spec + exec | |
| `shift`, `pad` | `shift_spec`, `pad_spec`; exec `shift`, `pad` | spec + exec | |
| `WEST_global`, `WEST_future`, `WEST_until`, `WEST_release_helper`, `WEST_release` | `<name>_spec`; exec same | spec + exec | Exec loops upward; until/release keep the running `WEST_global` (Isabelle recomputes it each level: same value, quadratic work). |
| `exhaustive` | — | SKIPPED | Needed only for Isabelle's `function` package. |
| `WEST_termination_measure`, `WEST_termination_measure_not` | `WEST_termination_measure` | spec | Written as `1 + 3·m φ` on every `Not φ`, which is what the 19 Isabelle equations amount to (`_not` lemma). |
| `WEST_reg_aux` | `WEST_reg_aux_spec`; exec `WEST_reg_aux` | spec + exec | Spec: all cases incl. the `Not` rewrites. Exec: NNF input only (`requires is_nnf`), which is all `WEST_reg` gives it. |
| `WEST_num_vars` | `WEST_num_vars_spec`; exec `WEST_num_vars` | spec + exec | Exec requires `WEST_num_vars_spec f ≤ usize::MAX`. |
| `WEST_reg` | `WEST_reg_spec`; exec `WEST_reg` | spec + exec | Exec `ensures` states `WEST_correct_v2` (D37). |
| `pad_WEST_reg`, `simp_pad_WEST_reg` | `<name>_spec`; exec `simp_pad_WEST_reg` | spec + exec | Exec requires `bound_sum f < usize::MAX` (so `complen` fits) and states `WEST_correct_pad`. |
| `value` examples | `tests/west.rs : afp_value_examples` | test | Outputs checked against Isabelle's Haskell export. |
| `export_code` | `differential/` | test | Exec output identical to the export on 1200 random formulas (2026-10-04). |

Not in Isabelle: `exec.rs : bound_sum`, `complen_le_bound_sum`,
`bound_sum_checked`, `complen` (exec `complen_mltl`).

## WEST_Proofs.thy

| Isabelle | Rust | Notes |
|---|---|---|
| `state_regex_of_vars`, `trace_regex_of_vars`, `WEST_regex_of_vars` | `matching.rs : trace_regex_of_vars`, `WEST_regex_of_vars` | State version inlined. |
| `WEST_and_state_correct*`, `WEST_and_trace_correct*`, `WEST_and_correct*` | `matching.rs : WEST_and_state_match`, `WEST_and_trace_match`, `WEST_and_helper_match`, `WEST_and_correct` | Via `WEST_and_state_index`, `WEST_and_trace_index`. Each also states `num_vars` is kept. |
| `WEST_or_correct` | `matching.rs : west_match_append` | |
| shift / pad lemmas | `matching.rs : shift_trace_match`, `shift_correct`, `pad_match` | |
| `WEST_simp_trace_correct*` | `simp.rs : WEST_simp_trace_correct` | Via `check_simp_unique_diff`: `check_simp` regexes differ in ≤ 1 entry. |
| `WEST_simp_helper_correct_forward/converse`, `simp_correct*`, `WEST_and_simp_correct`, `WEST_or_simp_correct` | `simp.rs`, same names (`update_L_correct` added) | |
| `WEST_global/future/until/release_correct*` | `temporal.rs`, same names (+ `WEST_release_helper_correct`) | Over `shifted π L i`. |
| `WEST_reg_aux_num_vars`, `WEST_reg_num_vars` | `correct.rs : WEST_reg_aux_of_vars`, `WEST_reg_of_vars` | |
| `WEST_num_vars_nnf`, `complen_convert_nnf`, `nnf_int_welldef` | `correct.rs : convert_nnf_num_vars_complen`, `convert_nnf_welldef` | |
| `WEST_reg_aux_correct` | same | NNF as `is_nnf` (core) instead of `∃ψ. F = convert_nnf ψ`. Operator cases in `future_case` … `release_case`. |
| `WEST_correct`, `WEST_correct_v2`, `WEST_correct_pad(_aux)` | same (+ `pad_WEST_reg_correct`, `pad_WEST_reg_of_vars`) | |
| everything else (~100 lemmas: list facts, `WEST_num_vars_subformulas`, case lemmas) | — | Replaced by the shorter route above. |

## Fast version (not in Isabelle)
`bits.rs`, `packed.rs`, `packed_ops.rs`, `fast.rs`, `fast_reg.rs`,
`api.rs`: no Isabelle counterpart. Each packed operation is proved to be a
spec operation of `WEST_Algorithms` on the views (`tr`, `pview`): word AND
= `WEST_and_trace`, cross product = `WEST_and`, OR = `WEST_simp_trace`,
diff test ⟹ `check_simp`, shift = `shift`, pad = `pad`; simplification
and the temporal operators are proved only up to matching (D43). The
top-level theorem (`fast_reg`) is `WEST_correct_pad`'s statement for the
fast output. Design: `../modules/west.md`.
