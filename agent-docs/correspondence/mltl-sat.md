# Correspondence: MLTL → SAT (REU `Mission_Time_LTL_to_SAT`) ↔ `src/mltl-sat`, `src/propositional`

Source: `REU/isabelle/` at `14fdbbe` (unpublished; going to the AFP).
Status words per INDEX. All VERIFIED items: Verus 0.2026.09.27.3cf1832,
2026-10-04 (`propositional` 44, `mltl-sat` 75 verified, 0 errors).

## AFP `Propositional_Proof_Systems` → `src/propositional`
| Isabelle | Rust | Status / note |
|---|---|---|
| `formula` (Formulas) | `formula.rs: Formula` | VERIFIED |
| `Top`, `BigAnd`, `BigOr`, `biimp` (Tseytin) | `top`, `big_and`, `big_or`, `biimp` | VERIFIED |
| `formula_semantics`, `entailment`, `sat` (Sema) | same names; `sat` over finite `Set` | VERIFIED |
| `top_semantics`, `BigAnd/BigOr_semantics`, `biimp_simp`, `entail_sat` | `top_semantics`, `big_and/or_semantics`, `biimp_semantics`, `entail_sat` | VERIFIED |
| `literal`, `lit_semantics` (CNF, CNF_Sema) | `cnf.rs: Literal`, `lit_semantics` | VERIFIED |
| `clause_semantics`, `cnf_semantics` (sets) | same names over `Seq` | list form, as the REU encoder uses lists |
| `form_of_lit`, `disj_of_clause`, `form_of_cnf` | same | VERIFIED; `form_of_cnf_semantics` links to `cnf_semantics` |
| `nnf`, `cnf_lists`, Tseytin (`tseytin_cnf_lists`) | — | NOT PORTED (our CNF is our own, see below) |
| — | `dimacs.rs`, `lrat.rs` | no Isabelle source: DIMACS CNF, `check_model`, LRAT checker |

## `Fast_MLTL_To_SAT.thy` → `mltl-sat/src/fast.rs`
| Isabelle | Rust | Note |
|---|---|---|
| `('a mltl × nat)` atoms | `Var<A> = (Mltl<A>, nat)` | |
| `mltl_size` | `mltl_size` | termination measure; `via fast_mltl_to_sat_decreases` |
| `unroll_until` | `unroll_until` | `decreases ub - lb` |
| `get_associated_clauses_at_node` | same + helpers `has_associated_clauses`, `associated_clause` | the four Isabelle equations share one shape; the helper holds the per-node clause |
| `fast_mltl_to_sat`, `fast_mltl_to_sat_root` | same | `aub+b-1` is `nat_sub` |
| `get_associated_clauses_at_node_*_k` | `get_associated_clauses_at_node_shape`, `models_associated_clauses` | one exact-shape lemma replaces the four |

## `Fast_MLTL_To_SAT_Soundness.thy` → `fast.rs`
| Isabelle | Rust | Note |
|---|---|---|
| `unroll_until_semantics` + `_converse` | `unroll_until_semantics` (iff) | |
| `semantics_U` | `semantics_U` (`until_at` = rhs) | |
| `trace_agrees_assign` | same | VERIFIED |
| `assign_agrees_trace` | same, per time `k` | VERIFIED; quantifier over `k` moved to a parameter |
| `val_to_trace` | `val_to_trace(v, n, ap)` | **divergence (D16):** states keep only atoms in `ap` (callers pass `atoms_mltl φ`) since our states are finite |
| `soundness_fast_mltl_to_sat_root_helper` | — | not needed: the main theorem follows from the two directions |
| `soundness_fast_mltl_to_sat_root_complen` | same | VERIFIED; `sat (set L)` is `sat(L.to_set())` |
| size / non-circularity lemmas (`dft_atom_*`, `fast_mltl_to_sat_atom_bound`, `child_omits_parent_not`, `assign_agree_shared`) | — | not needed by our proofs |

## Not ported (yet)
`MLTL_To_SAT` (slow translation, `equisatisfiable_slow`),
`Fast_MLTL_To_SAT_Equivalence` (`fs_eq_slow`), `…_Soundness_Alt`,
`…_Encoding_Length` (complexity), `Tseytin_CNF_Lists`, `Prop_CNF_Index`,
`MLTL_CNF_Encoder` (`mltl_dimacs`), and the SAT-solver theories
(`SAT_Solver_Locale_Executable`, `Prop_To_SAT_Solver`,
`SAT_Model_Extraction`, `MLTL_SAT_Solver`) — replaced by CaDiCaL + checks
(D45). The end-to-end theorem shape differs: Isabelle's
`mltl_sat_solver_correct` has `None ⟷ ¬SAT`; ours has `Unsat ⟹ ¬SAT`,
`Sat π ⟹ π ⊨ φ`, plus `Unknown`.

## Executable encoding (`table.rs`, `encode.rs`, `solve.rs`): no Isabelle source
- `table.rs`: hash-consing table; `table_ok` = entries describe `sub[i]`,
  children earlier, `sub` injective. So exec variables match Isabelle atoms
  one to one. `complen_exec`, `check_welldef` (exec counterparts of core specs).
- `encode.rs`: variable `bvar(n,id,t) = 1 + id·n + t`; aux vars above
  `len·n` for Until unrolling steps (meaning in ghost `aux` map). Invariant
  `enc_ok`: every model of the spec clauses emitted so far (`spec`, always a
  prefix-ordered copy of `fast_mltl_to_sat`) extended by `ext_val`
  satisfies the CNF. `encode` ensures `inv`: `mltl_sat_len ⟹ CNF sat`.
  The CNF is NOT the Isabelle `mltl_dimacs` output (that is naive or PPS
  Tseytin CNF); ours is definitional per Until step (4 clauses/step).
- Converse VERIFIED 2026-10-04: `restrict(w, sub, n)` reads a CNF model back
  as a spec valuation; invariant `enc_complete` (every CNF model, read back,
  satisfies the spec clauses so far; Until via `step_ok` + `chain_values`,
  backwards induction). `Encoding::inv` records it; `model_decodes_w` +
  `assign_agrees_trace` give `decoded_w(w) ⊨ φ`; `decode` is proved equal to
  `decoded` (= `val_to_trace` over `table_props`). `decide` ensures a real
  model ⟹ `Sat`; `equisatisfiable`: CNF sat ⟺ `mltl_sat_len` (counterpart
  of `mltl_dimacs_correct`). Remaining gap vs `mltl_sat_solver_correct`
  (`None ⟷ ¬SAT`): the solver's own completeness (CaDiCaL unverified; our
  checker rejects RAT steps).
