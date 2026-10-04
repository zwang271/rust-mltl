# M7 — MLTL SAT solver: survey and draft plan

Status: plan approved 2026-10-04 (D45, D46); core pipeline VERIFIED 2026-10-04. Owner says the theories will go to the AFP soon; until
then `REU/isabelle/` is the source (re-sync when the AFP version lands).

## What exists (session `Mission_Time_LTL_to_SAT`, `REU/isabelle/ROOT`, 0 sorry)
| Theory | Lines | Content |
|---|---|---|
| `MLTL_To_SAT` | 1571 | slow translation `mltl_to_sat φ i :: ('a×nat) formula` (unrolls U; F/G/R via U), `mltl_to_sat_root φ = mltl_to_sat (convert_bnf φ) 0`, `trace_to_val`, `val_to_trace`; `equisatisfiable_slow`: `intervals_welldef φ ⟹ MLTL_SAT_LEN φ (complen_mltl φ) ⟷ sat {mltl_to_sat_root φ}` |
| `Fast_MLTL_To_SAT` | 245 | fast (definitional) translation: atoms are `(subformula, time)`; `unroll_until`, `get_associated_clauses_at_node`, `fast_mltl_to_sat φ alb aub`, `fast_mltl_to_sat_root φ = Atom(bnf φ,0) # …` (list of `Atom(ψ,t) ↔ expansion`) |
| `Fast_MLTL_To_SAT_Soundness` | 1539 | direct proof `soundness_fast_mltl_to_sat_root_complen` (same shape as slow) |
| `Fast_MLTL_To_SAT_Equivalence` | 2465 | `fast_to_slow`, `fs_eq_slow`: expanding fast's clauses gives *syntactically* the slow output |
| `Fast_MLTL_To_SAT_Soundness_Alt` | 430 | fast soundness derived from slow + equivalence (AI-assisted) |
| `Fast_MLTL_To_SAT_Encoding_Length` | 2382 | `slow_complexity`, `fast_complexity`, worst-case families |
| `Tseytin_CNF_Lists` | 317 | PPS Tseytin with `Original`/`Auxiliary` atoms; `tseytin_cnf_lists_satisfiable_iff` |
| `Prop_CNF_Index`, `MLTL_CNF_Encoder` | 110+400 | atom → nat indexing; `mltl_dimacs` (Fast/Slow × Naive/Tseytin), `mltl_dimacs_correct`; exported to SML for Kissat/Z3 |
| `SAT_Solver_Locale_Executable`, `SAT_Model_Extraction`, `Prop_To_SAT_Solver` | 1059+117+527 | AFP `SATSolverVerification` functional CDCL made executable (`solve_executable_correct`), model extraction |
| `MLTL_SAT_Solver` | 659 | `mltl_sat_solver`; `mltl_sat_solver_correct`: `Some π ⟶ π ⊨ φ` and `None ⟷ ¬MLTL_SAT_LEN φ (complen φ)` |

Depends on AFP `Propositional_Proof_Systems` (`formula`, `Sema`, CNF, Tseytin)
and `SATSolverVerification` (needs a local AFP rename patch; irrelevant to us).
Already in mltl-core: `convert_bnf` (+ lemmas), `complen_mltl`, `MLTL_SAT`,
`MLTL_SAT_LEN`.

## Measured performance (REU `experiments/results/`, 100 formulas of Hariharan et al.)
- Verified SML end to end, fast+naive, 10 min timeout: 90/100 solved,
  median 74 s (encoding median 17 s, solver 46 s). Other three combinations:
  0–6 solved.
- Verified SML encoding → SMT-LIB → Z3 (unverified printing/parsing), fast:
  100/100, median 0.28 s, max 0.63 s. 62 of 100 are UNSAT.

## Verified SAT solvers (web survey 2026-10-03; sources checked unless "recalled")
- No Verus-verified SAT solver or LRAT checker found.
- CreuSAT (Creusot, Rust): SAT and UNSAT answers proven; no benchmarks
  published; README says build workflow broken. Recalled: far behind CaDiCaL.
- IsaSAT (Isabelle-LLVM): SAT Competition 2022/2024 last place, 165 solved
  vs ~290–306 for Kissat. Best verified CDCL, still ~55–60% of state of the art.
- Certificates: CaDiCaL emits LRAT natively since 1.7.0; Rust bindings
  `rustsat-cadical` (bundles up to 2.2.1, LRAT supported). Verified LRAT
  checkers: `lrat_isa` (Lammich, Isabelle-LLVM, pipe from CaDiCaL),
  `cake_lpr` (CakeML; within 5× of unverified lrat-check), GRAT; Rust:
  `ordeal-lrat` (Aeneas→Lean, very young). LRAT checking costs ~1–5× solving.
- DRAT vs LRAT: DRAT has no hints, so each step needs full unit propagation
  over the whole clause set (drat-trim: backward checking, core-first,
  watched literals; can take longer than solving). Every verified checker
  checks a hinted format instead (LRAT, GRAT, LPR) and leaves DRAT→hints to
  an untrusted tool. Plan: LRAT only (CaDiCaL emits it), no DRAT checker.
- External verified checkers (`lrat_isa`, `cake_lpr`) prove facts about a
  DIMACS *file*; using them needs our printer proved against *their* parser
  spec (cake_lpr proves `parse_dimacs (print_dimacs f)` ≈ `f`), a gap
  across two provers closed only by reading. An in-Verus checker avoids it.
- Reading: Heule, "Proofs of Unsatisfiability", Handbook of Satisfiability
  2nd ed. (2021) ch. 15, preprint
  https://www.cs.cmu.edu/~mheule/publications/p01c15-prf.pdf (§15.6 checking);
  LRAT paper https://arxiv.org/abs/1612.02353; cake_lpr
  https://cakeml.org/tacas21.pdf (Table 5: cake_lpr within 5× of C lrat-check).

## Plan (approved 2026-10-04)
Approach: untrusted fast solver (CaDiCaL) + verified checking of its answer.
- SAT: decode the model into a trace and check it with the verified
  evaluator (`mltl-eval`) plus length ≥ `complen`; this direction needs no
  translation proof at all.
- UNSAT: CaDiCaL LRAT checked by a new Verus LRAT checker against the
  in-memory CNF; checker accepts ⇒ CNF unsat ⇒ (translation theorem)
  `¬MLTL_SAT_LEN φ (complen φ)`. Proof text parsing needs no proof (a
  mis-parse can only cause rejection).
- The hand-off to CaDiCaL (FFI or DIMACS text) is untrusted by design: one
  `external_body` call with no `ensures` (record it in the ledger; trusted
  only for memory safety, or run CaDiCaL as a subprocess). Both answers are
  checked against our own in-memory CNF / formula, so a corrupted hand-off
  can only give `Unknown`. The checker must fix LRAT's input-clause
  numbering (1..n in the order we added them) itself; a mismatch with
  CaDiCaL's numbering costs completeness, not soundness.
- Result `Sat(π) | Unsat | Unknown` (Unknown if the certificate fails);
  unlike Isabelle's solver, no completeness guarantee.
- Propositional layer is shared by the translation (formulas) and the LRAT
  checker (CNF), mirroring AFP `Propositional_Proof_Systems`: `Formulas.thy`
  (`formula` = Atom/⊥/¬/∧/∨/→), `Sema.thy` (`formula_semantics`, `sat`),
  `CNF.thy` (`literal` Pos/Neg, clause = literal set), `CNF_Sema.thy`,
  `CNF_Formulas.thy` (`nnf`, `cnf_lists`, `form_of_cnf`). Proposed layout:
  a crate with no MLTL dependency (propositional logic + LRAT checker), and
  the MLTL translation crate on top. Exec CNF uses machine-integer
  variables; LRAT also needs partial assignments and unit propagation.
- Steps: T7.2 propositional layer (`formula`, semantics, CNF) S; T7.3 fast
  translation spec (Isabelle-shaped) + exec with subformula ids M; T7.4 port
  `Fast_MLTL_To_SAT_Soundness` L; T7.5 exec CNF (definitional, linear per
  unroll step) proved equisatisfiable with the spec M; T7.6 model → trace +
  evaluator check S; T7.7 CaDiCaL via `external/` submodule or crate S;
  T7.8 Verus LRAT checker L; T7.9 end-to-end fn + benchmark vs the REU SML/Z3
  numbers M. Optional: slow translation, `fs_eq_slow`, encoding-length
  theorems, Isabelle-faithful naive/Tseytin CNF.

## Progress
- 2026-10-04 `src/propositional` VERIFIED (44 items, 0 errors): `formula.rs`
  (PPS `Formulas`/`Sema`: `Formula`, `formula_semantics`, `big_and/or`,
  `biimp`, `sat`, `entailment`), `cnf.rs` (`Literal`, list-based
  `clause_semantics`/`cnf_semantics`, `form_of_cnf` + semantics lemma),
  `dimacs.rs` (i32 CNF, `check_model`, view to `Literal<nat>`), `lrat.rs`
  (checker). Checker design: db = `Vec<Option<Vec<i32>>>` by clause id
  (input clauses 1..n), partial assignment `Vec<i8>` + trail; invariant
  "every db clause is entailed by the input"; per step the ghost invariant
  `rup_inv` = "every model of F falsifying C extends the assignment".
  Tautologies are accepted without hints; negative (RAT) hints fail.
- Measured (CaDiCaL 3.0.1 from Homebrew, M-series laptop): random 3-SAT
  250 vars/1065 clauses: solve 1.27 s, solve + LRAT 1.41 s, our parse
  0.09 s + check 0.07 s (119k steps). PHP(9,8): 79k steps, 0.03 s check.
  All CaDiCaL proofs tried were RUP-only and accepted.
- 2026-10-04 `src/mltl-sat` VERIFIED (75 items): `fast.rs` (translation,
  `trace_agrees_assign`, `assign_agrees_trace`, root theorem), `table.rs`
  (hash-consing), `encode.rs` (CNF; invariants `enc_ok` = soundness,
  `enc_complete` = completeness), `solve.rs` (`decide`, `equisatisfiable`,
  verified `solve` with end-to-end `ensures`; trusted `run_solver`,
  `now_ns`). Details: `../correspondence/mltl-sat.md`.
- Benchmark: REU `experiments/formulas.txt` (100 formulas): 38 SAT / 62
  UNSAT, identical to the REU Z3 run (`results/six_experiments_30s/z3_fast.csv`);
  totals encode 0.13 s, CaDiCaL (with LRAT) 4.9 s, our checks 0.31 s;
  slowest formula 0.13 s; whole run 5.5 s wall. REU numbers: verified
  Isabelle SML solver median 74 s/formula (90/100 in 10 min); Isabelle
  encoding + Z3 median 0.28 s/formula.
- Verification time: propositional ~1.5 s, mltl-sat ~5 s.
- CaDiCaL stays a subprocess (owner, 2026-10-04) until WASM is on the table;
  in-process would add CaDiCaL's memory safety to the trusted base.
