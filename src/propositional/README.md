# propositional

Propositional logic for the MLTL SAT solver, proved in Verus: formulas, CNF,
and checkers for the two answers a SAT solver can give.

No verified SAT solver is fast, so we let a fast unverified solver
(CaDiCaL) answer and check its answer here:

- **"satisfiable" plus a model:** [`check_model`](src/dimacs.rs#L115)
  confirms the model satisfies every clause.
- **"unsatisfiable" plus an LRAT proof:** [`check_lrat`](src/lrat.rs#L672)
  replays the proof. Each step adds a clause and names earlier clauses
  (hints) that, by unit propagation, show the new clause follows. A proof
  ends by adding the empty clause.

Both take the solver's output as plain input, so nothing about the solver,
or about how its output was read, is trusted. Tiny example: for
`(x∨y)(x∨¬y)(¬x∨y)(¬x∨¬y)`, the proof `5 1 0 1 2 0` adds `x`
(assume `¬x`: clause 1 forces `y`, clause 2 is then false), and
`6 0 5 3 4 0` adds the empty clause.

## The guarantees

- `check_lrat(cnf, steps)` returning `true` means
  `!dimacs_satisfiable(cnf_seqs(cnf))`: no valuation satisfies every
  clause ([`dimacs_satisfiable`](src/dimacs.rs#L38),
  [`dimacs_models`](src/dimacs.rs#L34), [`cnf_seqs`](src/dimacs.rs#L48)).
  The incremental form is [`LratChecker`](src/lrat.rs#L467).
- `check_model(cnf, m)` returning `true` means the valuation
  [`model_valuation`](src/dimacs.rs#L110)`(m)` satisfies `cnf`.
- Literals are DIMACS integers. [`dimacs_satisfiable_view`](src/dimacs.rs#L94)
  shows this is [`cnf_satisfiable`](src/cnf.rs#L46) over
  [`Literal`](src/cnf.rs#L15)s, the AFP's CNF semantics.

The formulas ([`Formula`](src/formula.rs#L11),
[`formula_semantics`](src/formula.rs#L68)) and CNF definitions follow AFP
[`Propositional_Proof_Systems`](https://www.isa-afp.org/entries/Propositional_Proof_Systems.html);
[`form_of_cnf_semantics`](src/cnf.rs#L94) links the two. The LRAT checker
has no Isabelle counterpart. It supports clause additions justified by unit
propagation and deletions, which is what CaDiCaL's proofs use; other step
kinds are rejected.

Check a proof from the command line:
`cadical --lrat --binary=false f.cnf f.lrat`, then
`cargo run --release -p propositional --example lrat_check f.cnf f.lrat`
([`examples/lrat_check.rs`](examples/lrat_check.rs)). Proofs:
[`scripts/verify.sh`](../../scripts/verify.sh); tests:
`cargo test -p propositional --release`.

Agent context: [agent-docs/project/m7-sat.md](../../agent-docs/project/m7-sat.md).
