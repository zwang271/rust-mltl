//! Propositional logic for the MLTL SAT solver: formulas, semantics and CNF
//! ported from AFP `Propositional_Proof_Systems`, plus a CNF over DIMACS
//! integers with a verified model check and a verified LRAT proof checker.
//! Agent context: agent-docs/project/m7-sat.md.
pub mod formula;
pub mod cnf;
pub mod dimacs;
pub mod lrat;
pub mod lrat_text;
