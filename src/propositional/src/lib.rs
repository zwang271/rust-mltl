//! Propositional logic for the MLTL SAT solver: formulas, semantics and CNF
//! ported from AFP `Propositional_Proof_Systems`, plus a CNF over DIMACS
//! integers with a verified model check and a verified LRAT proof checker.
//! Agent context: agent-docs/project/m7-sat.md.
// A plain `cargo build` erases proof code, so proof-only imports, parameters
// and fields look unused. Verus runs (`cfg(verus_only)`) still report them.
#![cfg_attr(not(verus_only), allow(unused_imports, unused_variables, dead_code,
    while_true, non_shorthand_field_patterns))]
pub mod formula;
pub mod cnf;
pub mod dimacs;
pub mod lrat;
pub mod lrat_text;
