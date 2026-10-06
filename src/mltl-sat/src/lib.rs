//! MLTL satisfiability via SAT. Port of the fast (definitional) MLTL to
//! Boolean translation of the REU Isabelle session `Mission_Time_LTL_to_SAT`
//! (`Fast_MLTL_To_SAT.thy`, `Fast_MLTL_To_SAT_Soundness.thy`).
//! Agent context: agent-docs/project/m7-sat.md.
// Isabelle names are kept (D20).
// A plain `cargo build` erases proof code, so proof-only imports, parameters
// and fields look unused. Verus runs (`cfg(verus_only)`) still report them.
#![cfg_attr(not(verus_only), allow(unused_imports, unused_variables, dead_code,
    while_true, non_shorthand_field_patterns))]
#![allow(non_snake_case)]
pub mod fast;
pub mod table;
pub mod encode;
pub mod solve;
pub mod cadical;
