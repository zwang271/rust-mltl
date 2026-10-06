//! Verified WEST: the satisfying traces of an MLTL formula as a list of
//! regular expressions. Ported from AFP `Mission_Time_LTL_to_Regular_Expression`
//! (`WEST_Algorithms.thy`, `WEST_Proofs.thy`).
//! Correspondence table: agent-docs/correspondence/west.md.
// Isabelle names (`WEST_reg`, `WEST_and_state`, …) are kept (D20).
// A plain `cargo build` erases proof code, so proof-only imports, parameters
// and fields look unused. Verus runs (`cfg(verus_only)`) still report them.
#![cfg_attr(not(verus_only), allow(unused_imports, unused_variables, dead_code,
    while_true, non_shorthand_field_patterns))]
#![allow(non_snake_case)]
pub mod algorithms;
pub mod matching;
pub mod simp;
pub mod temporal;
pub mod correct;
pub mod exec;
pub mod bits;
pub mod packed;
pub mod packed_ops;
pub mod fast;
pub mod fast_reg;
pub mod api;
