//! MLTL syntax, semantics and properties, ported from AFP `Mission_Time_LTL`.
//!
//! Formulas are [`mltl::Mltl`] values. To get them from text, and to print
//! them, use the verified parser in `mltl-parse` (or the `mltl` front-door
//! crate, which also wraps the executable `convert_nnf` and `convert_bnf`
//! of [`properties`]):
//!
//! ```text
//! let mut atoms = mltl::Atoms::new();
//! let f = atoms.parse("!(p U[0,3] q)")?;
//! assert_eq!(atoms.print(&mltl::nnf(&f)), "!p R[0,3] !q");
//! ```
// A plain `cargo build` erases proof code, so proof-only imports, parameters
// and fields look unused. Verus runs (`cfg(verus_only)`) still report them.
#![cfg_attr(not(verus_only), allow(unused_imports, unused_variables, dead_code,
    while_true, non_shorthand_field_patterns))]
pub mod mltl;
pub mod properties;
pub mod parse_tree;
