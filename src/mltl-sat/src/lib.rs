//! MLTL satisfiability via SAT. Port of the fast (definitional) MLTL to
//! Boolean translation of the REU Isabelle session `Mission_Time_LTL_to_SAT`
//! (`Fast_MLTL_To_SAT.thy`, `Fast_MLTL_To_SAT_Soundness.thy`).
//! Agent context: agent-docs/project/m7-sat.md.
//!
//! # Example
//!
//! [`solve::solve`] translates a formula to SAT, runs CaDiCaL (`cadical` on
//! the `PATH`, or `$CADICAL`), and checks the answer with verified code, so
//! `Sat` and `Unsat` are always right. Formulas come from the verified
//! parser (via the `mltl` front-door crate):
//!
//! ```no_run
//! use mltl_sat::solve::{solve, Answer};
//!
//! let mut cx = mltl::Context::new();
//! let f = cx.parse_formula("F[0,3] (request & G[1,2] !grant)")?;
//! match solve(&f) {
//!     Some((Answer::Sat(t), _)) => {
//!         assert!(mltl::eval(&f, &t));
//!         println!("satisfied by {}", cx.display(&t));
//!     }
//!     Some((Answer::Unsat, _)) => println!("unsatisfiable"),
//!     _ => println!("no checked answer"),
//! }
//! let g = cx.parse_formula("G[0,4] grant & F[2,3] !grant")?;
//! assert!(matches!(solve(&g), Some((Answer::Unsat, _))));
//! # Ok::<(), mltl::Error>(())
//! ```
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
