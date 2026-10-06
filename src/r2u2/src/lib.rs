//! An idealized R2U2 monitor, verified against MLTL semantics.
//!
//! Follows the in-progress Isabelle development (`ROOT/isabelle/R2U2_*.thy`).
//! Stage 1 (D48): every shared connection queue (SCQ) is modelled by the
//! full history of verdicts written to it; what a real (unbounded) R2U2
//! queue holds is the compaction of that history ([`verdict::compact`]).
//! Bounded ring queues come later, as a refinement.
//! Correspondence table: agent-docs/correspondence/r2u2.md.
//!
//! # Example
//!
//! [`exec_engine::Monitor`] takes one state per step and keeps the verdicts
//! so far. A verdict `(v, t)` gives `v` for every step after the previous
//! verdict up to `t`. Formulas and traces come from the verified parser
//! (via the `mltl` front-door crate). This formula is false at step 1, which
//! `r2u2_core` gets wrong:
//!
//! ```
//! use r2u2::exec_engine::Monitor;
//!
//! let mut cx = mltl::Context::new();
//! let f = cx.parse_formula("p0 U[0,0] ((p1 U[1,1] p0) U[0,2] p1)")?;
//! let t = cx.parse_trace("[{}, {p0}, {p1}]")?;
//! let mut m = Monitor::new(&f).unwrap();
//! for state in &t {
//!     assert!(m.step(state));   // `false` only on arithmetic overflow
//! }
//! assert_eq!(mltl::value_at(m.verdicts(), 1), Some(false));
//! assert_eq!(mltl::value_at(m.verdicts(), 1), Some(mltl::eval(&f, &t[1..])));
//! # Ok::<(), mltl::Error>(())
//! ```
// A plain `cargo build` erases proof code, so proof-only imports, parameters
// and fields look unused. Verus runs (`cfg(verus_only)`) still report them.
#![cfg_attr(not(verus_only), allow(unused_imports, unused_variables, dead_code,
    while_true, non_shorthand_field_patterns))]
pub mod verdict;
pub mod scq;
pub mod observer;
pub mod operators;
pub mod engine;
pub mod soundness;
pub mod until;
pub mod promptness;
pub mod queue_size;
pub mod ring;
pub mod ring_engine;
pub mod ring_sim;
pub mod tight;
pub mod half;
pub mod exec;
pub mod exec_engine;
