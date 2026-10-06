//! An idealized R2U2 monitor, verified against MLTL semantics.
//!
//! Follows the in-progress Isabelle development (`ROOT/isabelle/R2U2_*.thy`).
//! Stage 1 (D48): every shared connection queue (SCQ) is modelled by the
//! full history of verdicts written to it; what a real (unbounded) R2U2
//! queue holds is the compaction of that history ([`verdict::compact`]).
//! Bounded ring queues come later, as a refinement.
//! Correspondence table: agent-docs/correspondence/r2u2.md.
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
