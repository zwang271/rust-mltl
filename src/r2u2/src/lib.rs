//! An idealized R2U2 monitor, verified against MLTL semantics.
//!
//! Follows the in-progress Isabelle formalization (`ROOT/isabelle/R2U2_*.thy`).
//! Every shared connection queue (SCQ) is modelled by the full history of
//! verdicts written to it; what a real (unbounded) R2U2 queue holds is the
//! compaction of that history ([`verdict::compact`]).
//! Correspondence table: agent-docs/correspondence/r2u2.md.
pub mod verdict;
pub mod scq;
pub mod observer;
pub mod operators;
pub mod engine;
pub mod soundness;
pub mod until;
pub mod promptness;
