//! Verified executable MLTL evaluation (AFP semantics, from mltl-core).
//! Algorithms: `../EVAL_MLTL.md`. Trace representations: `../README.md`.
pub mod trace;
pub mod top_down;
pub mod bottom_up;
/// Unverified prototype for comparing trace representations (T10.4).
pub mod proto;

pub use bottom_up::mltl_eval_bottom_up;
pub use top_down::mltl_eval;
pub use trace::Trace;
