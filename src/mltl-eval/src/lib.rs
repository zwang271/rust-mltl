//! Verified executable MLTL evaluation (AFP semantics, from mltl-core).
//! Algorithms: `../EVAL_MLTL.md`. Trace representations: `../README.md`.
pub mod trace;
pub mod atom_read;
pub mod bit_trace;
pub mod top_down;
pub mod bottom_up;

pub use bottom_up::{mltl_eval_bottom_up, mltl_eval_bottom_up_bits};
pub use bit_trace::BitTrace;
pub use top_down::mltl_eval;
pub use trace::Trace;
