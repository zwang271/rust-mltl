//! Verified executable MLTL evaluation (AFP semantics, from mltl-core).
//! Algorithms: `../EVAL_MLTL.md`. Trace representations: `../README.md`.
//!
//! # Example: from text
//!
//! Parse the formula and the trace with one atom table (verified parser,
//! via the `mltl` front-door crate), then evaluate:
//!
//! ```
//! use mltl_eval::{mltl_eval, mltl_eval_bottom_up};
//!
//! let mut atoms = mltl::Atoms::new();
//! let f = atoms.parse("G[0,2] (request -> F[0,1] grant)")?;
//! let trace = atoms.trace([vec!["request"], vec!["grant"], vec!["request"], vec![]])?;
//!
//! assert!(!mltl_eval(&f, &trace));   // the request at step 2 is never granted
//! assert!(mltl_eval_bottom_up(&f, &trace[..2]));
//! # Ok::<(), mltl::Error>(())
//! ```
//!
//! # Example: numbered atoms
//!
//! Atoms are numbers (`p` = 0, `q` = 1). A trace is one set of true atoms per
//! step. Check `G[0,2] (p U[0,1] q)` on a 4-step trace:
//!
//! ```
//! use std::collections::HashSet;
//! use mltl_core::mltl::Mltl;
//! use mltl_eval::{mltl_eval, mltl_eval_bottom_up, mltl_eval_bottom_up_bits, BitTrace};
//!
//! let (p, q) = (0, 1);
//! // G[0,2] (p U[0,1] q)
//! let f = Mltl::Global(0, 2, Box::new(Mltl::Until(
//!     Box::new(Mltl::Prop(p)), 0, 1, Box::new(Mltl::Prop(q)))));
//!
//! // steps:          {p}      {q}      {p}      {q}
//! let trace: Vec<HashSet<usize>> =
//!     vec![[p].into(), [q].into(), [p].into(), [q].into()];
//!
//! // All evaluators are proved to agree with the MLTL semantics.
//! assert!(mltl_eval(&f, &trace));            // top-down
//! assert!(mltl_eval_bottom_up(&f, &trace));  // bottom-up
//!
//! // For many formulas on the same trace, convert it once to bit rows.
//! let bits = BitTrace::from_sets(&trace, 2);  // atoms are below 2
//! assert!(mltl_eval_bottom_up_bits(&f, &bits));
//! ```
//!
//! Steps past the end of a trace count as the empty trace, as in the AFP
//! semantics. So `F[0,2] ¬p` holds on the one-step trace `[{p}]`:
//!
//! ```
//! # use std::collections::HashSet;
//! # use mltl_core::mltl::Mltl;
//! # use mltl_eval::mltl_eval;
//! let f = Mltl::Future(0, 2, Box::new(Mltl::Not(Box::new(Mltl::Prop(0)))));
//! let trace: Vec<HashSet<usize>> = vec![[0].into()];
//! assert!(mltl_eval(&f, &trace));
//! ```
pub mod trace;
pub mod atom_read;
pub mod bit_trace;
pub mod top_down;
pub mod bottom_up;

pub use bottom_up::{mltl_eval_bottom_up, mltl_eval_bottom_up_bits};
pub use bit_trace::BitTrace;
pub use top_down::mltl_eval;
pub use trace::Trace;
