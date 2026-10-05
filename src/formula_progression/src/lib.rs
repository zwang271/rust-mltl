//! Verified MLTL formula progression, ported from AFP
//! `Mission_Time_LTL_Formula_Progression` (`MLTL_Formula_Progression.thy`),
//! plus the simplified progression of the unpublished
//! `Formula_Progression_Extended.thy`.
//! Correspondence table: agent-docs/correspondence/formula-progression.md.
//!
//! # Example
//!
//! [`extended::prog`] rewrites a formula after each state of a trace into
//! what the rest of the trace must satisfy. Formulas and traces come from
//! the verified parser (via the `mltl` front-door crate):
//!
//! ```
//! use formula_progression::extended::prog;
//! use formula_progression::algorithm::formula_progression;
//! use mltl_core::mltl::Mltl;
//!
//! let mut atoms = mltl::Atoms::new();
//! let f = atoms.parse("G[0,3] p")?;
//!
//! // After a state where `p` holds, three more `p` steps are needed.
//! let t = atoms.trace([["p"]])?;
//! assert_eq!(atoms.print(&prog(&f, &t)), "G[0,2] p");
//!
//! // After a state where `p` fails, the verdict is final: False.
//! let t = atoms.trace([vec!["p"], vec![]])?;
//! assert!(matches!(prog(&f, &t), Mltl::False));
//!
//! // The AFP algorithm without simplification gives an equivalent but
//! // larger formula.
//! let g = formula_progression(&f, &atoms.trace([["p"]])?);
//! assert_eq!(atoms.print(&g), "!(!true | F[0,2] !p)");
//! # Ok::<(), mltl::Error>(())
//! ```
pub mod algorithm;
pub mod correctness;
pub mod simp;
pub mod extended;
