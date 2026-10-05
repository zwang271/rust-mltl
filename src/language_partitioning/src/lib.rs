//! Verified MLTL language partitioning, ported from AFP
//! `Mission_Time_LTL_Language_Partition` (`MLTL_Language_Partition_Algorithm.thy`,
//! `MLTL_Language_Partition_Proof.thy`).
//! Correspondence table: agent-docs/correspondence/language-partitioning.md.
//!
//! # Example
//!
//! Attach a composition to every interval ([`splits::with_width`] or
//! [`splits::with_compositions`]), then partition with [`exec::LP_mltl`].
//! The formula comes from the verified parser (via the `mltl` front-door
//! crate):
//!
//! ```
//! use language_partitioning::exec::LP_mltl;
//! use language_partitioning::splits::{with_compositions, with_width};
//!
//! let mut atoms = mltl::Atoms::new();
//! let f = atoms.parse("F[0,8] x")?;
//!
//! // Split [0,8] into three blocks of 3 steps: x first holds in block 1, 2 or 3.
//! let ext = with_compositions(&f, &vec![vec![3, 3, 3]]).unwrap();
//! let parts: Vec<String> = LP_mltl(&ext, 1).iter().map(|g| atoms.print(g)).collect();
//! assert_eq!(parts, ["F[0,2] x", "G[0,2] !x & F[3,5] x", "G[0,5] !x & F[6,8] x"]);
//!
//! // The same split, as blocks of width 3 on every interval.
//! let ext = with_width(&f, 3).unwrap();
//! assert_eq!(LP_mltl(&ext, 1).len(), 3);
//! # Ok::<(), mltl::Error>(())
//! ```
// Isabelle names (`LP_mltl`, `And_mltl_list`, …) are kept (D20).
#![allow(non_snake_case)]
pub mod ext;
pub mod composition;
pub mod algorithm;
pub mod lists;
pub mod blocks;
pub mod structure;
pub mod union;
pub mod disjoint;
pub mod exec;
pub mod splits;
