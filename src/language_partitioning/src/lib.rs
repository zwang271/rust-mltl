//! Verified MLTL language partitioning, ported from AFP
//! `Mission_Time_LTL_Language_Partition` (`MLTL_Language_Partition_Algorithm.thy`,
//! `MLTL_Language_Partition_Proof.thy`).
//! Correspondence table: agent-docs/correspondence/language-partitioning.md.
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
