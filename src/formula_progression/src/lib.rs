//! Verified MLTL formula progression, ported from AFP
//! `Mission_Time_LTL_Formula_Progression` (`MLTL_Formula_Progression.thy`),
//! plus the simplified progression of the unpublished
//! `Formula_Progression_Extended.thy`.
//! Correspondence table: agent-docs/correspondence/formula-progression.md.
pub mod algorithm;
pub mod correctness;
pub mod simp;
pub mod extended;
