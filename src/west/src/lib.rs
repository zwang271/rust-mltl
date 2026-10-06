//! Verified WEST: the satisfying traces of an MLTL formula as a list of
//! regular expressions. Ported from AFP `Mission_Time_LTL_to_Regular_Expression`
//! (`WEST_Algorithms.thy`, `WEST_Proofs.thy`).
//! Correspondence table: agent-docs/correspondence/west.md.
//!
//! # Example
//!
//! [`api::fast_reg_checked`] returns regular expressions that together
//! match exactly the traces satisfying the formula; [`api::trace_to_text`]
//! writes one in WEST's format (steps separated by commas, one character
//! per atom: `1` true, `0` false, `s` either). Formulas come from the
//! verified parser (via the `mltl` front-door crate):
//!
//! ```
//! use west::api::{fast_reg_checked, trace_to_text};
//!
//! let mut cx = mltl::Context::new();
//! let f = cx.parse_formula("a U[0,2] b")?;   // a is atom 0, b is atom 1
//! let r = fast_reg_checked(&f).unwrap();
//! let text: Vec<String> = (0..r.traces.len())
//!     .map(|i| String::from_utf8(trace_to_text(&r, i)).unwrap())
//!     .collect();
//! // b now; or a, then b; or a, a, then b.
//! assert_eq!(text, ["s1,ss,ss", "1s,s1,ss", "1s,1s,s1"]);
//!
//! // The same, with a header naming the columns, from the front door:
//! assert_eq!(cx.west(&f)?, "# a,b\ns1,ss,ss\n1s,s1,ss\n1s,1s,s1\n");
//! # Ok::<(), mltl::Error>(())
//! ```
// Isabelle names (`WEST_reg`, `WEST_and_state`, …) are kept (D20).
// A plain `cargo build` erases proof code, so proof-only imports, parameters
// and fields look unused. Verus runs (`cfg(verus_only)`) still report them.
#![cfg_attr(not(verus_only), allow(unused_imports, unused_variables, dead_code,
    while_true, non_shorthand_field_patterns))]
#![allow(non_snake_case)]
pub mod algorithms;
pub mod matching;
pub mod simp;
pub mod temporal;
pub mod correct;
pub mod exec;
pub mod bits;
pub mod packed;
pub mod packed_ops;
pub mod fast;
pub mod fast_reg;
pub mod api;
