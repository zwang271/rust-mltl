//! Verified parser and printer for MLTL formulas.
//!
//! The specification is the grammar in `GRAMMAR.md`, transcribed rule by rule
//! in [`grammar`] (tokens: [`lexer`]). [`parse`] is proved to return exactly
//! the formula the grammar assigns to the text, and to fail only when the
//! text is not a formula.
//!
//! # Example
//!
//! [`Atoms`] numbers the atoms of several formulas consistently (what the
//! evaluators and other algorithms take) and prints numbered results back
//! with their names:
//!
//! ```
//! use mltl_parse::Atoms;
//!
//! let mut atoms = Atoms::new();
//! let f = atoms.parse(b"G[0,10] (request -> F[0,5] grant)").unwrap();
//! let g = atoms.parse(b"grant & !request").unwrap();
//! assert_eq!(atoms.atom(&b"request".to_vec()), Some(0));
//! assert_eq!(atoms.atom(&b"grant".to_vec()), Some(1));
//!
//! // `->` is stored as `!a | b`; printing uses as few parentheses as possible.
//! assert_eq!(atoms.print(&f), b"G[0,10] (!request | F[0,5] grant)");
//! assert_eq!(atoms.print(&g), b"grant & !request");
//!
//! // Numbers without a name print as `pN`.
//! assert_eq!(atoms.print(&mltl_core::mltl::Mltl::Prop(7)), b"p7");
//! ```
//!
//! For one-off use, [`parse_str`] returns the formula with names as atoms,
//! and [`printer::print`] prints it. Errors render like cargo's:
//!
//! ```
//! let text = "G[0,10] (request -> F[5,0] grant)";
//! let e = mltl_parse::parse_str(text).unwrap_err();
//! println!("{}", e.render(text.as_bytes(), "<input>"));
//! ```
// A plain `cargo build` erases proof code, so proof-only imports, parameters
// and fields look unused. Verus runs (`cfg(verus_only)`) still report them.
#![cfg_attr(not(verus_only), allow(unused_imports, unused_variables, dead_code,
    while_true, non_shorthand_field_patterns))]
pub mod lexer;
pub mod grammar;
pub mod parser;
pub mod printer;
pub mod numbering;
pub mod afp_binding;
pub mod error;
pub mod report;
pub mod atoms;

use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;
use crate::lexer::*;
use crate::grammar::*;
use crate::parser::*;
use crate::numbering::*;
use crate::error::*;
use mltl_core::mltl::Mltl;

pub use crate::parser::ExecFormula;
pub use crate::error::{ErrorKind, ParseError};
pub use crate::lexer::Span;
pub use crate::parser::Expected;
pub use crate::atoms::Atoms;

verus! {

/// Parse MLTL text (GRAMMAR.md) into a formula whose atoms are names.
///
/// - **Sound:** a returned formula is the one the grammar assigns to `text`.
/// - **Complete:** if the grammar assigns a formula to `text`, it is returned.
///   So an error means `text` is not a formula, and since at most one formula
///   can be returned, the grammar gives every text at most one reading.
/// - **Errors** say what went wrong and where ([`ParseError`]; render with
///   [`ParseError::render`]). Every position in them is inside `text`.
pub fn parse(text: &[u8]) -> (r: Result<ExecFormula, ParseError>)
    ensures
        r is Ok ==> denotes(text@, view_f(r->Ok_0)),
        forall|f: SpecFormula| #[trigger] denotes(text@, f) ==> r is Ok && view_f(r->Ok_0) == f,
        r is Err ==> error_ok(r->Err_0, text.len() as nat),
{
    let mut spans: Vec<Span> = Vec::new();
    let mut bad = Span { start: 0, end: 0 };
    match lex(text, &mut spans, &mut bad) {
        Some(ts) => {
            let mut fail = Fail { at: 0, expected: Expected::End, related: 0 };
            match parse_tokens(&ts, &mut fail) {
                Some(f) => Ok(f),
                None => Err(from_fail(&fail, &spans, text.len())),
            }
        },
        None => {
            let digit = bad.start < text.len() && 48 <= text[bad.start] && text[bad.start] <= 57;
            let kind = if digit { ErrorKind::NumberTooLarge } else { ErrorKind::UnknownChar };
            Err(ParseError { kind, at: bad, related: None })
        },
    }
}

/// [`parse`] for a `&str`.
pub fn parse_str(text: &str) -> (r: Result<ExecFormula, ParseError>)
    ensures
        r is Ok ==> denotes(text.spec_bytes(), view_f(r->Ok_0)),
        forall|f: SpecFormula| #[trigger] denotes(text.spec_bytes(), f) ==> r is Ok && view_f(r->Ok_0) == f,
        r is Err ==> error_ok(r->Err_0, text.spec_bytes().len()),
{
    parse(text.as_bytes())
}

/// [`parse`], then number the atoms (GRAMMAR.md §6): `pN` is atom N, other
/// names get the next free numbers in order of first appearance. Returns the
/// numbered formula and the table of non-`pN` names.
///
/// - The result is the formula `text` denotes, with each atom replaced by its
///   number; `pN` atoms get N; different atoms get different numbers.
/// - So, on traces where each atom's number holds exactly when the atom does,
///   both formulas have the same truth value
///   ([`numbering::lemma_numbering_semantics`]).
/// - Errors: those of [`parse`], or [`ParseError::NumberingFailed`] if a `pN`
///   has N ≥ usize::MAX or the numbers run out (more than usize::MAX names).
pub fn parse_numbered(text: &[u8]) -> (r: Result<(Mltl<usize>, Vec<(Vec<u8>, usize)>), ParseError>)
    ensures
        r is Ok ==> exists|f: SpecFormula| {
            &&& #[trigger] denotes(text@, f)
            &&& (r->Ok_0).0 == map_atoms(f, numbering(table_view((r->Ok_0).1@)))
            &&& number_injective(f, table_view((r->Ok_0).1@))
            &&& pn_kept(f, table_view((r->Ok_0).1@))
        },
        r is Err ==> error_ok(r->Err_0, text.len() as nat),
{
    match parse(text) {
        Ok(f) => {
            let r = number(&f);
            proof {
                if r is Some { assert(denotes(text@, view_f(f))); }
            }
            match r {
                Some(x) => Ok(x),
                None => Err(ParseError { kind: ErrorKind::NumberingFailed, at: Span { start: 0, end: text.len() }, related: None }),
            }
        },
        Err(e) => Err(e),
    }
}

} // verus!
