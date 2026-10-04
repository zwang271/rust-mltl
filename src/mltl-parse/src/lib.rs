//! Verified parser and printer for MLTL formulas.
//!
//! The specification is the grammar in `GRAMMAR.md`, transcribed rule by rule
//! in [`grammar`] (tokens: [`lexer`]). [`parse`] is proved to return exactly
//! the formula the grammar assigns to the text, and to fail only when the
//! text is not a formula.
pub mod lexer;
pub mod grammar;
pub mod parser;
pub mod printer;
pub mod numbering;
pub mod afp_binding;
pub mod error;
pub mod report;

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
