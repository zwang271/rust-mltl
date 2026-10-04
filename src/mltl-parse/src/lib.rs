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

use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;
use crate::lexer::*;
use crate::grammar::*;
use crate::parser::*;
use crate::numbering::*;
use mltl_core::mltl::Mltl;

pub use crate::parser::ExecFormula;

verus! {

/// Parse MLTL text (GRAMMAR.md) into a formula whose atoms are names.
///
/// - **Sound:** a returned formula is the one the grammar assigns to `text`.
/// - **Complete:** if the grammar assigns a formula to `text`, it is returned.
///   So `None` means `text` is not a formula, and since at most one formula
///   can be returned, the grammar gives every text at most one reading.
pub fn parse(text: &[u8]) -> (r: Option<ExecFormula>)
    ensures
        r is Some ==> denotes(text@, view_f(r->Some_0)),
        forall|f: SpecFormula| #[trigger] denotes(text@, f) ==> r is Some && view_f(r->Some_0) == f,
{
    match lex(text) {
        Some(ts) => parse_tokens(&ts),
        None => None,
    }
}

/// [`parse`] for a `&str`.
pub fn parse_str(text: &str) -> (r: Option<ExecFormula>)
    ensures
        r is Some ==> denotes(text.spec_bytes(), view_f(r->Some_0)),
        forall|f: SpecFormula| #[trigger] denotes(text.spec_bytes(), f) ==> r is Some && view_f(r->Some_0) == f,
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
/// - `None` if `text` is not a formula, if a `pN` has N ≥ usize::MAX, or if
///   the numbers run out (more than usize::MAX distinct names).
pub fn parse_numbered(text: &[u8]) -> (r: Option<(Mltl<usize>, Vec<(Vec<u8>, usize)>)>)
    ensures
        r is Some ==> exists|f: SpecFormula| {
            &&& #[trigger] denotes(text@, f)
            &&& (r->Some_0).0 == map_atoms(f, numbering(table_view((r->Some_0).1@)))
            &&& number_injective(f, table_view((r->Some_0).1@))
            &&& pn_kept(f, table_view((r->Some_0).1@))
        },
{
    match parse(text) {
        Some(f) => {
            let r = number(&f);
            proof {
                if r is Some { assert(denotes(text@, view_f(f))); }
            }
            r
        },
        None => None,
    }
}

} // verus!
