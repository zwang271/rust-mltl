//! Parse errors: where the verified lexer or parser stopped, as positions in
//! the text. Turning them into messages is `report.rs`.
use vstd::prelude::*;
use crate::lexer::*;
use crate::parser::*;

verus! {

/// What went wrong.
pub enum ErrorKind {
    /// A character that starts no token.
    UnknownChar,
    /// A number larger than `usize::MAX`.
    NumberTooLarge,
    /// The parser expected something else at `at`.
    Expected(Expected),
    /// `parse_numbered` only: a `pN` with N ≥ usize::MAX, or more names than
    /// numbers.
    NumberingFailed,
}

/// A text that is not a formula: what went wrong, where (`at`), and the
/// related operator or `(` for interval and parenthesis errors.
pub struct ParseError {
    pub kind: ErrorKind,
    pub at: Span,
    pub related: Option<Span>,
}

/// Every position in `e` is inside a text of length `n`.
pub open spec fn error_ok(e: ParseError, n: nat) -> bool {
    &&& span_ok(e.at, n)
    &&& match e.related {
        Some(s) => span_ok(s, n),
        None => true,
    }
}

/// The span of token `k`, or the end of the text for `k == spans.len()`.
fn token_span(spans: &Vec<Span>, k: usize, Ghost(n): Ghost<nat>, end: usize) -> (r: Span)
    requires
        spans_ok(spans@, spans.len() as nat, n),
        k <= spans.len(),
        end == n,
    ensures
        span_ok(r, n),
{
    if k < spans.len() {
        proof { assert(spans@[k as int].start < spans@[k as int].end); }
        Span { start: spans[k].start, end: spans[k].end }
    } else {
        Span { start: end, end }
    }
}

/// The error for a parser failure, given the tokens' positions.
pub fn from_fail(fail: &Fail, spans: &Vec<Span>, n: usize) -> (r: ParseError)
    requires
        spans_ok(spans@, spans.len() as nat, n as nat),
        fail_ok(*fail, spans.len() as nat),
    ensures
        error_ok(r, n as nat),
{
    let at = token_span(spans, fail.at, Ghost(n as nat), n);
    let (kind, related) = match fail.expected {
        Expected::Formula => (Expected::Formula, false),
        Expected::IntervalOpen => (Expected::IntervalOpen, true),
        Expected::IntervalLo => (Expected::IntervalLo, true),
        Expected::IntervalComma => (Expected::IntervalComma, true),
        Expected::IntervalHi => (Expected::IntervalHi, true),
        Expected::IntervalClose => (Expected::IntervalClose, true),
        Expected::IntervalOrder => (Expected::IntervalOrder, true),
        Expected::CloseParen => (Expected::CloseParen, true),
        Expected::End => (Expected::End, false),
    };
    let related = if related { Some(token_span(spans, fail.related, Ghost(n as nat), n)) } else { None };
    ParseError { kind: ErrorKind::Expected(kind), at, related }
}

} // verus!
