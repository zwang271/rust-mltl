//! The grammar of GRAMMAR.md §3–4 as a specification.
//!
//! Each rule is a relation `rule(ts, lo, hi, f)`: "the tokens `ts[lo..hi]`
//! form a <rule> that means the formula `f`". The rules are written in the
//! recursive (strict BNF) form of GRAMMAR.md's rules; for example
//!
//!   conjunction = until_release { "&" until_release }
//!
//! becomes "either an until_release, or a conjunction, then `&`, then an
//! until_release", which groups `a & b & c` as `(a & b) & c`. The meaning of
//! each form (GRAMMAR.md §4) is built in: `a -> b` relates to
//! `implies_mltl(a, b)`, and so on.
use vstd::prelude::*;
use mltl_core::mltl::*;
use crate::lexer::*;

verus! {

pub type SpecFormula = Mltl<Seq<u8>>;

/// `a ^ b` (GRAMMAR.md §4): one or the other, not both.
pub open spec fn xor_mltl<A>(a: Mltl<A>, b: Mltl<A>) -> Mltl<A> {
    Mltl::Or(
        Box::new(Mltl::And(Box::new(a), Box::new(Mltl::Not(Box::new(b))))),
        Box::new(Mltl::And(Box::new(Mltl::Not(Box::new(a))), Box::new(b))),
    )
}

/// The operands `(a, b)` if `f == implies_mltl(a, b)`.
pub open spec fn implies_parts<A>(f: Mltl<A>) -> Option<(Mltl<A>, Mltl<A>)> {
    match f {
        Mltl::Or(x, r) => match *x {
            Mltl::Not(l) => Some((*l, *r)),
            _ => None,
        },
        _ => None,
    }
}

/// The operands `(a, b)` if `f == iff_mltl(a, b)`.
pub open spec fn iff_parts<A>(f: Mltl<A>) -> Option<(Mltl<A>, Mltl<A>)> {
    match f {
        Mltl::And(x, y) => match (implies_parts(*x), implies_parts(*y)) {
            (Some((l, r)), Some((r2, l2))) => if l2 == l && r2 == r { Some((l, r)) } else { None },
            _ => None,
        },
        _ => None,
    }
}

/// The operands `(a, b)` if `f == xor_mltl(a, b)`.
pub open spec fn xor_parts<A>(f: Mltl<A>) -> Option<(Mltl<A>, Mltl<A>)> {
    match f {
        Mltl::Or(x, y) => match (*x, *y) {
            (Mltl::And(a, nb), Mltl::And(na, b)) => match (*nb, *na) {
                (Mltl::Not(b2), Mltl::Not(a2)) =>
                    if *a2 == *a && *b2 == *b { Some((*a, *b)) } else { None },
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// `ts[lo..hi]` is a non-empty span of `ts`.
pub open spec fn span(ts: Seq<SpecToken>, lo: int, hi: int) -> bool {
    0 <= lo < hi <= ts.len()
}

/// `interval = "[" number "," number "]"` starting at `k`, with `a ≤ b`
/// (GRAMMAR.md §3, side condition).
pub open spec fn interval(ts: Seq<SpecToken>, k: int, a: usize, b: usize) -> bool {
    &&& 0 <= k && k + 5 <= ts.len()
    &&& ts[k] is LBrack
    &&& ts[k + 1] == Token::<Seq<u8>>::Num(a)
    &&& ts[k + 2] is Comma
    &&& ts[k + 3] == Token::<Seq<u8>>::Num(b)
    &&& ts[k + 4] is RBrack
    &&& a <= b
}

/// `atom = "true" | "t" | "tt" | "false" | "f" | "ff" | name | "(" formula ")"`
/// (`t`, `tt` are already the token `True`; `f`, `ff` the token `False`).
pub open spec fn atom(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool
    decreases hi - lo, 0nat,
{
    span(ts, lo, hi) && (
        (hi == lo + 1 && ts[lo] is True && f is True)
        || (hi == lo + 1 && ts[lo] is False && f is False)
        || (hi == lo + 1 && ts[lo] is Name && f == Mltl::Prop(ts[lo]->Name_0))
        || (lo + 2 <= hi && ts[lo] is LParen && ts[hi - 1] is RParen && formula(ts, lo + 1, hi - 1, f))
    )
}

/// `unary = atom | "!" unary | "F" interval unary | "G" interval unary`
pub open spec fn unary(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool
    decreases hi - lo, 1nat,
{
    span(ts, lo, hi) && (
        atom(ts, lo, hi, f)
        || (ts[lo] is Not && f is Not && unary(ts, lo + 1, hi, *(f->Not_0)))
        || (lo + 6 <= hi && ts[lo] is KwF && f is Future
            && interval(ts, lo + 1, f->Future_0, f->Future_1) && unary(ts, lo + 6, hi, *(f->Future_2)))
        || (lo + 6 <= hi && ts[lo] is KwG && f is Global
            && interval(ts, lo + 1, f->Global_0, f->Global_1) && unary(ts, lo + 6, hi, *(f->Global_2)))
    )
}

/// `until_release = unary [ ( "U" | "R" ) interval unary ]`
pub open spec fn until_release(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool
    decreases hi - lo, 2nat,
{
    span(ts, lo, hi) && (
        unary(ts, lo, hi, f)
        || (f is Until && exists|m: int| #![trigger ts[m]] lo < m && m + 6 <= hi && ts[m] is KwU
            && interval(ts, m + 1, f->Until_1, f->Until_2)
            && unary(ts, lo, m, *(f->Until_0)) && unary(ts, m + 6, hi, *(f->Until_3)))
        || (f is Release && exists|m: int| #![trigger ts[m]] lo < m && m + 6 <= hi && ts[m] is KwR
            && interval(ts, m + 1, f->Release_1, f->Release_2)
            && unary(ts, lo, m, *(f->Release_0)) && unary(ts, m + 6, hi, *(f->Release_3)))
    )
}

/// `conjunction = until_release { "&" until_release }`
pub open spec fn conjunction(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool
    decreases hi - lo, 3nat,
{
    span(ts, lo, hi) && (
        until_release(ts, lo, hi, f)
        || (f is And && exists|m: int| #![trigger ts[m]] lo < m && m < hi && ts[m] is And
            && conjunction(ts, lo, m, *(f->And_0)) && until_release(ts, m + 1, hi, *(f->And_1)))
    )
}

/// `exclusive_or = conjunction { "^" conjunction }`
pub open spec fn exclusive_or(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool
    decreases hi - lo, 4nat,
{
    span(ts, lo, hi) && (
        conjunction(ts, lo, hi, f)
        || (xor_parts(f) is Some && exists|m: int| #![trigger ts[m]] lo < m && m < hi && ts[m] is Xor
            && exclusive_or(ts, lo, m, (xor_parts(f)->Some_0).0) && conjunction(ts, m + 1, hi, (xor_parts(f)->Some_0).1))
    )
}

/// `disjunction = exclusive_or { "|" exclusive_or }`
pub open spec fn disjunction(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool
    decreases hi - lo, 5nat,
{
    span(ts, lo, hi) && (
        exclusive_or(ts, lo, hi, f)
        || (f is Or && exists|m: int| #![trigger ts[m]] lo < m && m < hi && ts[m] is Or
            && disjunction(ts, lo, m, *(f->Or_0)) && exclusive_or(ts, m + 1, hi, *(f->Or_1)))
    )
}

/// `implication = disjunction [ ( "->" | "<->" ) disjunction ]`
pub open spec fn implication(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool
    decreases hi - lo, 6nat,
{
    span(ts, lo, hi) && (
        disjunction(ts, lo, hi, f)
        || (implies_parts(f) is Some && exists|m: int| #![trigger ts[m]] lo < m && m < hi && ts[m] is Implies
            && disjunction(ts, lo, m, (implies_parts(f)->Some_0).0) && disjunction(ts, m + 1, hi, (implies_parts(f)->Some_0).1))
        || (iff_parts(f) is Some && exists|m: int| #![trigger ts[m]] lo < m && m < hi && ts[m] is Iff
            && disjunction(ts, lo, m, (iff_parts(f)->Some_0).0) && disjunction(ts, m + 1, hi, (iff_parts(f)->Some_0).1))
    )
}

/// `formula = implication`
pub open spec fn formula(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool
    decreases hi - lo, 7nat,
{
    implication(ts, lo, hi, f)
}

/// The text `s` denotes the formula `f`: it splits into tokens, and the
/// whole token sequence is a `formula` meaning `f`.
pub open spec fn denotes(s: Seq<u8>, f: SpecFormula) -> bool {
    match lex_spec(s) {
        Some(ts) => formula(ts, 0, ts.len() as int, f),
        None => false,
    }
}

// Which token may follow a complete piece of each level without extending
// it. Used by the completeness proofs: the parser stops a level exactly when
// the next token cannot continue it.

pub open spec fn stop_until_release(ts: Seq<SpecToken>, k: int) -> bool {
    k == ts.len() || !(ts[k] is KwU || ts[k] is KwR)
}

pub open spec fn stop_conjunction(ts: Seq<SpecToken>, k: int) -> bool {
    stop_until_release(ts, k) && (k == ts.len() || !(ts[k] is And))
}

pub open spec fn stop_exclusive_or(ts: Seq<SpecToken>, k: int) -> bool {
    stop_conjunction(ts, k) && (k == ts.len() || !(ts[k] is Xor))
}

pub open spec fn stop_disjunction(ts: Seq<SpecToken>, k: int) -> bool {
    stop_exclusive_or(ts, k) && (k == ts.len() || !(ts[k] is Or))
}

pub open spec fn stop_implication(ts: Seq<SpecToken>, k: int) -> bool {
    stop_disjunction(ts, k) && (k == ts.len() || !(ts[k] is Implies || ts[k] is Iff))
}

pub proof fn lemma_implies_parts<A>(l: Mltl<A>, r: Mltl<A>)
    ensures
        implies_parts(implies_mltl(l, r)) == Some((l, r)),
{
}

pub proof fn lemma_iff_parts<A>(l: Mltl<A>, r: Mltl<A>)
    ensures
        iff_parts(iff_mltl(l, r)) == Some((l, r)),
{
}

pub proof fn lemma_xor_parts<A>(l: Mltl<A>, r: Mltl<A>)
    ensures
        xor_parts(xor_mltl(l, r)) == Some((l, r)),
{
}

pub proof fn lemma_parts_inverse<A>(f: Mltl<A>)
    ensures
        implies_parts(f) is Some ==> f == implies_mltl((implies_parts(f)->Some_0).0, (implies_parts(f)->Some_0).1),
        iff_parts(f) is Some ==> f == iff_mltl((iff_parts(f)->Some_0).0, (iff_parts(f)->Some_0).1),
        xor_parts(f) is Some ==> f == xor_mltl((xor_parts(f)->Some_0).0, (xor_parts(f)->Some_0).1),
{
}

} // verus!
