//! The parser: one function per grammar rule (`grammar.rs`), each proved
//! sound and complete for its rule.
//!
//! `p_<rule>(ts, i)` parses a `<rule>` starting at token `i` and returns the
//! formula and the position after it. Its guarantee has two halves:
//! - sound: if it returns `(f, j)`, then `ts[i..j]` is a `<rule>` meaning `f`;
//! - complete: if `ts[i..k]` is a `<rule>` meaning `f`, and the token at `k`
//!   cannot continue a `<rule>` (`stop_<rule>`), then it returns `(f, k)`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use crate::lexer::*;
use crate::grammar::*;

verus! {

pub type ExecFormula = Mltl<Vec<u8>>;
pub type Parsed = Option<(ExecFormula, usize)>;

/// What the parser expected where it stopped.
pub enum Expected {
    /// A formula: a name, `true`, `false`, `(`, `!`, `F` or `G`.
    Formula,
    /// The `[` of an interval.
    IntervalOpen,
    /// The first number of an interval.
    IntervalLo,
    /// The `,` of an interval.
    IntervalComma,
    /// The second number of an interval.
    IntervalHi,
    /// The `]` of an interval.
    IntervalClose,
    /// An interval `[a,b]` with `a ≤ b` (here `a > b`).
    IntervalOrder,
    /// The `)` closing the `(` at `related`.
    CloseParen,
    /// The end of the text, after a complete formula.
    End,
}

/// Where and why the parser stopped: at token `at` (`ts.len()` for the end),
/// expecting `expected`. `related` is the operator whose interval failed, or
/// the `(` that is not closed; otherwise equal to `at`.
pub struct Fail {
    pub at: usize,
    pub expected: Expected,
    pub related: usize,
}

pub open spec fn fail_ok(e: Fail, len: nat) -> bool {
    e.at <= len && e.related <= len
}

/// The specification formula denoted by an executable formula.
pub open spec fn view_f(f: ExecFormula) -> SpecFormula
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(n) => Mltl::Prop(n@),
        Mltl::Not(g) => Mltl::Not(Box::new(view_f(*g))),
        Mltl::And(g, h) => Mltl::And(Box::new(view_f(*g)), Box::new(view_f(*h))),
        Mltl::Or(g, h) => Mltl::Or(Box::new(view_f(*g)), Box::new(view_f(*h))),
        Mltl::Future(a, b, g) => Mltl::Future(a, b, Box::new(view_f(*g))),
        Mltl::Global(a, b, g) => Mltl::Global(a, b, Box::new(view_f(*g))),
        Mltl::Until(g, a, b, h) => Mltl::Until(Box::new(view_f(*g)), a, b, Box::new(view_f(*h))),
        Mltl::Release(g, a, b, h) => Mltl::Release(Box::new(view_f(*g)), a, b, Box::new(view_f(*h))),
    }
}

/// The parser returned exactly `(f, k)`.
pub open spec fn returns(r: Parsed, f: SpecFormula, k: int) -> bool {
    r is Some && (r->Some_0).1 == k && view_f((r->Some_0).0) == f
}

/// `r` is `None`, or a result `(f, j)` with `i < j <= len`.
pub open spec fn advances(r: Parsed, i: int, len: int) -> bool {
    r is Some ==> i < (r->Some_0).1 <= len
}

pub fn copy_vec(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == v@,
{
    let mut r: Vec<u8> = Vec::with_capacity(v.len());
    let mut k = 0;
    while k < v.len()
        invariant
            k <= v.len(),
            r@ == v@.subrange(0, k as int),
        decreases v.len() - k,
    {
        r.push(v[k]);
        k = k + 1;
        proof { assert(r@ =~= v@.subrange(0, k as int)); }
    }
    proof { assert(r@ =~= v@); }
    r
}

/// Deep copy (needed where a desugaring uses an operand twice).
pub fn clone_named(f: &ExecFormula) -> (r: ExecFormula)
    ensures
        view_f(r) == view_f(*f),
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(n) => Mltl::Prop(copy_vec(n)),
        Mltl::Not(g) => Mltl::Not(Box::new(clone_named(g))),
        Mltl::And(g, h) => Mltl::And(Box::new(clone_named(g)), Box::new(clone_named(h))),
        Mltl::Or(g, h) => Mltl::Or(Box::new(clone_named(g)), Box::new(clone_named(h))),
        Mltl::Future(a, b, g) => Mltl::Future(*a, *b, Box::new(clone_named(g))),
        Mltl::Global(a, b, g) => Mltl::Global(*a, *b, Box::new(clone_named(g))),
        Mltl::Until(g, a, b, h) => Mltl::Until(Box::new(clone_named(g)), *a, *b, Box::new(clone_named(h))),
        Mltl::Release(g, a, b, h) => Mltl::Release(Box::new(clone_named(g)), *a, *b, Box::new(clone_named(h))),
    }
}

/// `interval` at token `k` (the operator is token `k - 1`): exactly the
/// bounds of the interval there, if any.
fn p_interval(ts: &Vec<Token<Vec<u8>>>, k: usize, fail: &mut Fail) -> (r: Option<(usize, usize)>)
    requires
        1 <= k <= ts.len(),
    ensures
        r is Some ==> interval(tokens_view(ts@), k as int, (r->Some_0).0, (r->Some_0).1),
        forall|a: usize, b: usize| #[trigger] interval(tokens_view(ts@), k as int, a, b) ==> r == Some((a, b)),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
{
    let ghost tv = tokens_view(ts@);
    let n = ts.len();
    let op = k - 1;
    proof {
        assert forall|m: int| k <= m < n implies #[trigger] tv[m] == token_view(ts@[m]) by {}
    }
    if n - k < 1 || !matches!(ts[k], Token::LBrack) {
        *fail = Fail { at: k, expected: Expected::IntervalOpen, related: op };
        return None;
    }
    if n - k < 2 || !matches!(ts[k + 1], Token::Num(_)) {
        *fail = Fail { at: k + 1, expected: Expected::IntervalLo, related: op };
        return None;
    }
    if n - k < 3 || !matches!(ts[k + 2], Token::Comma) {
        *fail = Fail { at: k + 2, expected: Expected::IntervalComma, related: op };
        return None;
    }
    if n - k < 4 || !matches!(ts[k + 3], Token::Num(_)) {
        *fail = Fail { at: k + 3, expected: Expected::IntervalHi, related: op };
        return None;
    }
    if n - k < 5 || !matches!(ts[k + 4], Token::RBrack) {
        *fail = Fail { at: k + 4, expected: Expected::IntervalClose, related: op };
        return None;
    }
    match (&ts[k], &ts[k + 1], &ts[k + 2], &ts[k + 3], &ts[k + 4]) {
        (Token::LBrack, Token::Num(a), Token::Comma, Token::Num(b), Token::RBrack) => {
            if *a <= *b {
                Some((*a, *b))
            } else {
                *fail = Fail { at: k + 1, expected: Expected::IntervalOrder, related: op };
                None
            }
        },
        _ => {
            *fail = Fail { at: k, expected: Expected::IntervalOpen, related: op };
            None
        },
    }
}

/// `atom` at token `i`.
fn p_atom(ts: &Vec<Token<Vec<u8>>>, i: usize, fail: &mut Fail) -> (r: Parsed)
    requires
        i <= ts.len(),
    ensures
        advances(r, i as int, ts.len() as int),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> atom(tokens_view(ts@), i as int, (r->Some_0).1 as int, view_f((r->Some_0).0)),
        forall|k: int, f: SpecFormula| #[trigger] atom(tokens_view(ts@), i as int, k, f) ==> returns(r, f, k),
    decreases ts.len() - i, 0nat,
{
    let ghost tv = tokens_view(ts@);
    if i >= ts.len() {
        *fail = Fail { at: i, expected: Expected::Formula, related: i };
        return None;
    }
    proof { assert(tv[i as int] == token_view(ts@[i as int])); }
    match &ts[i] {
        Token::True => Some((Mltl::True, i + 1)),
        Token::False => Some((Mltl::False, i + 1)),
        Token::Name(n) => Some((Mltl::Prop(copy_vec(n)), i + 1)),
        Token::LParen => {
            let inner = p_formula(ts, i + 1, fail);
            match inner {
                Some((g, j)) => {
                    if j < ts.len() && matches!(ts[j], Token::RParen) {
                        let r = Some((g, j + 1));
                        proof {
                            assert(tv[j as int] == token_view(ts@[j as int]));
                            assert forall|k: int, f: SpecFormula| #[trigger] atom(tv, i as int, k, f)
                                implies returns(r, f, k) by {
                                assert(formula(tv, (i + 1) as int, k - 1, f));
                                assert(stop_implication(tv, k - 1));
                            }
                        }
                        r
                    } else {
                        proof {
                            assert(j < ts.len() ==> tv[j as int] == token_view(ts@[j as int]));
                            assert forall|k: int, f: SpecFormula| #[trigger] atom(tv, i as int, k, f)
                                implies returns(None, f, k) by {
                                assert(formula(tv, (i + 1) as int, k - 1, f));
                                assert(stop_implication(tv, k - 1));
                            }
                        }
                        *fail = Fail { at: j, expected: Expected::CloseParen, related: i };
                        None
                    }
                },
                None => {
                    proof {
                        assert forall|k: int, f: SpecFormula| #[trigger] atom(tv, i as int, k, f)
                            implies returns(None, f, k) by {
                            assert(formula(tv, (i + 1) as int, k - 1, f));
                            assert(stop_implication(tv, k - 1));
                        }
                    }
                    None
                },
            }
        },
        _ => {
            *fail = Fail { at: i, expected: Expected::Formula, related: i };
            None
        },
    }
}

/// `unary` at token `i`.
fn p_unary(ts: &Vec<Token<Vec<u8>>>, i: usize, fail: &mut Fail) -> (r: Parsed)
    requires
        i <= ts.len(),
    ensures
        advances(r, i as int, ts.len() as int),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> unary(tokens_view(ts@), i as int, (r->Some_0).1 as int, view_f((r->Some_0).0)),
        forall|k: int, f: SpecFormula| #[trigger] unary(tokens_view(ts@), i as int, k, f) ==> returns(r, f, k),
    decreases ts.len() - i, 1nat,
{
    let ghost tv = tokens_view(ts@);
    if i < ts.len() {
        proof { assert(tv[i as int] == token_view(ts@[i as int])); }
        match &ts[i] {
            Token::Not => {
                let sub = p_unary(ts, i + 1, fail);
                let r = match sub {
                    Some((g, j)) => Some((Mltl::Not(Box::new(g)), j)),
                    None => None,
                };
                proof {
                    assert forall|k: int, f: SpecFormula| #[trigger] unary(tv, i as int, k, f)
                        implies returns(r, f, k) by {
                        assert(!atom(tv, i as int, k, f));
                        assert(unary(tv, (i + 1) as int, k, *(f->Not_0)));
                    }
                }
                return r;
            },
            Token::KwF | Token::KwG => {
                let is_f = matches!(ts[i], Token::KwF);
                let iv = p_interval(ts, i + 1, fail);
                let r = match iv {
                    Some((a, b)) => {
                        let sub = p_unary(ts, i + 6, fail);
                        match sub {
                            Some((g, j)) => {
                                if is_f { Some((Mltl::Future(a, b, Box::new(g)), j)) }
                                else { Some((Mltl::Global(a, b, Box::new(g)), j)) }
                            },
                            None => None,
                        }
                    },
                    None => None,
                };
                proof {
                    assert forall|k: int, f: SpecFormula| #[trigger] unary(tv, i as int, k, f)
                        implies returns(r, f, k) by {
                        assert(!atom(tv, i as int, k, f));
                        if is_f {
                            assert(interval(tv, (i + 1) as int, f->Future_0, f->Future_1));
                            assert(unary(tv, (i + 6) as int, k, *(f->Future_2)));
                        } else {
                            assert(interval(tv, (i + 1) as int, f->Global_0, f->Global_1));
                            assert(unary(tv, (i + 6) as int, k, *(f->Global_2)));
                        }
                    }
                }
                return r;
            },
            _ => {},
        }
    }
    let r = p_atom(ts, i, fail);
    proof {
        assert forall|k: int, f: SpecFormula| #[trigger] unary(tv, i as int, k, f)
            implies returns(r, f, k) by {
            assert(i < ts.len() ==> tv[i as int] == token_view(ts@[i as int]));
            assert(atom(tv, i as int, k, f));
        }
    }
    r
}

/// `a ^ b` built as `xor_mltl(a, b)` (operands are copied: each occurs twice).
fn exec_xor(a: ExecFormula, b: ExecFormula) -> (r: ExecFormula)
    ensures
        view_f(r) == xor_mltl(view_f(a), view_f(b)),
{
    reveal_with_fuel(view_f, 4);
    let a2 = clone_named(&a);
    let b2 = clone_named(&b);
    Mltl::Or(
        Box::new(Mltl::And(Box::new(a), Box::new(Mltl::Not(Box::new(b))))),
        Box::new(Mltl::And(Box::new(Mltl::Not(Box::new(a2))), Box::new(b2))),
    )
}

/// `a <-> b` built as `iff_mltl(a, b)`.
fn exec_iff(a: ExecFormula, b: ExecFormula) -> (r: ExecFormula)
    ensures
        view_f(r) == iff_mltl(view_f(a), view_f(b)),
{
    reveal_with_fuel(view_f, 4);
    let a2 = clone_named(&a);
    let b2 = clone_named(&b);
    Mltl::And(
        Box::new(Mltl::Or(Box::new(Mltl::Not(Box::new(a))), Box::new(b))),
        Box::new(Mltl::Or(Box::new(Mltl::Not(Box::new(b2))), Box::new(a2))),
    )
}

/// `until_release` at token `i`.
fn p_until_release(ts: &Vec<Token<Vec<u8>>>, i: usize, fail: &mut Fail) -> (r: Parsed)
    requires
        i <= ts.len(),
    ensures
        advances(r, i as int, ts.len() as int),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> until_release(tokens_view(ts@), i as int, (r->Some_0).1 as int, view_f((r->Some_0).0)),
        forall|k: int, f: SpecFormula| #[trigger] until_release(tokens_view(ts@), i as int, k, f)
            && stop_until_release(tokens_view(ts@), k) ==> returns(r, f, k),
    decreases ts.len() - i, 2nat,
{
    let ghost tv = tokens_view(ts@);
    let first = p_unary(ts, i, fail);
    match first {
        None => {
            proof {
                assert forall|k: int, f: SpecFormula| #[trigger] until_release(tv, i as int, k, f)
                    && stop_until_release(tv, k) implies returns(None, f, k) by {
                    if !unary(tv, i as int, k, f) {
                        if f is Until {
                            let m = choose|m: int| #![trigger tv[m]] i < m && m + 6 <= k && tv[m] is KwU
                                && interval(tv, m + 1, f->Until_1, f->Until_2)
                                && unary(tv, i as int, m, *(f->Until_0)) && unary(tv, m + 6, k, *(f->Until_3));
                        } else {
                            let m = choose|m: int| #![trigger tv[m]] i < m && m + 6 <= k && tv[m] is KwR
                                && interval(tv, m + 1, f->Release_1, f->Release_2)
                                && unary(tv, i as int, m, *(f->Release_0)) && unary(tv, m + 6, k, *(f->Release_3));
                        }
                    }
                }
            }
            None
        },
        Some((g1, j)) => {
            if j < ts.len() && (matches!(ts[j], Token::KwU) || matches!(ts[j], Token::KwR)) {
                proof { assert(tv[j as int] == token_view(ts@[j as int])); }
                let is_u = matches!(ts[j], Token::KwU);
                let iv = p_interval(ts, j + 1, fail);
                let r = match iv {
                    Some((a, b)) => {
                        let sub = p_unary(ts, j + 6, fail);
                        match sub {
                            Some((g2, k2)) => {
                                let f = if is_u { Mltl::Until(Box::new(g1), a, b, Box::new(g2)) }
                                        else { Mltl::Release(Box::new(g1), a, b, Box::new(g2)) };
                                Some((f, k2))
                            },
                            None => None,
                        }
                    },
                    None => None,
                };
                proof {
                    if r is Some {
                        let k2 = (r->Some_0).1 as int;
                        let f = view_f((r->Some_0).0);
                        if is_u {
                            assert(i < j && j + 6 <= k2 && tv[j as int] is KwU
                                && interval(tv, j + 1, f->Until_1, f->Until_2)
                                && unary(tv, i as int, j as int, *(f->Until_0)) && unary(tv, j + 6, k2, *(f->Until_3)));
                        } else {
                            assert(i < j && j + 6 <= k2 && tv[j as int] is KwR
                                && interval(tv, j + 1, f->Release_1, f->Release_2)
                                && unary(tv, i as int, j as int, *(f->Release_0)) && unary(tv, j + 6, k2, *(f->Release_3)));
                        }
                    }
                    assert forall|k: int, f: SpecFormula| #[trigger] until_release(tv, i as int, k, f)
                        && stop_until_release(tv, k) implies returns(r, f, k) by {
                        if unary(tv, i as int, k, f) {
                            assert(k == j);
                        } else if f is Until {
                            let m = choose|m: int| #![trigger tv[m]] i < m && m + 6 <= k && tv[m] is KwU
                                && interval(tv, m + 1, f->Until_1, f->Until_2)
                                && unary(tv, i as int, m, *(f->Until_0)) && unary(tv, m + 6, k, *(f->Until_3));
                            assert(m == j);
                            assert(interval(tv, (j + 1) as int, f->Until_1, f->Until_2));
                            assert(unary(tv, (j + 6) as int, k, *(f->Until_3)));
                        } else {
                            let m = choose|m: int| #![trigger tv[m]] i < m && m + 6 <= k && tv[m] is KwR
                                && interval(tv, m + 1, f->Release_1, f->Release_2)
                                && unary(tv, i as int, m, *(f->Release_0)) && unary(tv, m + 6, k, *(f->Release_3));
                            assert(m == j);
                            assert(interval(tv, (j + 1) as int, f->Release_1, f->Release_2));
                            assert(unary(tv, (j + 6) as int, k, *(f->Release_3)));
                        }
                    }
                }
                r
            } else {
                let r = Some((g1, j));
                proof {
                    assert(j < ts.len() ==> tv[j as int] == token_view(ts@[j as int]));
                    assert forall|k: int, f: SpecFormula| #[trigger] until_release(tv, i as int, k, f)
                        && stop_until_release(tv, k) implies returns(r, f, k) by {
                        if !unary(tv, i as int, k, f) {
                            if f is Until {
                                let m = choose|m: int| #![trigger tv[m]] i < m && m + 6 <= k && tv[m] is KwU
                                    && interval(tv, m + 1, f->Until_1, f->Until_2)
                                    && unary(tv, i as int, m, *(f->Until_0)) && unary(tv, m + 6, k, *(f->Until_3));
                                assert(m == j);
                            } else {
                                let m = choose|m: int| #![trigger tv[m]] i < m && m + 6 <= k && tv[m] is KwR
                                    && interval(tv, m + 1, f->Release_1, f->Release_2)
                                    && unary(tv, i as int, m, *(f->Release_0)) && unary(tv, m + 6, k, *(f->Release_3));
                                assert(m == j);
                            }
                        }
                    }
                }
                r
            }
        },
    }
}

// ---------------------------------------------------------------------------
// conjunction = until_release { "&" until_release }
// ---------------------------------------------------------------------------

/// Proof helper: `f`'s derivation as a conjunction over `[i, k]` passes through
/// position `j` with `acc` as its value over `[i, j]` (the left spine of the chain).
pub open spec fn spine_conjunction(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula) -> bool
    decreases k - j,
{
    (j == k && acc == f)
    || (j < k && f is And && exists|m: int| #![trigger tv[m]] j <= m < k && tv[m] is And
        && spine_conjunction(tv, j, acc, m, *(f->And_0)) && until_release(tv, m + 1, k, *(f->And_1)))
}

proof fn lemma_conjunction_spine(tv: Seq<SpecToken>, i: int, k: int, f: SpecFormula) -> (r: (int, SpecFormula))
    requires
        conjunction(tv, i, k, f),
    ensures
        i < r.0 <= k,
        until_release(tv, i, r.0, r.1),
        spine_conjunction(tv, r.0, r.1, k, f),
        r.0 == k || tv[r.0] is And,
    decreases k - i,
{
    if until_release(tv, i, k, f) {
        (k, f)
    } else {
        let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is And
            && conjunction(tv, i, m, *(f->And_0)) && until_release(tv, m + 1, k, *(f->And_1));
        let (j0, g0) = lemma_conjunction_spine(tv, i, m, *(f->And_0));
        assert(spine_conjunction(tv, j0, g0, k, f));
        (j0, g0)
    }
}

proof fn lemma_conjunction_spine_step(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula)
    -> (r: (int, SpecFormula))
    requires
        spine_conjunction(tv, j, acc, k, f),
        j < k,
    ensures
        tv[j] is And,
        j + 1 < r.0 <= k,
        until_release(tv, j + 1, r.0, r.1),
        r.0 == k || tv[r.0] is And,
        spine_conjunction(tv, r.0, Mltl::And(Box::new(acc), Box::new(r.1)), k, f),
    decreases k - j,
{
    let m = choose|m: int| #![trigger tv[m]] j <= m < k && tv[m] is And
        && spine_conjunction(tv, j, acc, m, *(f->And_0)) && until_release(tv, m + 1, k, *(f->And_1));
    lemma_parts_inverse(f);
    if j == m {
        assert(acc == *(f->And_0));
        assert(Mltl::And(Box::new(acc), Box::new(*(f->And_1))) == f);
        (k, *(f->And_1))
    } else {
        let (m2, h) = lemma_conjunction_spine_step(tv, j, acc, m, *(f->And_0));
        assert(spine_conjunction(tv, m2, Mltl::And(Box::new(acc), Box::new(h)), k, f));
        (m2, h)
    }
}

proof fn lemma_conjunction_spine_le(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula)
    requires
        spine_conjunction(tv, j, acc, k, f),
    ensures
        j <= k,
        j == k ==> acc == f,
{
}

/// `conjunction` at token `i`.
fn p_conjunction(ts: &Vec<Token<Vec<u8>>>, i: usize, fail: &mut Fail) -> (r: Parsed)
    requires
        i <= ts.len(),
    ensures
        advances(r, i as int, ts.len() as int),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> conjunction(tokens_view(ts@), i as int, (r->Some_0).1 as int, view_f((r->Some_0).0)),
        forall|k: int, f: SpecFormula| #[trigger] conjunction(tokens_view(ts@), i as int, k, f)
            && stop_conjunction(tokens_view(ts@), k) ==> returns(r, f, k),
    decreases ts.len() - i, 3nat,
{
    let ghost tv = tokens_view(ts@);
    let first = p_until_release(ts, i, fail);
    match first {
        None => {
            proof {
                assert forall|k: int, f: SpecFormula| #[trigger] conjunction(tv, i as int, k, f)
                    && stop_conjunction(tv, k) implies returns(None, f, k) by {
                    let (j0, g0) = lemma_conjunction_spine(tv, i as int, k, f);
                    assert(stop_until_release(tv, j0));
                }
            }
            None
        },
        Some((g, j)) => {
            let mut acc = g;
            let mut pos = j;
            proof {
                assert forall|k: int, f: SpecFormula| #[trigger] conjunction(tv, i as int, k, f)
                    && stop_conjunction(tv, k) implies spine_conjunction(tv, pos as int, view_f(acc), k, f) by {
                    let (j0, g0) = lemma_conjunction_spine(tv, i as int, k, f);
                    assert(stop_until_release(tv, j0));
                }
            }
            while pos < ts.len() && matches!(ts[pos], Token::And)
                invariant
                    i < pos <= ts.len(),
                    tv == tokens_view(ts@),
                    conjunction(tv, i as int, pos as int, view_f(acc)),
                    forall|k: int, f: SpecFormula| #[trigger] conjunction(tv, i as int, k, f)
                        && stop_conjunction(tv, k) ==> spine_conjunction(tv, pos as int, view_f(acc), k, f),
                decreases ts.len() - pos,
            {
                proof { assert(tv[pos as int] == token_view(ts@[pos as int])); }
                let next = p_until_release(ts, pos + 1, fail);
                match next {
                    None => {
                        proof {
                            assert forall|k: int, f: SpecFormula| #[trigger] conjunction(tv, i as int, k, f)
                                && stop_conjunction(tv, k) implies returns(None, f, k) by {
                                lemma_conjunction_spine_le(tv, pos as int, view_f(acc), k, f);
                                if pos as int == k {
                                    assert(false);
                                }
                                let (m2, h) = lemma_conjunction_spine_step(tv, pos as int, view_f(acc), k, f);
                                assert(stop_until_release(tv, m2));
                                assert(until_release(tv, (pos + 1) as int, m2, h));
                            }
                        }
                        return None;
                    },
                    Some((h, k2)) => {
                        let ghost old_acc = view_f(acc);
                        let ghost old_pos = pos as int;
                        acc = Mltl::And(Box::new(acc), Box::new(h));
                        pos = k2;
                        proof {
                            assert(view_f(acc) == Mltl::And(Box::new(old_acc), Box::new(view_f(h))));
                            lemma_parts_inverse(view_f(acc));
                            
                            assert(conjunction(tv, i as int, pos as int, view_f(acc))) by {
                                assert(conjunction(tv, i as int, old_pos, old_acc));
                                assert(until_release(tv, old_pos + 1, pos as int, view_f(h)));
                            }
                            assert forall|k: int, f: SpecFormula| #[trigger] conjunction(tv, i as int, k, f)
                                && stop_conjunction(tv, k) implies spine_conjunction(tv, pos as int, view_f(acc), k, f) by {
                                assert(spine_conjunction(tv, old_pos, old_acc, k, f));
                                lemma_conjunction_spine_le(tv, old_pos, old_acc, k, f);
                                if old_pos == k {
                                    assert(false);
                                }
                                let (m2, h2) = lemma_conjunction_spine_step(tv, old_pos, old_acc, k, f);
                                assert(stop_until_release(tv, m2));
                                assert(until_release(tv, old_pos + 1, m2, h2));
                            }
                        }
                    },
                }
            }
            let r = Some((acc, pos));
            proof {
                assert(pos < ts.len() ==> tv[pos as int] == token_view(ts@[pos as int]));
                assert forall|k: int, f: SpecFormula| #[trigger] conjunction(tv, i as int, k, f)
                    && stop_conjunction(tv, k) implies returns(r, f, k) by {
                    lemma_conjunction_spine_le(tv, pos as int, view_f(acc), k, f);
                    if (pos as int) < k {
                        let (m2, h) = lemma_conjunction_spine_step(tv, pos as int, view_f(acc), k, f);
                    }
                }
            }
            r
        },
    }
}

// ---------------------------------------------------------------------------
// exclusive_or = conjunction { "^" conjunction }
// ---------------------------------------------------------------------------

/// Proof helper: `f`'s derivation as a exclusive_or over `[i, k]` passes through
/// position `j` with `acc` as its value over `[i, j]` (the left spine of the chain).
pub open spec fn spine_exclusive_or(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula) -> bool
    decreases k - j,
{
    (j == k && acc == f)
    || (j < k && xor_parts(f) is Some && exists|m: int| #![trigger tv[m]] j <= m < k && tv[m] is Xor
        && spine_exclusive_or(tv, j, acc, m, (xor_parts(f)->Some_0).0) && conjunction(tv, m + 1, k, (xor_parts(f)->Some_0).1))
}

proof fn lemma_exclusive_or_spine(tv: Seq<SpecToken>, i: int, k: int, f: SpecFormula) -> (r: (int, SpecFormula))
    requires
        exclusive_or(tv, i, k, f),
    ensures
        i < r.0 <= k,
        conjunction(tv, i, r.0, r.1),
        spine_exclusive_or(tv, r.0, r.1, k, f),
        r.0 == k || tv[r.0] is Xor,
    decreases k - i,
{
    if conjunction(tv, i, k, f) {
        (k, f)
    } else {
        let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Xor
            && exclusive_or(tv, i, m, (xor_parts(f)->Some_0).0) && conjunction(tv, m + 1, k, (xor_parts(f)->Some_0).1);
        let (j0, g0) = lemma_exclusive_or_spine(tv, i, m, (xor_parts(f)->Some_0).0);
        assert(spine_exclusive_or(tv, j0, g0, k, f));
        (j0, g0)
    }
}

proof fn lemma_exclusive_or_spine_step(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula)
    -> (r: (int, SpecFormula))
    requires
        spine_exclusive_or(tv, j, acc, k, f),
        j < k,
    ensures
        tv[j] is Xor,
        j + 1 < r.0 <= k,
        conjunction(tv, j + 1, r.0, r.1),
        r.0 == k || tv[r.0] is Xor,
        spine_exclusive_or(tv, r.0, xor_mltl(acc, r.1), k, f),
    decreases k - j,
{
    let m = choose|m: int| #![trigger tv[m]] j <= m < k && tv[m] is Xor
        && spine_exclusive_or(tv, j, acc, m, (xor_parts(f)->Some_0).0) && conjunction(tv, m + 1, k, (xor_parts(f)->Some_0).1);
    lemma_parts_inverse(f);
    if j == m {
        assert(acc == (xor_parts(f)->Some_0).0);
        assert(xor_mltl(acc, (xor_parts(f)->Some_0).1) == f);
        (k, (xor_parts(f)->Some_0).1)
    } else {
        let (m2, h) = lemma_exclusive_or_spine_step(tv, j, acc, m, (xor_parts(f)->Some_0).0);
        assert(spine_exclusive_or(tv, m2, xor_mltl(acc, h), k, f));
        (m2, h)
    }
}

proof fn lemma_exclusive_or_spine_le(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula)
    requires
        spine_exclusive_or(tv, j, acc, k, f),
    ensures
        j <= k,
        j == k ==> acc == f,
{
}

/// `exclusive_or` at token `i`.
fn p_exclusive_or(ts: &Vec<Token<Vec<u8>>>, i: usize, fail: &mut Fail) -> (r: Parsed)
    requires
        i <= ts.len(),
    ensures
        advances(r, i as int, ts.len() as int),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> exclusive_or(tokens_view(ts@), i as int, (r->Some_0).1 as int, view_f((r->Some_0).0)),
        forall|k: int, f: SpecFormula| #[trigger] exclusive_or(tokens_view(ts@), i as int, k, f)
            && stop_exclusive_or(tokens_view(ts@), k) ==> returns(r, f, k),
    decreases ts.len() - i, 4nat,
{
    let ghost tv = tokens_view(ts@);
    let first = p_conjunction(ts, i, fail);
    match first {
        None => {
            proof {
                assert forall|k: int, f: SpecFormula| #[trigger] exclusive_or(tv, i as int, k, f)
                    && stop_exclusive_or(tv, k) implies returns(None, f, k) by {
                    let (j0, g0) = lemma_exclusive_or_spine(tv, i as int, k, f);
                    assert(stop_conjunction(tv, j0));
                }
            }
            None
        },
        Some((g, j)) => {
            let mut acc = g;
            let mut pos = j;
            proof {
                assert forall|k: int, f: SpecFormula| #[trigger] exclusive_or(tv, i as int, k, f)
                    && stop_exclusive_or(tv, k) implies spine_exclusive_or(tv, pos as int, view_f(acc), k, f) by {
                    let (j0, g0) = lemma_exclusive_or_spine(tv, i as int, k, f);
                    assert(stop_conjunction(tv, j0));
                }
            }
            while pos < ts.len() && matches!(ts[pos], Token::Xor)
                invariant
                    i < pos <= ts.len(),
                    tv == tokens_view(ts@),
                    exclusive_or(tv, i as int, pos as int, view_f(acc)),
                    forall|k: int, f: SpecFormula| #[trigger] exclusive_or(tv, i as int, k, f)
                        && stop_exclusive_or(tv, k) ==> spine_exclusive_or(tv, pos as int, view_f(acc), k, f),
                decreases ts.len() - pos,
            {
                proof { assert(tv[pos as int] == token_view(ts@[pos as int])); }
                let next = p_conjunction(ts, pos + 1, fail);
                match next {
                    None => {
                        proof {
                            assert forall|k: int, f: SpecFormula| #[trigger] exclusive_or(tv, i as int, k, f)
                                && stop_exclusive_or(tv, k) implies returns(None, f, k) by {
                                lemma_exclusive_or_spine_le(tv, pos as int, view_f(acc), k, f);
                                if pos as int == k {
                                    assert(false);
                                }
                                let (m2, h) = lemma_exclusive_or_spine_step(tv, pos as int, view_f(acc), k, f);
                                assert(stop_conjunction(tv, m2));
                                assert(conjunction(tv, (pos + 1) as int, m2, h));
                            }
                        }
                        return None;
                    },
                    Some((h, k2)) => {
                        let ghost old_acc = view_f(acc);
                        let ghost old_pos = pos as int;
                        acc = exec_xor(acc, h);
                        pos = k2;
                        proof {
                            assert(view_f(acc) == xor_mltl(old_acc, view_f(h)));
                            lemma_parts_inverse(view_f(acc));
                            lemma_xor_parts(old_acc, view_f(h));
                            assert(exclusive_or(tv, i as int, pos as int, view_f(acc))) by {
                                assert(exclusive_or(tv, i as int, old_pos, old_acc));
                                assert(conjunction(tv, old_pos + 1, pos as int, view_f(h)));
                            }
                            assert forall|k: int, f: SpecFormula| #[trigger] exclusive_or(tv, i as int, k, f)
                                && stop_exclusive_or(tv, k) implies spine_exclusive_or(tv, pos as int, view_f(acc), k, f) by {
                                assert(spine_exclusive_or(tv, old_pos, old_acc, k, f));
                                lemma_exclusive_or_spine_le(tv, old_pos, old_acc, k, f);
                                if old_pos == k {
                                    assert(false);
                                }
                                let (m2, h2) = lemma_exclusive_or_spine_step(tv, old_pos, old_acc, k, f);
                                assert(stop_conjunction(tv, m2));
                                assert(conjunction(tv, old_pos + 1, m2, h2));
                            }
                        }
                    },
                }
            }
            let r = Some((acc, pos));
            proof {
                assert(pos < ts.len() ==> tv[pos as int] == token_view(ts@[pos as int]));
                assert forall|k: int, f: SpecFormula| #[trigger] exclusive_or(tv, i as int, k, f)
                    && stop_exclusive_or(tv, k) implies returns(r, f, k) by {
                    lemma_exclusive_or_spine_le(tv, pos as int, view_f(acc), k, f);
                    if (pos as int) < k {
                        let (m2, h) = lemma_exclusive_or_spine_step(tv, pos as int, view_f(acc), k, f);
                    }
                }
            }
            r
        },
    }
}

// ---------------------------------------------------------------------------
// disjunction = exclusive_or { "|" exclusive_or }
// ---------------------------------------------------------------------------

/// Proof helper: `f`'s derivation as a disjunction over `[i, k]` passes through
/// position `j` with `acc` as its value over `[i, j]` (the left spine of the chain).
pub open spec fn spine_disjunction(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula) -> bool
    decreases k - j,
{
    (j == k && acc == f)
    || (j < k && f is Or && exists|m: int| #![trigger tv[m]] j <= m < k && tv[m] is Or
        && spine_disjunction(tv, j, acc, m, *(f->Or_0)) && exclusive_or(tv, m + 1, k, *(f->Or_1)))
}

proof fn lemma_disjunction_spine(tv: Seq<SpecToken>, i: int, k: int, f: SpecFormula) -> (r: (int, SpecFormula))
    requires
        disjunction(tv, i, k, f),
    ensures
        i < r.0 <= k,
        exclusive_or(tv, i, r.0, r.1),
        spine_disjunction(tv, r.0, r.1, k, f),
        r.0 == k || tv[r.0] is Or,
    decreases k - i,
{
    if exclusive_or(tv, i, k, f) {
        (k, f)
    } else {
        let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Or
            && disjunction(tv, i, m, *(f->Or_0)) && exclusive_or(tv, m + 1, k, *(f->Or_1));
        let (j0, g0) = lemma_disjunction_spine(tv, i, m, *(f->Or_0));
        assert(spine_disjunction(tv, j0, g0, k, f));
        (j0, g0)
    }
}

proof fn lemma_disjunction_spine_step(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula)
    -> (r: (int, SpecFormula))
    requires
        spine_disjunction(tv, j, acc, k, f),
        j < k,
    ensures
        tv[j] is Or,
        j + 1 < r.0 <= k,
        exclusive_or(tv, j + 1, r.0, r.1),
        r.0 == k || tv[r.0] is Or,
        spine_disjunction(tv, r.0, Mltl::Or(Box::new(acc), Box::new(r.1)), k, f),
    decreases k - j,
{
    let m = choose|m: int| #![trigger tv[m]] j <= m < k && tv[m] is Or
        && spine_disjunction(tv, j, acc, m, *(f->Or_0)) && exclusive_or(tv, m + 1, k, *(f->Or_1));
    lemma_parts_inverse(f);
    if j == m {
        assert(acc == *(f->Or_0));
        assert(Mltl::Or(Box::new(acc), Box::new(*(f->Or_1))) == f);
        (k, *(f->Or_1))
    } else {
        let (m2, h) = lemma_disjunction_spine_step(tv, j, acc, m, *(f->Or_0));
        assert(spine_disjunction(tv, m2, Mltl::Or(Box::new(acc), Box::new(h)), k, f));
        (m2, h)
    }
}

proof fn lemma_disjunction_spine_le(tv: Seq<SpecToken>, j: int, acc: SpecFormula, k: int, f: SpecFormula)
    requires
        spine_disjunction(tv, j, acc, k, f),
    ensures
        j <= k,
        j == k ==> acc == f,
{
}

/// `disjunction` at token `i`.
fn p_disjunction(ts: &Vec<Token<Vec<u8>>>, i: usize, fail: &mut Fail) -> (r: Parsed)
    requires
        i <= ts.len(),
    ensures
        advances(r, i as int, ts.len() as int),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> disjunction(tokens_view(ts@), i as int, (r->Some_0).1 as int, view_f((r->Some_0).0)),
        forall|k: int, f: SpecFormula| #[trigger] disjunction(tokens_view(ts@), i as int, k, f)
            && stop_disjunction(tokens_view(ts@), k) ==> returns(r, f, k),
    decreases ts.len() - i, 5nat,
{
    let ghost tv = tokens_view(ts@);
    let first = p_exclusive_or(ts, i, fail);
    match first {
        None => {
            proof {
                assert forall|k: int, f: SpecFormula| #[trigger] disjunction(tv, i as int, k, f)
                    && stop_disjunction(tv, k) implies returns(None, f, k) by {
                    let (j0, g0) = lemma_disjunction_spine(tv, i as int, k, f);
                    assert(stop_exclusive_or(tv, j0));
                }
            }
            None
        },
        Some((g, j)) => {
            let mut acc = g;
            let mut pos = j;
            proof {
                assert forall|k: int, f: SpecFormula| #[trigger] disjunction(tv, i as int, k, f)
                    && stop_disjunction(tv, k) implies spine_disjunction(tv, pos as int, view_f(acc), k, f) by {
                    let (j0, g0) = lemma_disjunction_spine(tv, i as int, k, f);
                    assert(stop_exclusive_or(tv, j0));
                }
            }
            while pos < ts.len() && matches!(ts[pos], Token::Or)
                invariant
                    i < pos <= ts.len(),
                    tv == tokens_view(ts@),
                    disjunction(tv, i as int, pos as int, view_f(acc)),
                    forall|k: int, f: SpecFormula| #[trigger] disjunction(tv, i as int, k, f)
                        && stop_disjunction(tv, k) ==> spine_disjunction(tv, pos as int, view_f(acc), k, f),
                decreases ts.len() - pos,
            {
                proof { assert(tv[pos as int] == token_view(ts@[pos as int])); }
                let next = p_exclusive_or(ts, pos + 1, fail);
                match next {
                    None => {
                        proof {
                            assert forall|k: int, f: SpecFormula| #[trigger] disjunction(tv, i as int, k, f)
                                && stop_disjunction(tv, k) implies returns(None, f, k) by {
                                lemma_disjunction_spine_le(tv, pos as int, view_f(acc), k, f);
                                if pos as int == k {
                                    assert(false);
                                }
                                let (m2, h) = lemma_disjunction_spine_step(tv, pos as int, view_f(acc), k, f);
                                assert(stop_exclusive_or(tv, m2));
                                assert(exclusive_or(tv, (pos + 1) as int, m2, h));
                            }
                        }
                        return None;
                    },
                    Some((h, k2)) => {
                        let ghost old_acc = view_f(acc);
                        let ghost old_pos = pos as int;
                        acc = Mltl::Or(Box::new(acc), Box::new(h));
                        pos = k2;
                        proof {
                            assert(view_f(acc) == Mltl::Or(Box::new(old_acc), Box::new(view_f(h))));
                            lemma_parts_inverse(view_f(acc));
                            
                            assert(disjunction(tv, i as int, pos as int, view_f(acc))) by {
                                assert(disjunction(tv, i as int, old_pos, old_acc));
                                assert(exclusive_or(tv, old_pos + 1, pos as int, view_f(h)));
                            }
                            assert forall|k: int, f: SpecFormula| #[trigger] disjunction(tv, i as int, k, f)
                                && stop_disjunction(tv, k) implies spine_disjunction(tv, pos as int, view_f(acc), k, f) by {
                                assert(spine_disjunction(tv, old_pos, old_acc, k, f));
                                lemma_disjunction_spine_le(tv, old_pos, old_acc, k, f);
                                if old_pos == k {
                                    assert(false);
                                }
                                let (m2, h2) = lemma_disjunction_spine_step(tv, old_pos, old_acc, k, f);
                                assert(stop_exclusive_or(tv, m2));
                                assert(exclusive_or(tv, old_pos + 1, m2, h2));
                            }
                        }
                    },
                }
            }
            let r = Some((acc, pos));
            proof {
                assert(pos < ts.len() ==> tv[pos as int] == token_view(ts@[pos as int]));
                assert forall|k: int, f: SpecFormula| #[trigger] disjunction(tv, i as int, k, f)
                    && stop_disjunction(tv, k) implies returns(r, f, k) by {
                    lemma_disjunction_spine_le(tv, pos as int, view_f(acc), k, f);
                    if (pos as int) < k {
                        let (m2, h) = lemma_disjunction_spine_step(tv, pos as int, view_f(acc), k, f);
                    }
                }
            }
            r
        },
    }
}

/// `implication` at token `i`.
fn p_implication(ts: &Vec<Token<Vec<u8>>>, i: usize, fail: &mut Fail) -> (r: Parsed)
    requires
        i <= ts.len(),
    ensures
        advances(r, i as int, ts.len() as int),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> implication(tokens_view(ts@), i as int, (r->Some_0).1 as int, view_f((r->Some_0).0)),
        forall|k: int, f: SpecFormula| #[trigger] implication(tokens_view(ts@), i as int, k, f)
            && stop_implication(tokens_view(ts@), k) ==> returns(r, f, k),
    decreases ts.len() - i, 6nat,
{
    reveal_with_fuel(view_f, 3);
    let ghost tv = tokens_view(ts@);
    let first = p_disjunction(ts, i, fail);
    match first {
        None => {
            proof {
                assert forall|k: int, f: SpecFormula| #[trigger] implication(tv, i as int, k, f)
                    && stop_implication(tv, k) implies returns(None, f, k) by {
                    if !disjunction(tv, i as int, k, f) {
                        if implies_parts(f) is Some && exists|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Implies
                            && disjunction(tv, i as int, m, (implies_parts(f)->Some_0).0)
                            && disjunction(tv, m + 1, k, (implies_parts(f)->Some_0).1) {
                            let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Implies
                                && disjunction(tv, i as int, m, (implies_parts(f)->Some_0).0)
                                && disjunction(tv, m + 1, k, (implies_parts(f)->Some_0).1);
                            assert(stop_disjunction(tv, m));
                        } else {
                            let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Iff
                                && disjunction(tv, i as int, m, (iff_parts(f)->Some_0).0)
                                && disjunction(tv, m + 1, k, (iff_parts(f)->Some_0).1);
                            assert(stop_disjunction(tv, m));
                        }
                    }
                }
            }
            None
        },
        Some((g1, j)) => {
            if j < ts.len() && (matches!(ts[j], Token::Implies) || matches!(ts[j], Token::Iff)) {
                proof { assert(tv[j as int] == token_view(ts@[j as int])); }
                let is_imp = matches!(ts[j], Token::Implies);
                let sub = p_disjunction(ts, j + 1, fail);
                let r = match sub {
                    Some((g2, k2)) => {
                        let f = if is_imp { Mltl::Or(Box::new(Mltl::Not(Box::new(g1))), Box::new(g2)) }
                                else { exec_iff(g1, g2) };
                        Some((f, k2))
                    },
                    None => None,
                };
                proof {
                    if r is Some {
                        let k2 = (r->Some_0).1 as int;
                        let f = view_f((r->Some_0).0);
                        let (l, rr) = (view_f(g1), view_f((sub->Some_0).0));
                        if is_imp {
                            assert(f == implies_mltl(l, rr));
                            lemma_implies_parts(l, rr);
                            assert(i < j && j < k2 && tv[j as int] is Implies
                                && disjunction(tv, i as int, j as int, (implies_parts(f)->Some_0).0)
                                && disjunction(tv, j + 1, k2, (implies_parts(f)->Some_0).1));
                        } else {
                            lemma_iff_parts(l, rr);
                            assert(i < j && j < k2 && tv[j as int] is Iff
                                && disjunction(tv, i as int, j as int, (iff_parts(f)->Some_0).0)
                                && disjunction(tv, j + 1, k2, (iff_parts(f)->Some_0).1));
                        }
                    }
                    assert forall|k: int, f: SpecFormula| #[trigger] implication(tv, i as int, k, f)
                        && stop_implication(tv, k) implies returns(r, f, k) by {
                        lemma_parts_inverse(f);
                        if disjunction(tv, i as int, k, f) {
                            assert(k == j);
                        } else if implies_parts(f) is Some && exists|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Implies
                            && disjunction(tv, i as int, m, (implies_parts(f)->Some_0).0)
                            && disjunction(tv, m + 1, k, (implies_parts(f)->Some_0).1) {
                            let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Implies
                                && disjunction(tv, i as int, m, (implies_parts(f)->Some_0).0)
                                && disjunction(tv, m + 1, k, (implies_parts(f)->Some_0).1);
                            assert(stop_disjunction(tv, m));
                            assert(m == j);
                            assert(disjunction(tv, (j + 1) as int, k, (implies_parts(f)->Some_0).1));
                        } else {
                            let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Iff
                                && disjunction(tv, i as int, m, (iff_parts(f)->Some_0).0)
                                && disjunction(tv, m + 1, k, (iff_parts(f)->Some_0).1);
                            assert(stop_disjunction(tv, m));
                            assert(m == j);
                            assert(disjunction(tv, (j + 1) as int, k, (iff_parts(f)->Some_0).1));
                        }
                    }
                }
                r
            } else {
                let r = Some((g1, j));
                proof {
                    assert(j < ts.len() ==> tv[j as int] == token_view(ts@[j as int]));
                    assert forall|k: int, f: SpecFormula| #[trigger] implication(tv, i as int, k, f)
                        && stop_implication(tv, k) implies returns(r, f, k) by {
                        if !disjunction(tv, i as int, k, f) {
                            if implies_parts(f) is Some && exists|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Implies
                                && disjunction(tv, i as int, m, (implies_parts(f)->Some_0).0)
                                && disjunction(tv, m + 1, k, (implies_parts(f)->Some_0).1) {
                                let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Implies
                                    && disjunction(tv, i as int, m, (implies_parts(f)->Some_0).0)
                                    && disjunction(tv, m + 1, k, (implies_parts(f)->Some_0).1);
                                assert(stop_disjunction(tv, m));
                            } else {
                                let m = choose|m: int| #![trigger tv[m]] i < m && m < k && tv[m] is Iff
                                    && disjunction(tv, i as int, m, (iff_parts(f)->Some_0).0)
                                    && disjunction(tv, m + 1, k, (iff_parts(f)->Some_0).1);
                                assert(stop_disjunction(tv, m));
                            }
                        }
                    }
                }
                r
            }
        },
    }
}

/// `formula` at token `i`.
fn p_formula(ts: &Vec<Token<Vec<u8>>>, i: usize, fail: &mut Fail) -> (r: Parsed)
    requires
        i <= ts.len(),
    ensures
        advances(r, i as int, ts.len() as int),
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> formula(tokens_view(ts@), i as int, (r->Some_0).1 as int, view_f((r->Some_0).0)),
        forall|k: int, f: SpecFormula| #[trigger] formula(tokens_view(ts@), i as int, k, f)
            && stop_implication(tokens_view(ts@), k) ==> returns(r, f, k),
    decreases ts.len() - i, 7nat,
{
    let r = p_implication(ts, i, fail);
    proof {
        let tv = tokens_view(ts@);
        assert forall|k: int, f: SpecFormula| #[trigger] formula(tv, i as int, k, f)
            && stop_implication(tv, k) implies returns(r, f, k) by {
            assert(implication(tv, i as int, k, f));
        }
    }
    r
}

/// The whole token sequence as one formula: the unique formula it denotes,
/// or `None` if there is none (then `fail` says where the parser stopped).
pub fn parse_tokens(ts: &Vec<Token<Vec<u8>>>, fail: &mut Fail) -> (r: Option<ExecFormula>)
    ensures
        r is None ==> fail_ok(*final(fail), ts.len() as nat),
        r is Some ==> formula(tokens_view(ts@), 0, ts.len() as int, view_f(r->Some_0)),
        forall|f: SpecFormula| #[trigger] formula(tokens_view(ts@), 0, ts.len() as int, f)
            ==> r is Some && view_f(r->Some_0) == f,
{
    let res = p_formula(ts, 0, fail);
    let ghost tv = tokens_view(ts@);
    match res {
        Some((f, j)) => {
            if j == ts.len() {
                Some(f)
            } else {
                proof {
                    assert forall|g: SpecFormula| #[trigger] formula(tv, 0, ts.len() as int, g) implies false by {
                        assert(stop_implication(tv, ts.len() as int));
                    }
                }
                *fail = Fail { at: j, expected: Expected::End, related: j };
                None
            }
        },
        None => {
            proof {
                assert forall|g: SpecFormula| #[trigger] formula(tv, 0, ts.len() as int, g) implies false by {
                    assert(stop_implication(tv, ts.len() as int));
                }
            }
            None
        },
    }
}

} // verus!
