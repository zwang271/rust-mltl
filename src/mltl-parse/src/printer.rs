//! The printer: formulas back to text, with as few parentheses as the
//! grammar's levels allow, proved to parse back to the same formula.
//!
//! Layer 1 (this part): formulas to tokens (`print_tokens`), and the proof
//! that the grammar reads those tokens as the original formula.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::lexer::*;
use crate::grammar::*;
use crate::parser::*;

verus! {

/// The grammar level of a formula's outermost operator (GRAMMAR.md §3):
/// 1 atom, 2 unary, 3 until/release, 4 conjunction, 6 disjunction.
pub open spec fn level(f: SpecFormula) -> nat {
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(_) | Mltl::Future(_, _, _) | Mltl::Global(_, _, _) => 2,
        Mltl::Until(_, _, _, _) | Mltl::Release(_, _, _, _) => 3,
        Mltl::And(_, _) => 4,
        Mltl::Or(_, _) => 6,
    }
}

pub open spec fn interval_tokens(a: usize, b: usize) -> Seq<SpecToken> {
    seq![Token::LBrack, Token::Num(a), Token::Comma, Token::Num(b), Token::RBrack]
}

/// Tokens of `f` where a piece of level `l` is expected: parenthesised only
/// if `f`'s own level is looser than `l`.
pub open spec fn tokens_at(f: SpecFormula, l: nat) -> Seq<SpecToken>
    decreases f, 1nat,
{
    if level(f) <= l { raw_tokens(f) } else { seq![Token::LParen] + raw_tokens(f) + seq![Token::RParen] }
}

/// Tokens of `f` without outer parentheses. Operands are printed at the
/// levels the grammar requires: `a & b` needs a conjunction on the left and
/// an until/release on the right, so `(p & q) & r` prints as `p & q & r` but
/// `p & (q & r)` keeps its parentheses.
pub open spec fn raw_tokens(f: SpecFormula) -> Seq<SpecToken>
    decreases f, 0nat,
{
    match f {
        Mltl::True => seq![Token::True],
        Mltl::False => seq![Token::False],
        Mltl::Prop(n) => seq![Token::Name(n)],
        Mltl::Not(g) => seq![Token::Not] + tokens_at(*g, 2),
        Mltl::Future(a, b, g) => seq![Token::KwF] + interval_tokens(a, b) + tokens_at(*g, 2),
        Mltl::Global(a, b, g) => seq![Token::KwG] + interval_tokens(a, b) + tokens_at(*g, 2),
        Mltl::Until(g, a, b, h) => tokens_at(*g, 2) + seq![Token::KwU] + interval_tokens(a, b) + tokens_at(*h, 2),
        Mltl::Release(g, a, b, h) => tokens_at(*g, 2) + seq![Token::KwR] + interval_tokens(a, b) + tokens_at(*h, 2),
        Mltl::And(g, h) => tokens_at(*g, 4) + seq![Token::And] + tokens_at(*h, 3),
        Mltl::Or(g, h) => tokens_at(*g, 6) + seq![Token::Or] + tokens_at(*h, 5),
    }
}

/// The tokens of a whole formula.
pub open spec fn print_tokens(f: SpecFormula) -> Seq<SpecToken> {
    tokens_at(f, 7)
}

/// A name the lexer reads back as that name: non-empty, starts with a
/// letter or `_`, continues with letters, digits, `_`, and is not a keyword.
pub open spec fn valid_name(n: Seq<u8>) -> bool {
    &&& n.len() > 0
    &&& is_word_start(n[0])
    &&& forall|k: int| 0 <= k < n.len() ==> is_word_char(#[trigger] n[k])
    &&& keyword(n) is None
}

/// Every atom of `f` is a valid name.
pub open spec fn valid_names(f: SpecFormula) -> bool
    decreases f,
{
    match f {
        Mltl::True | Mltl::False => true,
        Mltl::Prop(n) => valid_name(n),
        Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => valid_names(*g),
        Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) =>
            valid_names(*g) && valid_names(*h),
    }
}

/// The formulas the printer handles: every interval well-formed (the parser
/// rejects `a > b`) and every atom a valid name.
pub open spec fn printable(f: SpecFormula) -> bool {
    intervals_welldef(f) && valid_names(f)
}

/// The grammar rule of level `l` (1 atom .. 7 formula; 5 is exclusive_or).
pub open spec fn rule(l: nat, ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula) -> bool {
    if l <= 1 { atom(ts, lo, hi, f) }
    else if l == 2 { unary(ts, lo, hi, f) }
    else if l == 3 { until_release(ts, lo, hi, f) }
    else if l == 4 { conjunction(ts, lo, hi, f) }
    else if l == 5 { exclusive_or(ts, lo, hi, f) }
    else if l == 6 { disjunction(ts, lo, hi, f) }
    else { formula(ts, lo, hi, f) }
}

/// A piece of a tighter level is also a piece of every looser level.
proof fn lemma_lift(l1: nat, l2: nat, ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula)
    requires
        1 <= l1 <= l2 <= 7,
        rule(l1, ts, lo, hi, f),
    ensures
        rule(l2, ts, lo, hi, f),
    decreases l2 - l1,
{
    if l1 < l2 {
        let l = (l1 + 1) as nat;
        if l1 == 1 { assert(unary(ts, lo, hi, f)); }
        else if l1 == 2 { assert(until_release(ts, lo, hi, f)); }
        else if l1 == 3 { assert(conjunction(ts, lo, hi, f)); }
        else if l1 == 4 { assert(exclusive_or(ts, lo, hi, f)); }
        else if l1 == 5 { assert(disjunction(ts, lo, hi, f)); }
        else { assert(implication(ts, lo, hi, f)); assert(formula(ts, lo, hi, f)); }
        lemma_lift(l, l2, ts, lo, hi, f);
    }
}

/// `ts[lo..lo + |x ++ y|] == x ++ y` splits into its two parts.
proof fn lemma_split(ts: Seq<SpecToken>, lo: int, x: Seq<SpecToken>, y: Seq<SpecToken>)
    requires
        0 <= lo,
        lo + x.len() + y.len() <= ts.len(),
        ts.subrange(lo, lo + x.len() + y.len()) == x + y,
    ensures
        ts.subrange(lo, lo + x.len()) == x,
        ts.subrange(lo + x.len(), lo + x.len() + y.len()) == y,
{
    assert(ts.subrange(lo, lo + x.len()) =~= (x + y).subrange(0, x.len() as int));
    assert(ts.subrange(lo + x.len(), lo + x.len() + y.len()) =~= (x + y).subrange(x.len() as int, (x.len() + y.len()) as int));
}

/// Tokens printed at level `l` are read by the grammar's level-`l` rule as `f`.
proof fn lemma_tokens_at(ts: Seq<SpecToken>, lo: int, f: SpecFormula, l: nat)
    requires
        printable(f),
        2 <= l <= 7,
        0 <= lo,
        lo + tokens_at(f, l).len() <= ts.len(),
        ts.subrange(lo, lo + tokens_at(f, l).len()) == tokens_at(f, l),
    ensures
        rule(l, ts, lo, lo + tokens_at(f, l).len(), f),
    decreases f, 1nat,
{
    let r = raw_tokens(f);
    if level(f) <= l {
        lemma_raw_tokens(ts, lo, f);
        lemma_lift(level(f), l, ts, lo, lo + r.len(), f);
    } else {
        let hi = lo + r.len() + 2;
        lemma_split(ts, lo, seq![Token::LParen] + r, seq![Token::RParen]);
        lemma_split(ts, lo, seq![Token::LParen], r);
        assert(ts[lo] == (seq![Token::LParen] + r)[0]);
        assert(ts[hi - 1] == seq![Token::<Seq<u8>>::RParen][0]) by {
            assert(ts.subrange(lo + r.len() + 1, hi)[0] == ts[hi - 1]);
        }
        lemma_raw_tokens(ts, lo + 1, f);
        lemma_lift(level(f), 7, ts, lo + 1, lo + 1 + r.len(), f);
        assert(atom(ts, lo, hi, f));
        lemma_lift(1, l, ts, lo, hi, f);
    }
}

proof fn lemma_interval_tokens(ts: Seq<SpecToken>, k: int, a: usize, b: usize)
    requires
        0 <= k, k + 5 <= ts.len(),
        ts.subrange(k, k + 5) == interval_tokens(a, b),
        a <= b,
    ensures
        interval(ts, k, a, b),
{
    assert(ts[k] == ts.subrange(k, k + 5)[0]);
    assert(ts[k + 1] == ts.subrange(k, k + 5)[1]);
    assert(ts[k + 2] == ts.subrange(k, k + 5)[2]);
    assert(ts[k + 3] == ts.subrange(k, k + 5)[3]);
    assert(ts[k + 4] == ts.subrange(k, k + 5)[4]);
}

/// Unparenthesised tokens of `f` are read as `f` at `f`'s own level.
proof fn lemma_raw_tokens(ts: Seq<SpecToken>, lo: int, f: SpecFormula)
    requires
        printable(f),
        0 <= lo,
        lo + raw_tokens(f).len() <= ts.len(),
        ts.subrange(lo, lo + raw_tokens(f).len()) == raw_tokens(f),
    ensures
        rule(level(f), ts, lo, lo + raw_tokens(f).len(), f),
    decreases f, 0nat,
{
    let r = raw_tokens(f);
    let hi = lo + r.len();
    assert(ts[lo] == ts.subrange(lo, hi)[0]);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => {
            let x = seq![Token::<Seq<u8>>::Not];
            lemma_split(ts, lo, x, tokens_at(*g, 2));
            lemma_tokens_at(ts, lo + 1, *g, 2);
        },
        Mltl::Future(a, b, g) | Mltl::Global(a, b, g) => {
            let kw = if f is Future { seq![Token::<Seq<u8>>::KwF] } else { seq![Token::<Seq<u8>>::KwG] };
            assert(r == kw + interval_tokens(a, b) + tokens_at(*g, 2));
            lemma_split(ts, lo, kw + interval_tokens(a, b), tokens_at(*g, 2));
            lemma_split(ts, lo, kw, interval_tokens(a, b));
            lemma_interval_tokens(ts, lo + 1, a, b);
            lemma_tokens_at(ts, lo + 6, *g, 2);
        },
        Mltl::Until(g, a, b, h) | Mltl::Release(g, a, b, h) => {
            let kw = if f is Until { seq![Token::<Seq<u8>>::KwU] } else { seq![Token::<Seq<u8>>::KwR] };
            let pg = tokens_at(*g, 2);
            let m = lo + pg.len();
            assert(r == pg + kw + interval_tokens(a, b) + tokens_at(*h, 2));
            lemma_split(ts, lo, pg + kw + interval_tokens(a, b), tokens_at(*h, 2));
            lemma_split(ts, lo, pg + kw, interval_tokens(a, b));
            lemma_split(ts, lo, pg, kw);
            assert(ts[m] == ts.subrange(m, m + 1)[0]);
            lemma_interval_tokens(ts, m + 1, a, b);
            lemma_tokens_at(ts, lo, *g, 2);
            lemma_tokens_at(ts, m + 6, *h, 2);
            assert(tv_until_release_witness(ts, lo, hi, f, m));
        },
        Mltl::And(g, h) | Mltl::Or(g, h) => {
            let (lg, lh) = if f is And { (4nat, 3nat) } else { (6nat, 5nat) };
            let op = if f is And { seq![Token::<Seq<u8>>::And] } else { seq![Token::<Seq<u8>>::Or] };
            let pg = tokens_at(*g, lg);
            let m = lo + pg.len();
            assert(r == pg + op + tokens_at(*h, lh));
            lemma_split(ts, lo, pg + op, tokens_at(*h, lh));
            lemma_split(ts, lo, pg, op);
            assert(ts[m] == ts.subrange(m, m + 1)[0]);
            lemma_tokens_at(ts, lo, *g, lg);
            lemma_tokens_at(ts, m + 1, *h, lh);
            if f is And {
                assert(lo < m && m < hi && ts[m] is And
                    && conjunction(ts, lo, m, *(f->And_0)) && until_release(ts, m + 1, hi, *(f->And_1)));
            } else {
                assert(lo < m && m < hi && ts[m] is Or
                    && disjunction(ts, lo, m, *(f->Or_0)) && exclusive_or(ts, m + 1, hi, *(f->Or_1)));
            }
        },
    }
}

/// The until/release witness at `m` (a named form of the existential's body).
pub open spec fn tv_until_release_witness(ts: Seq<SpecToken>, lo: int, hi: int, f: SpecFormula, m: int) -> bool {
    if f is Until {
        lo < m && m + 6 <= hi && ts[m] is KwU && interval(ts, m + 1, f->Until_1, f->Until_2)
            && unary(ts, lo, m, *(f->Until_0)) && unary(ts, m + 6, hi, *(f->Until_3))
    } else {
        lo < m && m + 6 <= hi && ts[m] is KwR && interval(ts, m + 1, f->Release_1, f->Release_2)
            && unary(ts, lo, m, *(f->Release_0)) && unary(ts, m + 6, hi, *(f->Release_3))
    }
}

/// Round trip at the token level: the grammar reads `print_tokens(f)` as `f`.
pub proof fn lemma_print_tokens(f: SpecFormula)
    requires
        printable(f),
    ensures
        formula(print_tokens(f), 0, print_tokens(f).len() as int, f),
{
    let ts = print_tokens(f);
    assert(ts.subrange(0, ts.len() as int) =~= ts);
    lemma_tokens_at(ts, 0, f, 7);
}


// ---------------------------------------------------------------------------
// Layer 2: tokens to text, and the lexer reads the text back as the tokens.
// ---------------------------------------------------------------------------

/// Decimal digits of `v`.
pub open spec fn digits(v: nat) -> Seq<u8>
    decreases v,
{
    if v < 10 { seq![(48 + v) as u8] } else { digits(v / 10) + seq![(48 + v % 10) as u8] }
}

/// The text of one token.
pub open spec fn token_text(t: SpecToken) -> Seq<u8> {
    match t {
        Token::Name(n) => n,
        Token::Num(v) => digits(v as nat),
        Token::True => seq![116u8, 114, 117, 101],
        Token::False => seq![102u8, 97, 108, 115, 101],
        Token::KwF => seq![70u8],
        Token::KwG => seq![71u8],
        Token::KwU => seq![85u8],
        Token::KwR => seq![82u8],
        Token::LParen => seq![40u8],
        Token::RParen => seq![41u8],
        Token::LBrack => seq![91u8],
        Token::RBrack => seq![93u8],
        Token::Comma => seq![44u8],
        Token::Not => seq![33u8],
        Token::And => seq![38u8],
        Token::Or => seq![124u8],
        Token::Xor => seq![94u8],
        Token::Implies => seq![45u8, 62],
        Token::Iff => seq![60u8, 45, 62],
    }
}

/// No space between `t1` and `t2`: after `(`, `[`, `,`, `!` and before `)`,
/// `]`, `,`, `[`. Everywhere else one space. So `F[0,3] p`, `!(p & q)`.
pub open spec fn glue(t1: SpecToken, t2: SpecToken) -> bool {
    t1 is LParen || t1 is LBrack || t1 is Comma || t1 is Not
        || t2 is RParen || t2 is RBrack || t2 is Comma || t2 is LBrack
}

pub open spec fn separator(t1: SpecToken, t2: SpecToken) -> Seq<u8> {
    if glue(t1, t2) { Seq::empty() } else { seq![32u8] }
}

/// The text of a token sequence.
pub open spec fn render(ts: Seq<SpecToken>) -> Seq<u8>
    decreases ts.len(),
{
    if ts.len() == 0 {
        Seq::empty()
    } else if ts.len() == 1 {
        token_text(ts[0])
    } else {
        render(ts.drop_last()) + separator(ts[ts.len() - 2], ts[ts.len() - 1]) + token_text(ts.last())
    }
}

/// The printed text of a formula.
pub open spec fn print_text(f: SpecFormula) -> Seq<u8> {
    render(print_tokens(f))
}

pub open spec fn valid_token(t: SpecToken) -> bool {
    t is Name ==> valid_name(t->Name_0)
}

pub open spec fn valid_tokens(ts: Seq<SpecToken>) -> bool {
    forall|k: int| 0 <= k < ts.len() ==> valid_token(#[trigger] ts[k])
}

/// `render` read from the front: first token, separator, the rest.
proof fn lemma_render_head(ts: Seq<SpecToken>)
    requires
        ts.len() >= 2,
    ensures
        render(ts) == token_text(ts[0]) + separator(ts[0], ts[1]) + render(ts.drop_first()),
    decreases ts.len(),
{
    if ts.len() > 2 {
        let d = ts.drop_last();
        lemma_render_head(d);
        assert(d[0] == ts[0] && d[1] == ts[1]);
        assert(d.drop_first() =~= ts.drop_first().drop_last());
        let r = ts.drop_first();
        assert(render(r) == render(r.drop_last()) + separator(r[r.len() - 2], r[r.len() - 1]) + token_text(r.last()));
        assert(r[r.len() - 2] == ts[ts.len() - 2] && r[r.len() - 1] == ts[ts.len() - 1] && r.last() == ts.last());
        assert(render(ts) == render(d) + separator(ts[ts.len() - 2], ts[ts.len() - 1]) + token_text(ts.last()));
        let sep = separator(ts[ts.len() - 2], ts[ts.len() - 1]);
        assert(render(d) == token_text(ts[0]) + separator(ts[0], ts[1]) + render(r.drop_last()));
        assert((token_text(ts[0]) + separator(ts[0], ts[1]) + render(r.drop_last())) + sep + token_text(ts.last())
            =~= token_text(ts[0]) + separator(ts[0], ts[1]) + (render(r.drop_last()) + sep + token_text(ts.last())));
        assert(render(r) == render(r.drop_last()) + sep + token_text(ts.last()));
        assert(render(ts) == token_text(ts[0]) + separator(ts[0], ts[1]) + render(r));
    } else {
        assert(ts.drop_last() =~= seq![ts[0]]);
        assert(ts.drop_first() =~= seq![ts[1]]);
        assert(render(seq![ts[0]]) == token_text(ts[0]));
        assert(render(seq![ts[1]]) == token_text(ts[1]));
        assert(render(ts) == render(ts.drop_last()) + separator(ts[0], ts[1]) + token_text(ts.last()));
    }
}

proof fn lemma_word_end_run(s: Seq<u8>, i: nat, e: nat)
    requires
        i <= e <= s.len(),
        forall|k: int| i <= k < e ==> is_word_char(#[trigger] s[k]),
        e == s.len() || !is_word_char(s[e as int]),
    ensures
        word_end(s, i) == e,
    decreases e - i,
{
    if i < e { lemma_word_end_run(s, i + 1, e); }
}

proof fn lemma_digits_end_run(s: Seq<u8>, i: nat, e: nat)
    requires
        i <= e <= s.len(),
        forall|k: int| i <= k < e ==> is_digit(#[trigger] s[k]),
        e == s.len() || !is_digit(s[e as int]),
    ensures
        digits_end(s, i) == e,
    decreases e - i,
{
    if i < e { lemma_digits_end_run(s, i + 1, e); }
}

pub proof fn lemma_digits(v: nat)
    ensures
        digits(v).len() >= 1,
        forall|k: int| 0 <= k < digits(v).len() ==> is_digit(#[trigger] digits(v)[k]),
    decreases v,
{
    if v >= 10 {
        lemma_digits(v / 10);
        assert forall|k: int| 0 <= k < digits(v).len() implies is_digit(#[trigger] digits(v)[k]) by {
            if k < digits(v / 10).len() { assert(digits(v)[k] == digits(v / 10)[k]); }
        }
    }
}

/// The lexer's value of the digits of `v`, wherever they appear, is `v`.
pub(crate) proof fn lemma_digits_value(s: Seq<u8>, i: nat, v: nat)
    requires
        i + digits(v).len() <= s.len(),
        s.subrange(i as int, (i + digits(v).len()) as int) == digits(v),
    ensures
        digits_value(s, i, i + digits(v).len()) == v,
    decreases v,
{
    let n = digits(v).len();
    lemma_digits(v);
    if v < 10 {
        assert(s[i as int] == s.subrange(i as int, (i + n) as int)[0]);
        assert(digits_value(s, i, i) == 0);
    } else {
        let d = digits(v / 10);
        lemma_digits(v / 10);
        assert(digits(v).subrange(0, d.len() as int) =~= d);
        assert(s.subrange(i as int, (i + d.len()) as int) =~= digits(v).subrange(0, d.len() as int));
        lemma_digits_value(s, i, v / 10);
        assert(s[(i + n - 1) as int] == s.subrange(i as int, (i + n) as int)[n - 1]);
        assert(v == (v / 10) * 10 + v % 10) by (nonlinear_arith);
    }
}

/// The token's text ends at a character that cannot continue it.
pub open spec fn boundary_ok(s: Seq<u8>, e: nat) -> bool {
    e == s.len() || !(is_word_char(s[e as int]) || is_digit(s[e as int]))
}

/// After the text of `t` starting at `i`, the lexer emits `t` and continues
/// right after the text.
proof fn lemma_lex_token(s: Seq<u8>, i: nat, t: SpecToken)
    requires
        valid_token(t),
        i + token_text(t).len() <= s.len(),
        s.subrange(i as int, (i + token_text(t).len()) as int) == token_text(t),
        (t is Name || t is Num || t is True || t is False || t is KwF || t is KwG || t is KwU || t is KwR)
            ==> boundary_ok(s, i + token_text(t).len()),
    ensures
        lex_from(s, i) == cons_opt(t, lex_from(s, i + token_text(t).len())),
{
    let x = token_text(t);
    let e = i + x.len();
    assert forall|k: int| 0 <= k < x.len() implies s[i + k] == x[k] by {
        assert(s.subrange(i as int, e as int)[k] == s[i + k]);
    }
    if t is Num {
        let v = t->Num_0;
        lemma_digits(v as nat);
        assert(s[i as int] == x[0]);
        assert forall|k: int| i + 1 <= k < e implies is_digit(#[trigger] s[k]) by { assert(s[k] == x[k - i]); }
        lemma_digits_end_run(s, i + 1, e);
        lemma_digits_value(s, i, v as nat);
    } else if t is Name || t is True || t is False || t is KwF || t is KwG || t is KwU || t is KwR {
        assert(s[i as int] == x[0]);
        assert forall|k: int| i + 1 <= k < e implies is_word_char(#[trigger] s[k]) by {
            assert(s[k] == x[k - i]);
        }
        lemma_word_end_run(s, i + 1, e);
        let w = s.subrange(i as int, e as int);
        assert(w =~= x);
    } else {
        assert(s[i as int] == x[0]);
        if t is Implies || t is Iff {
            assert(s[(i + 1) as int] == x[1]);
            if t is Iff { assert(s[(i + 2) as int] == x[2]); }
        }
    }
}

/// The lexer reads `render(ts)`, appearing as the end of `s`, as `ts`.
proof fn lemma_lex_render(s: Seq<u8>, i: nat, ts: Seq<SpecToken>)
    requires
        valid_tokens(ts),
        i <= s.len(),
        s.subrange(i as int, s.len() as int) == render(ts),
    ensures
        lex_from(s, i) == Some(ts),
    decreases ts.len(),
{
    if ts.len() == 0 {
        assert(i == s.len());
    } else {
        let t = ts[0];
        let x = token_text(t);
        let e = i + x.len();
        if ts.len() == 1 {
            assert(s.subrange(i as int, e as int) =~= x);
            lemma_lex_token(s, i, t);
            assert(lex_from(s, e) == Some(Seq::<SpecToken>::empty()));
            assert(seq![t] + Seq::<SpecToken>::empty() =~= ts);
        } else {
            let rest = ts.drop_first();
            let sep = separator(ts[0], ts[1]);
            lemma_render_head(ts);
            let all = s.subrange(i as int, s.len() as int);
            assert(all == x + sep + render(rest));
            assert((x + sep + render(rest)).subrange(0, x.len() as int) =~= x);
            assert(s.subrange(i as int, e as int) =~= all.subrange(0, x.len() as int));
            assert((x + sep + render(rest)).subrange((x.len() + sep.len()) as int, all.len() as int) =~= render(rest));
            let e2 = e + sep.len();
            assert(s.subrange(e2 as int, s.len() as int) =~= all.subrange((x.len() + sep.len()) as int, all.len() as int));
            assert forall|k: int| 0 <= k < rest.len() implies valid_token(#[trigger] rest[k]) by {
                assert(rest[k] == ts[k + 1]);
            }
            lemma_lex_render(s, e2, rest);
            // the character after the token's text cannot continue it
            assert(s[e as int] == all[x.len() as int]);
            if sep.len() == 0 {
                lemma_render_first(rest);
                assert(all[x.len() as int] == render(rest)[0]);
            }
            lemma_lex_token(s, i, t);
            if sep.len() == 1 {
                assert(s[e as int] == 32);
                assert(lex_from(s, e) == lex_from(s, e + 1));
            }
            assert(seq![t] + rest =~= ts);
        }
    }
}

/// The first character of `render(ts)` is the first character of its first token.
proof fn lemma_render_first(ts: Seq<SpecToken>)
    requires
        ts.len() >= 1,
        valid_tokens(ts),
    ensures
        render(ts).len() >= 1,
        render(ts)[0] == token_text(ts[0])[0],
        (ts[0] is RParen || ts[0] is RBrack || ts[0] is Comma || ts[0] is LBrack)
            ==> !(is_word_char(render(ts)[0]) || is_digit(render(ts)[0])),
    decreases ts.len(),
{
    lemma_token_text_len(ts[0]);
    if ts.len() >= 2 {
        lemma_render_head(ts);
    }
}

proof fn lemma_token_text_len(t: SpecToken)
    requires
        valid_token(t),
    ensures
        token_text(t).len() >= 1,
{
    if t is Num { lemma_digits(t->Num_0 as nat); }
}


// ---------------------------------------------------------------------------
// The round trip
// ---------------------------------------------------------------------------

proof fn lemma_valid_concat(x: Seq<SpecToken>, y: Seq<SpecToken>)
    requires
        valid_tokens(x),
        valid_tokens(y),
    ensures
        valid_tokens(x + y),
{
    assert forall|k: int| 0 <= k < (x + y).len() implies valid_token(#[trigger] (x + y)[k]) by {
        if k < x.len() { assert((x + y)[k] == x[k]); } else { assert((x + y)[k] == y[k - x.len()]); }
    }
}

proof fn lemma_valid_tokens_at(f: SpecFormula, l: nat)
    requires
        valid_names(f),
    ensures
        valid_tokens(tokens_at(f, l)),
    decreases f, 1nat,
{
    lemma_valid_raw(f);
    if !(level(f) <= l) {
        lemma_valid_concat(seq![Token::LParen], raw_tokens(f));
        lemma_valid_concat(seq![Token::LParen] + raw_tokens(f), seq![Token::RParen]);
    }
}

proof fn lemma_valid_raw(f: SpecFormula)
    requires
        valid_names(f),
    ensures
        valid_tokens(raw_tokens(f)),
    decreases f, 0nat,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => {
            lemma_valid_tokens_at(*g, 2);
            lemma_valid_concat(seq![Token::Not], tokens_at(*g, 2));
        },
        Mltl::Future(a, b, g) | Mltl::Global(a, b, g) => {
            let kw = if f is Future { seq![Token::<Seq<u8>>::KwF] } else { seq![Token::<Seq<u8>>::KwG] };
            lemma_valid_tokens_at(*g, 2);
            lemma_valid_concat(kw, interval_tokens(a, b));
            lemma_valid_concat(kw + interval_tokens(a, b), tokens_at(*g, 2));
        },
        Mltl::Until(g, a, b, h) | Mltl::Release(g, a, b, h) => {
            let kw = if f is Until { seq![Token::<Seq<u8>>::KwU] } else { seq![Token::<Seq<u8>>::KwR] };
            lemma_valid_tokens_at(*g, 2);
            lemma_valid_tokens_at(*h, 2);
            lemma_valid_concat(tokens_at(*g, 2), kw);
            lemma_valid_concat(tokens_at(*g, 2) + kw, interval_tokens(a, b));
            lemma_valid_concat(tokens_at(*g, 2) + kw + interval_tokens(a, b), tokens_at(*h, 2));
        },
        Mltl::And(g, h) | Mltl::Or(g, h) => {
            let (lg, lh) = if f is And { (4nat, 3nat) } else { (6nat, 5nat) };
            let op = if f is And { seq![Token::<Seq<u8>>::And] } else { seq![Token::<Seq<u8>>::Or] };
            lemma_valid_tokens_at(*g, lg);
            lemma_valid_tokens_at(*h, lh);
            lemma_valid_concat(tokens_at(*g, lg), op);
            lemma_valid_concat(tokens_at(*g, lg) + op, tokens_at(*h, lh));
        },
    }
}

/// **Round trip.** For every formula with well-formed intervals and valid
/// names, the printed text denotes that formula. With `parse`'s
/// completeness, parsing the printed text gives back exactly `f`.
pub proof fn lemma_round_trip(f: SpecFormula)
    requires
        printable(f),
    ensures
        denotes(print_text(f), f),
{
    let ts = print_tokens(f);
    let s = render(ts);
    lemma_valid_tokens_at(f, 7);
    assert(s.subrange(0, s.len() as int) =~= s);
    lemma_lex_render(s, 0, ts);
    lemma_print_tokens(f);
}

// ---------------------------------------------------------------------------
// Executable printer
// ---------------------------------------------------------------------------

fn exec_level(f: &ExecFormula) -> (r: u8)
    ensures
        r as nat == level(view_f(*f)),
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(_) | Mltl::Future(_, _, _) | Mltl::Global(_, _, _) => 2,
        Mltl::Until(_, _, _, _) | Mltl::Release(_, _, _, _) => 3,
        Mltl::And(_, _) => 4,
        Mltl::Or(_, _) => 6,
    }
}

fn push_interval(a: usize, b: usize, out: &mut Vec<Token<Vec<u8>>>)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@) + interval_tokens(a, b),
{
    let ghost before = tokens_view(out@);
    out.push(Token::LBrack);
    out.push(Token::Num(a));
    out.push(Token::Comma);
    out.push(Token::Num(b));
    out.push(Token::RBrack);
    proof { assert(tokens_view(out@) =~= before + interval_tokens(a, b)); }
}

fn push_token(t: Token<Vec<u8>>, out: &mut Vec<Token<Vec<u8>>>)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@) + seq![token_view(t)],
{
    let ghost before = tokens_view(out@);
    out.push(t);
    proof { assert(tokens_view(out@) =~= before + seq![token_view(t)]); }
}

/// Appends `tokens_at(f, l)`.
fn exec_tokens_at(f: &ExecFormula, l: u8, out: &mut Vec<Token<Vec<u8>>>)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@) + tokens_at(view_f(*f), l as nat),
    decreases f, 1nat,
{
    let ghost before = tokens_view(out@);
    if exec_level(f) <= l {
        exec_raw_tokens(f, out);
    } else {
        push_token(Token::LParen, out);
        exec_raw_tokens(f, out);
        push_token(Token::RParen, out);
        proof {
            assert(tokens_view(out@) =~= before + (seq![Token::LParen] + raw_tokens(view_f(*f)) + seq![Token::RParen]));
        }
    }
}

/// Appends `raw_tokens(f)`.
#[verifier::spinoff_prover]
fn exec_raw_tokens(f: &ExecFormula, out: &mut Vec<Token<Vec<u8>>>)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@) + raw_tokens(view_f(*f)),
    decreases f, 0nat,
{
    let ghost before = tokens_view(out@);
    let ghost vf = view_f(*f);
    match f {
        Mltl::True => push_token(Token::True, out),
        Mltl::False => push_token(Token::False, out),
        Mltl::Prop(n) => push_token(Token::Name(copy_vec(n)), out),
        Mltl::Not(g) => {
            push_token(Token::Not, out);
            exec_tokens_at(g, 2, out);
            proof { assert(tokens_view(out@) =~= before + raw_tokens(vf)); }
        },
        Mltl::Future(a, b, g) => {
            push_token(Token::KwF, out);
            push_interval(*a, *b, out);
            exec_tokens_at(g, 2, out);
            proof { assert(tokens_view(out@) =~= before + raw_tokens(vf)); }
        },
        Mltl::Global(a, b, g) => {
            push_token(Token::KwG, out);
            push_interval(*a, *b, out);
            exec_tokens_at(g, 2, out);
            proof { assert(tokens_view(out@) =~= before + raw_tokens(vf)); }
        },
        Mltl::Until(g, a, b, h) => {
            exec_tokens_at(g, 2, out);
            push_token(Token::KwU, out);
            push_interval(*a, *b, out);
            exec_tokens_at(h, 2, out);
            proof { assert(tokens_view(out@) =~= before + raw_tokens(vf)); }
        },
        Mltl::Release(g, a, b, h) => {
            exec_tokens_at(g, 2, out);
            push_token(Token::KwR, out);
            push_interval(*a, *b, out);
            exec_tokens_at(h, 2, out);
            proof { assert(tokens_view(out@) =~= before + raw_tokens(vf)); }
        },
        Mltl::And(g, h) => {
            exec_tokens_at(g, 4, out);
            push_token(Token::And, out);
            exec_tokens_at(h, 3, out);
            proof { assert(tokens_view(out@) =~= before + raw_tokens(vf)); }
        },
        Mltl::Or(g, h) => {
            exec_tokens_at(g, 6, out);
            push_token(Token::Or, out);
            exec_tokens_at(h, 5, out);
            proof { assert(tokens_view(out@) =~= before + raw_tokens(vf)); }
        },
    }
}

/// Appends the decimal digits of `v`.
pub(crate) fn push_digits(v: usize, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + digits(v as nat),
    decreases v,
{
    let ghost before = out@;
    if v >= 10 {
        push_digits(v / 10, out);
    }
    out.push((48 + v % 10) as u8);
    proof {
        if v < 10 { assert(out@ =~= before + digits(v as nat)); }
        else { assert(out@ =~= before + digits(v as nat)); }
    }
}

fn push_bytes(b: &[u8], out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + b@,
{
    let ghost before = out@;
    let mut k = 0;
    while k < b.len()
        invariant
            k <= b.len(),
            out@ == before + b@.subrange(0, k as int),
        decreases b.len() - k,
    {
        out.push(b[k]);
        k = k + 1;
        proof { assert(out@ =~= before + b@.subrange(0, k as int)); }
    }
    proof { assert(b@.subrange(0, b.len() as int) =~= b@); }
}

fn push_text(t: &Token<Vec<u8>>, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + token_text(token_view(*t)),
{
    let ghost before = out@;
    match t {
        Token::Name(n) => push_bytes(n.as_slice(), out),
        Token::Num(v) => push_digits(*v, out),
        Token::True => { push_bytes(&[116u8, 114, 117, 101], out); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::False => { push_bytes(&[102u8, 97, 108, 115, 101], out); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::KwF => { out.push(70); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::KwG => { out.push(71); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::KwU => { out.push(85); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::KwR => { out.push(82); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::LParen => { out.push(40); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::RParen => { out.push(41); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::LBrack => { out.push(91); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::RBrack => { out.push(93); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::Comma => { out.push(44); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::Not => { out.push(33); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::And => { out.push(38); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::Or => { out.push(124); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::Xor => { out.push(94); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::Implies => { out.push(45); out.push(62); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
        Token::Iff => { out.push(60); out.push(45); out.push(62); proof { assert(out@ =~= before + token_text(token_view(*t))); } },
    }
}

fn exec_glue(t1: &Token<Vec<u8>>, t2: &Token<Vec<u8>>) -> (r: bool)
    ensures
        r == glue(token_view(*t1), token_view(*t2)),
{
    let a = match t1 { Token::LParen | Token::LBrack | Token::Comma | Token::Not => true, _ => false };
    let b = match t2 { Token::RParen | Token::RBrack | Token::Comma | Token::LBrack => true, _ => false };
    a || b
}

/// The text of a token sequence: exactly `render`.
fn exec_render(ts: &Vec<Token<Vec<u8>>>) -> (r: Vec<u8>)
    ensures
        r@ == render(tokens_view(ts@)),
{
    let ghost tv = tokens_view(ts@);
    let mut out: Vec<u8> = Vec::new();
    let mut k = 0;
    while k < ts.len()
        invariant
            k <= ts.len(),
            tv == tokens_view(ts@),
            out@ == render(tv.subrange(0, k as int)),
        decreases ts.len() - k,
    {
        let ghost pre = tv.subrange(0, k as int);
        let ghost next = tv.subrange(0, k + 1);
        proof {
            assert(next.drop_last() =~= pre);
            assert(next.last() == tv[k as int]);
            assert(tv[k as int] == token_view(ts@[k as int]));
        }
        if k > 0 {
            proof {
                assert(next[next.len() - 2] == token_view(ts@[k - 1]));
                assert(tv[k - 1] == token_view(ts@[k - 1]));
            }
            if !exec_glue(&ts[k - 1], &ts[k]) {
                out.push(32);
            }
            let ghost mid = out@;
            push_text(&ts[k], &mut out);
            proof {
                assert(render(next) == render(pre) + separator(next[next.len() - 2], next[next.len() - 1]) + token_text(next.last()));
            }
        } else {
            push_text(&ts[k], &mut out);
            proof {
                assert(next =~= seq![tv[0]]);
                assert(pre =~= Seq::<SpecToken>::empty());
                assert(out@ =~= render(next));
            }
        }
        k = k + 1;
    }
    proof { assert(tv.subrange(0, ts.len() as int) =~= tv); }
    out
}

/// Print a formula as text (GRAMMAR.md syntax, as few parentheses as the
/// levels allow). For formulas with well-formed intervals and valid names,
/// the text denotes exactly `f`, so [`crate::parse`] returns `f` again.
pub fn print(f: &ExecFormula) -> (r: Vec<u8>)
    ensures
        r@ == print_text(view_f(*f)),
        printable(view_f(*f)) ==> denotes(r@, view_f(*f)),
{
    let mut ts: Vec<Token<Vec<u8>>> = Vec::new();
    exec_tokens_at(f, 7, &mut ts);
    proof { assert(tokens_view(ts@) =~= print_tokens(view_f(*f))); }
    let r = exec_render(&ts);
    proof {
        if printable(view_f(*f)) { lemma_round_trip(view_f(*f)); }
    }
    r
}

} // verus!
