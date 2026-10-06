//! Tokens and the lexer (GRAMMAR.md §1).
//!
//! `lex_spec` is the specification: a recursive definition of how text
//! splits into tokens (longest match; whitespace separates tokens). `lex` is
//! the executable lexer, proved to return exactly `lex_spec`.
use vstd::prelude::*;

verus! {

/// A token. `N` is the type of names: `Vec<u8>` in executable code, `Seq<u8>`
/// in specifications.
pub enum Token<N> {
    Name(N),
    Num(usize),
    /// `true`, `t`, `tt`
    True,
    /// `false`, `f`, `ff`
    False,
    /// `F`
    KwF,
    /// `G`
    KwG,
    /// `U`
    KwU,
    /// `R`
    KwR,
    LParen,
    RParen,
    LBrack,
    RBrack,
    /// `{` (traces only)
    LBrace,
    /// `}` (traces only)
    RBrace,
    Comma,
    /// `!`
    Not,
    /// `&`
    And,
    /// `|`
    Or,
    /// `^`
    Xor,
    /// `->`
    Implies,
    /// `<->`
    Iff,
}

pub type SpecToken = Token<Seq<u8>>;

/// The bytes `start..end` of a text. At the end of the text,
/// `start == end == text.len()`.
pub struct Span {
    pub start: usize,
    pub end: usize,
}

pub open spec fn span_ok(s: Span, n: nat) -> bool {
    s.start <= s.end && s.end <= n
}

/// One span per token, each non-empty and inside a text of length `n`.
pub open spec fn spans_ok(sp: Seq<Span>, count: nat, n: nat) -> bool {
    &&& sp.len() == count
    &&& forall|k: int| #![trigger sp[k]] 0 <= k < sp.len() ==> sp[k].start < sp[k].end && sp[k].end <= n
}

pub open spec fn token_view(t: Token<Vec<u8>>) -> SpecToken {
    match t {
        Token::Name(n) => Token::Name(n@),
        Token::Num(v) => Token::Num(v),
        Token::True => Token::True,
        Token::False => Token::False,
        Token::KwF => Token::KwF,
        Token::KwG => Token::KwG,
        Token::KwU => Token::KwU,
        Token::KwR => Token::KwR,
        Token::LParen => Token::LParen,
        Token::RParen => Token::RParen,
        Token::LBrack => Token::LBrack,
        Token::RBrack => Token::RBrack,
        Token::LBrace => Token::LBrace,
        Token::RBrace => Token::RBrace,
        Token::Comma => Token::Comma,
        Token::Not => Token::Not,
        Token::And => Token::And,
        Token::Or => Token::Or,
        Token::Xor => Token::Xor,
        Token::Implies => Token::Implies,
        Token::Iff => Token::Iff,
    }
}

pub open spec fn tokens_view(ts: Seq<Token<Vec<u8>>>) -> Seq<SpecToken> {
    ts.map_values(|t: Token<Vec<u8>>| token_view(t))
}

// ---------------------------------------------------------------------------
// Character classes (ASCII)
// ---------------------------------------------------------------------------

pub open spec fn is_digit(c: u8) -> bool { 48 <= c && c <= 57 }
pub open spec fn is_letter(c: u8) -> bool { (65 <= c && c <= 90) || (97 <= c && c <= 122) }
/// A name or keyword starts with a letter or `_` (95).
pub open spec fn is_word_start(c: u8) -> bool { is_letter(c) || c == 95 }
/// ... and continues with letters, digits or `_`.
pub open spec fn is_word_char(c: u8) -> bool { is_letter(c) || is_digit(c) || c == 95 }
/// Space, tab, line feed, carriage return.
pub open spec fn is_space(c: u8) -> bool { c == 32 || c == 9 || c == 10 || c == 13 }

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// End of the run of characters satisfying `is_word_char` starting at `i`.
pub open spec fn word_end(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i < s.len() && is_word_char(s[i as int]) { word_end(s, i + 1) } else { i }
}

/// End of the run of digits starting at `i`.
pub open spec fn digits_end(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i,
{
    if i < s.len() && is_digit(s[i as int]) { digits_end(s, i + 1) } else { i }
}

/// The decimal value of `s[i..j]` (all digits).
pub open spec fn digits_value(s: Seq<u8>, i: nat, j: nat) -> nat
    decreases j,
{
    if j <= i { 0 } else { digits_value(s, i, (j - 1) as nat) * 10 + (s[j - 1] - 48) as nat }
}

/// `w` is the word whose bytes are `b`.
pub open spec fn is_word(w: Seq<u8>, b: Seq<u8>) -> bool {
    w.len() == b.len() && forall|k: int| 0 <= k < w.len() ==> w[k] == b[k]
}

/// Keywords (GRAMMAR.md §1), or `None` for an ordinary name.
pub open spec fn keyword(w: Seq<u8>) -> Option<SpecToken> {
    if is_word(w, seq![70u8]) { Some(Token::KwF) }                           // F
    else if is_word(w, seq![71u8]) { Some(Token::KwG) }                      // G
    else if is_word(w, seq![85u8]) { Some(Token::KwU) }                      // U
    else if is_word(w, seq![82u8]) { Some(Token::KwR) }                      // R
    else if is_word(w, seq![116u8, 114, 117, 101]) || is_word(w, seq![116u8]) || is_word(w, seq![116u8, 116]) {
        Some(Token::True)                                                    // true, t, tt
    } else if is_word(w, seq![102u8, 97, 108, 115, 101]) || is_word(w, seq![102u8]) || is_word(w, seq![102u8, 102]) {
        Some(Token::False)                                                   // false, f, ff
    } else { None }
}

/// Single-character symbols.
pub open spec fn symbol(c: u8) -> Option<SpecToken> {
    if c == 40 { Some(Token::LParen) }        // (
    else if c == 41 { Some(Token::RParen) }   // )
    else if c == 91 { Some(Token::LBrack) }   // [
    else if c == 93 { Some(Token::RBrack) }   // ]
    else if c == 123 { Some(Token::LBrace) }  // {
    else if c == 125 { Some(Token::RBrace) }  // }
    else if c == 44 { Some(Token::Comma) }    // ,
    else if c == 33 { Some(Token::Not) }      // !
    else if c == 38 { Some(Token::And) }      // &
    else if c == 124 { Some(Token::Or) }      // |
    else if c == 94 { Some(Token::Xor) }      // ^
    else { None }
}

pub open spec fn cons_opt(t: SpecToken, rest: Option<Seq<SpecToken>>) -> Option<Seq<SpecToken>> {
    match rest {
        Some(r) => Some(seq![t] + r),
        None => None,
    }
}

/// The tokens of `s[i..]`, or `None` if it contains something that is not a
/// token (an unknown character, or a number larger than `usize::MAX`).
pub open spec fn lex_from(s: Seq<u8>, i: nat) -> Option<Seq<SpecToken>>
    decreases s.len() - i,
    via lex_from_decreases
{
    if i >= s.len() {
        Some(Seq::empty())
    } else {
        let c = s[i as int];
        if is_space(c) {
            lex_from(s, i + 1)
        } else if is_word_start(c) {
            let j = word_end(s, i + 1);
            let w = s.subrange(i as int, j as int);
            let t = match keyword(w) { Some(k) => k, None => Token::Name(w) };
            cons_opt(t, lex_from(s, j))
        } else if is_digit(c) {
            let j = digits_end(s, i + 1);
            let v = digits_value(s, i, j);
            if v > usize::MAX { None } else { cons_opt(Token::Num(v as usize), lex_from(s, j)) }
        } else if c == 45 && i + 1 < s.len() && s[(i + 1) as int] == 62 {             // ->
            cons_opt(Token::Implies, lex_from(s, i + 2))
        } else if c == 60 && i + 2 < s.len() && s[(i + 1) as int] == 45 && s[(i + 2) as int] == 62 {  // <->
            cons_opt(Token::Iff, lex_from(s, i + 3))
        } else {
            match symbol(c) {
                Some(t) => cons_opt(t, lex_from(s, i + 1)),
                None => None,
            }
        }
    }
}

pub proof fn lemma_word_end(s: Seq<u8>, i: nat)
    requires
        i <= s.len(),
    ensures
        i <= word_end(s, i) <= s.len(),
        forall|k: int| i <= k < word_end(s, i) ==> is_word_char(s[k]),
        word_end(s, i) < s.len() ==> !is_word_char(s[word_end(s, i) as int]),
    decreases s.len() - i,
{
    if i < s.len() && is_word_char(s[i as int]) {
        lemma_word_end(s, i + 1);
    }
}

pub proof fn lemma_digits_end(s: Seq<u8>, i: nat)
    requires
        i <= s.len(),
    ensures
        i <= digits_end(s, i) <= s.len(),
        forall|k: int| i <= k < digits_end(s, i) ==> is_digit(s[k]),
        digits_end(s, i) < s.len() ==> !is_digit(s[digits_end(s, i) as int]),
    decreases s.len() - i,
{
    if i < s.len() && is_digit(s[i as int]) {
        lemma_digits_end(s, i + 1);
    }
}

#[via_fn]
proof fn lex_from_decreases(s: Seq<u8>, i: nat) {
    if i < s.len() {
        lemma_word_end(s, i + 1);
        lemma_digits_end(s, i + 1);
    }
}

/// The tokens of `s`.
pub open spec fn lex_spec(s: Seq<u8>) -> Option<Seq<SpecToken>> {
    lex_from(s, 0)
}

/// Adding a digit never makes a number smaller.
pub proof fn lemma_digits_value_mono(s: Seq<u8>, i: nat, j: nat, k: nat)
    requires
        i <= j <= k <= s.len(),
        forall|m: int| i <= m < k ==> is_digit(s[m]),
    ensures
        digits_value(s, i, j) <= digits_value(s, i, k),
    decreases k - j,
{
    if j < k {
        lemma_digits_value_mono(s, i, j, (k - 1) as nat);
        assert(digits_value(s, i, k) == digits_value(s, i, (k - 1) as nat) * 10 + (s[k - 1] - 48) as nat);
    }
}

// ---------------------------------------------------------------------------
// Executable lexer
// ---------------------------------------------------------------------------

/// `lex_from(s, 0) == prefix ++ lex_from(s, i)` (as options).
pub open spec fn lex_split(s: Seq<u8>, prefix: Seq<SpecToken>, i: nat) -> bool {
    lex_spec(s) == match lex_from(s, i) {
        Some(r) => Some(prefix + r),
        None => None::<Seq<SpecToken>>,
    }
}

/// One lexing step that emits token `t` and continues at `j`.
proof fn lemma_split_step(s: Seq<u8>, prefix: Seq<SpecToken>, i: nat, t: SpecToken, j: nat)
    requires
        lex_split(s, prefix, i),
        lex_from(s, i) == cons_opt(t, lex_from(s, j)),
    ensures
        lex_split(s, prefix + seq![t], j),
{
    match lex_from(s, j) {
        Some(r) => { assert(prefix + (seq![t] + r) =~= (prefix + seq![t]) + r); },
        None => {},
    }
}

pub fn exec_keyword(s: &[u8], i: usize, j: usize) -> (r: Option<Token<Vec<u8>>>)
    requires
        i < j <= s.len(),
    ensures
        match r {
            Some(t) => keyword(s@.subrange(i as int, j as int)) == Some(token_view(t)) && !(t is Name),
            None => keyword(s@.subrange(i as int, j as int)) is None,
        },
{
    let ghost w = s@.subrange(i as int, j as int);
    let n = j - i;
    let c0 = s[i];
    proof { assert(w[0] == c0); }
    if n == 1 {
        if c0 == 70 { return Some(Token::KwF); }
        if c0 == 71 { return Some(Token::KwG); }
        if c0 == 85 { return Some(Token::KwU); }
        if c0 == 82 { return Some(Token::KwR); }
        if c0 == 116 { return Some(Token::True); }
        if c0 == 102 { return Some(Token::False); }
        return None;
    }
    let c1 = s[i + 1];
    proof { assert(w[1] == c1); }
    if n == 2 {
        if c0 == 116 && c1 == 116 { return Some(Token::True); }
        if c0 == 102 && c1 == 102 { return Some(Token::False); }
        return None;
    }
    if n == 4 {
        let (c2, c3) = (s[i + 2], s[i + 3]);
        proof { assert(w[2] == c2 && w[3] == c3); }
        if c0 == 116 && c1 == 114 && c2 == 117 && c3 == 101 { return Some(Token::True); }
        return None;
    }
    if n == 5 {
        let (c2, c3, c4) = (s[i + 2], s[i + 3], s[i + 4]);
        proof { assert(w[2] == c2 && w[3] == c3 && w[4] == c4); }
        if c0 == 102 && c1 == 97 && c2 == 108 && c3 == 115 && c4 == 101 { return Some(Token::False); }
        return None;
    }
    None
}

fn exec_symbol(c: u8) -> (r: Option<Token<Vec<u8>>>)
    ensures
        match r {
            Some(t) => symbol(c) == Some(token_view(t)),
            None => symbol(c) is None,
        },
{
    if c == 40 { Some(Token::LParen) }
    else if c == 41 { Some(Token::RParen) }
    else if c == 91 { Some(Token::LBrack) }
    else if c == 93 { Some(Token::RBrack) }
    else if c == 123 { Some(Token::LBrace) }
    else if c == 125 { Some(Token::RBrace) }
    else if c == 44 { Some(Token::Comma) }
    else if c == 33 { Some(Token::Not) }
    else if c == 38 { Some(Token::And) }
    else if c == 124 { Some(Token::Or) }
    else if c == 94 { Some(Token::Xor) }
    else { None }
}

fn copy_bytes(s: &[u8], i: usize, j: usize) -> (r: Vec<u8>)
    requires
        i <= j <= s.len(),
    ensures
        r@ == s@.subrange(i as int, j as int),
{
    let mut r: Vec<u8> = Vec::with_capacity(j - i);
    let mut k = i;
    while k < j
        invariant
            i <= k <= j <= s.len(),
            r@ == s@.subrange(i as int, k as int),
        decreases j - k,
    {
        r.push(s[k]);
        k = k + 1;
        proof { assert(r@ =~= s@.subrange(i as int, k as int)); }
    }
    r
}

/// Record the span `start..end` of the token just added; every earlier span
/// ends at or before `before`.
fn push_span(spans: &mut Vec<Span>, start: usize, end: usize, Ghost(before): Ghost<nat>)
    requires
        before <= start < end,
        forall|k: int| #![trigger old(spans)@[k]] 0 <= k < old(spans)@.len()
            ==> old(spans)@[k].start < old(spans)@[k].end && old(spans)@[k].end <= before,
    ensures
        final(spans)@.len() == old(spans)@.len() + 1,
        forall|k: int| #![trigger final(spans)@[k]] 0 <= k < final(spans)@.len()
            ==> final(spans)@[k].start < final(spans)@[k].end && final(spans)@[k].end <= end,
{
    let ghost old_sp = spans@;
    spans.push(Span { start, end });
    proof {
        assert forall|k: int| #![trigger spans@[k]] 0 <= k < spans@.len()
            implies spans@[k].start < spans@[k].end && spans@[k].end <= end by {
            if k < old_sp.len() { assert(spans@[k] == old_sp[k]); }
        }
    }
}

/// The executable lexer: returns exactly `lex_spec(s)`. It also gives each
/// token's position (`spans`), or on failure the position of the piece that
/// is not a token (`fail`: an unknown character, or a number too large).
pub fn lex(s: &[u8], spans: &mut Vec<Span>, fail: &mut Span) -> (r: Option<Vec<Token<Vec<u8>>>>)
    ensures
        match r {
            Some(ts) => lex_spec(s@) == Some(tokens_view(ts@)) && spans_ok(final(spans)@, ts.len() as nat, s.len() as nat),
            None => lex_spec(s@) is None && span_ok(*final(fail), s.len() as nat),
        },
{
    let n = s.len();
    *spans = Vec::new();
    let mut out: Vec<Token<Vec<u8>>> = Vec::new();
    let mut i: usize = 0;
    proof { assert(tokens_view(out@) =~= Seq::<SpecToken>::empty()); }
    while i < n
        invariant
            i <= n, n == s.len(),
            lex_split(s@, tokens_view(out@), i as nat),
            spans_ok(spans@, out@.len() as nat, i as nat),
        decreases n - i,
    {
        let c = s[i];
        let start = i;
        let ghost before = tokens_view(out@);
        let ghost si = i as nat;
        if c == 32 || c == 9 || c == 10 || c == 13 {
            proof { assert(lex_from(s@, si) == lex_from(s@, si + 1)); }
            i = i + 1;
        } else if (65 <= c && c <= 90) || (97 <= c && c <= 122) || c == 95 {
            let mut j = i + 1;
            while j < n && ((65 <= s[j] && s[j] <= 90) || (97 <= s[j] && s[j] <= 122) || (48 <= s[j] && s[j] <= 57) || s[j] == 95)
                invariant
                    i < j <= n, n == s.len(),
                    word_end(s@, (i + 1) as nat) == word_end(s@, j as nat),
                decreases n - j,
            {
                j = j + 1;
            }
            proof { assert(word_end(s@, j as nat) == j as nat); }
            let t = match exec_keyword(s, i, j) {
                Some(k) => k,
                None => Token::Name(copy_bytes(s, i, j)),
            };
            proof {
                assert(lex_from(s@, si) == cons_opt(token_view(t), lex_from(s@, j as nat)));
                lemma_split_step(s@, before, si, token_view(t), j as nat);
            }
            out.push(t);
            proof { assert(tokens_view(out@) =~= before + seq![token_view(t)]); }
            i = j;
            push_span(spans, start, i, Ghost(si));
        } else if 48 <= c && c <= 57 {
            let mut j = i + 1;
            let mut v: usize = (c - 48) as usize;
            let mut overflow = false;
            proof {
                assert(digits_value(s@, si, si) == 0);
                assert(digits_value(s@, si, si + 1) == (s@[i as int] - 48) as nat);
            }
            while j < n && 48 <= s[j] && s[j] <= 57
                invariant
                    i < j <= n, n == s.len(),
                    digits_end(s@, (i + 1) as nat) == digits_end(s@, j as nat),
                    forall|m: int| i <= m < j ==> is_digit(#[trigger] s@[m]),
                    !overflow ==> v == digits_value(s@, i as nat, j as nat),
                    overflow ==> digits_value(s@, i as nat, j as nat) > usize::MAX,
                decreases n - j,
            {
                let d = (s[j] - 48) as usize;
                proof { assert(digits_value(s@, i as nat, (j + 1) as nat) == digits_value(s@, i as nat, j as nat) * 10 + d); }
                if !overflow {
                    if v > (usize::MAX - d) / 10 {
                        overflow = true;
                        proof {
                            assert(v * 10 + d > usize::MAX) by (nonlinear_arith)
                                requires v > (usize::MAX - d) / 10, d <= 9;
                        }
                    } else {
                        proof {
                            assert(v * 10 + d <= usize::MAX) by (nonlinear_arith)
                                requires v <= (usize::MAX - d) / 10, d <= 9;
                        }
                        v = v * 10 + d;
                    }
                } else {
                    proof {
                        assert(digits_value(s@, i as nat, j as nat) * 10 + d >= digits_value(s@, i as nat, j as nat)) by (nonlinear_arith);
                    }
                }
                j = j + 1;
            }
            proof { assert(digits_end(s@, j as nat) == j as nat); }
            if overflow {
                proof { assert(lex_from(s@, si) is None); }
                *fail = Span { start: i, end: j };
                return None;
            }
            proof {
                assert(lex_from(s@, si) == cons_opt(Token::Num(v), lex_from(s@, j as nat)));
                lemma_split_step(s@, before, si, Token::Num(v), j as nat);
            }
            out.push(Token::Num(v));
            proof { assert(tokens_view(out@) =~= before + seq![Token::<Seq<u8>>::Num(v)]); }
            i = j;
            push_span(spans, start, i, Ghost(si));
        } else if c == 45 && n - i > 1 && s[i + 1] == 62 {
            proof {
                assert(lex_from(s@, si) == cons_opt(Token::Implies, lex_from(s@, si + 2)));
                lemma_split_step(s@, before, si, Token::Implies, si + 2);
            }
            out.push(Token::Implies);
            proof { assert(tokens_view(out@) =~= before + seq![Token::<Seq<u8>>::Implies]); }
            i = i + 2;
            push_span(spans, start, i, Ghost(si));
        } else if c == 60 && n - i > 2 && s[i + 1] == 45 && s[i + 2] == 62 {
            proof {
                assert(lex_from(s@, si) == cons_opt(Token::Iff, lex_from(s@, si + 3)));
                lemma_split_step(s@, before, si, Token::Iff, si + 3);
            }
            out.push(Token::Iff);
            proof { assert(tokens_view(out@) =~= before + seq![Token::<Seq<u8>>::Iff]); }
            i = i + 3;
            push_span(spans, start, i, Ghost(si));
        } else {
            match exec_symbol(c) {
                Some(t) => {
                    proof {
                        assert(lex_from(s@, si) == cons_opt(token_view(t), lex_from(s@, si + 1)));
                        lemma_split_step(s@, before, si, token_view(t), si + 1);
                    }
                    out.push(t);
                    proof { assert(tokens_view(out@) =~= before + seq![token_view(t)]); }
                    i = i + 1;
                    push_span(spans, start, i, Ghost(si));
                },
                None => {
                    proof { assert(lex_from(s@, si) is None); }
                    *fail = Span { start: i, end: i + 1 };
                    return None;
                },
            }
        }
    }
    proof {
        assert(lex_from(s@, i as nat) == Some(Seq::<SpecToken>::empty()));
        assert(tokens_view(out@) + Seq::<SpecToken>::empty() =~= tokens_view(out@));
    }
    Some(out)
}

} // verus!
