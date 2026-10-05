//! Packed trace regexes for the fast WEST (`fast.rs`), and what they mean.
//!
//! A trace regex of `len` states over `n` atoms is `words_for(n, len)` words.
//! Entry `(t, v)` is pair `p = n·t + v`: bit `2p` = "may be false", bit
//! `2p+1` = "may be true" (11 = `S`, 10 = `One`, 01 = `Zero`; 00 never
//! occurs in a well-formed regex). Bits past `2·n·len` are 1. `ptrace`
//! reads the words back as a `TraceRegex`, so every lemma about the spec
//! operations of `algorithms.rs` applies.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use crate::algorithms::*;
use crate::bits::*;
use crate::matching::*;

verus! {

/// Words needed for `len` states of `n` atoms.
pub open spec fn words_for(n: nat, len: nat) -> nat {
    ((2 * n * len + 63) / 64) as nat
}

/// Bit `q` of a trace's words.
pub open spec fn gb(x: Seq<u64>, q: int) -> bool {
    bit(x[q / 64], q % 64)
}

/// Pair `p` (bits `2p`, `2p+1`) of a trace's words is not `00`.
pub open spec fn pok(x: Seq<u64>, p: int) -> bool {
    gb(x, 2 * p) || gb(x, 2 * p + 1)
}

/// Reading a pair of bits as a `WestBit` (`00`, which well-formed regexes
/// never contain, reads as `Zero`).
pub open spec fn decode(lo: bool, hi: bool) -> WestBit {
    if lo && hi { WestBit::S } else if hi { WestBit::One } else { WestBit::Zero }
}

/// Entry for pair `p`.
pub open spec fn pentry(x: Seq<u64>, p: int) -> WestBit {
    decode(gb(x, 2 * p), gb(x, 2 * p + 1))
}

/// The trace regex the words `x` stand for.
pub open spec fn tr(x: Seq<u64>, n: nat, len: nat) -> TraceRegex {
    Seq::new(len, |t: int| Seq::new(n, |v: int| pentry(x, n * t + v)))
}

/// Well-formed packed trace: right number of words, no `00` pair among the
/// `n·len` used ones, all unused bits 1.
pub open spec fn twf(x: Seq<u64>, n: nat, len: nat) -> bool {
    &&& x.len() == words_for(n, len)
    &&& forall|p: int| 0 <= p < n * len ==> #[trigger] pok(x, p)
    &&& forall|q: int| 2 * n * len <= q < 64 * x.len() ==> #[trigger] gb(x, q)
}

// ---------------------------------------------------------------------------
// Position arithmetic
// ---------------------------------------------------------------------------

/// Bits `2p` and `2p+1` are bits `2(p % 32)` and `2(p % 32) + 1` of word
/// `p / 32`.
pub proof fn lemma_pair_pos(p: int)
    requires
        p >= 0,
    ensures
        (2 * p) / 64 == p / 32,
        (2 * p) % 64 == 2 * (p % 32),
        (2 * p + 1) / 64 == p / 32,
        (2 * p + 1) % 64 == 2 * (p % 32) + 1,
{
    lemma_fundamental_div_mod(p, 32);
    let a = p / 32;
    let b = p % 32;
    assert(0 <= b < 32) by { lemma_mod_bound(p, 32); }
    assert(2 * p == 64 * a + 2 * b);
    lemma_fundamental_div_mod_converse(2 * p, 64, a, 2 * b);
    lemma_fundamental_div_mod_converse(2 * p + 1, 64, a, 2 * b + 1);
}

/// Splitting a pair index of a `len × n` grid into `(t, v)`.
pub proof fn lemma_grid(n: nat, len: nat, p: int)
    requires
        n >= 1,
        0 <= p < n * len,
    ensures
        0 <= p / (n as int) < len,
        0 <= p % (n as int) < n,
        p == n * (p / (n as int)) + p % (n as int),
{
    lemma_fundamental_div_mod(p, n as int);
    lemma_mod_bound(p, n as int);
    lemma_div_pos_is_pos(p, n as int);
    if p / (n as int) >= len {
        lemma_mul_inequality(len as int, p / (n as int), n as int);
        lemma_mul_is_commutative(len as int, n as int);
        lemma_mul_is_commutative(p / (n as int), n as int);
    }
}

/// `n·t + v < n·len` for `t < len`, `v < n`.
pub proof fn lemma_grid_bound(n: nat, len: nat, t: int, v: int)
    requires
        0 <= t < len,
        0 <= v < n,
    ensures
        0 <= n * t + v < n * len,
{
    lemma_mul_inequality(t + 1, len as int, n as int);
    lemma_mul_is_commutative(t + 1, n as int);
    lemma_mul_is_commutative(len as int, n as int);
    lemma_mul_is_distributive_add(n as int, t, 1);
    lemma_mul_nonnegative(n as int, t);
}

/// The used pairs fit in the words: `2·n·len ≤ 64·words_for(n, len)`, and
/// the words are at most one more than needed.
pub proof fn lemma_words_for(n: nat, len: nat)
    ensures
        2 * n * len <= 64 * words_for(n, len),
        64 * words_for(n, len) < 2 * n * len + 64,
        n >= 1 && len >= 1 ==> words_for(n, len) >= 1,
{
    let m = 2 * n * len;
    lemma_fundamental_div_mod((m + 63) as int, 64);
    lemma_mod_bound((m + 63) as int, 64);
    if n >= 1 && len >= 1 {
        assert(2 * n * len >= 2) by (nonlinear_arith) requires n >= 1, len >= 1;
    }
}

// ---------------------------------------------------------------------------
// Entries of a well-formed trace
// ---------------------------------------------------------------------------

/// Entry `(t, v)` of `tr x` is pair `n·t + v`.
pub proof fn lemma_tr_entry(x: Seq<u64>, n: nat, len: nat, t: int, v: int)
    requires
        0 <= t < len,
        0 <= v < n,
    ensures
        tr(x, n, len)[t][v] == pentry(x, n * t + v),
        tr(x, n, len)[t].len() == n,
{
}

/// `tr` has `len` states of `n` entries.
pub proof fn lemma_tr_of_vars(x: Seq<u64>, n: nat, len: nat)
    ensures
        tr(x, n, len).len() == len,
        trace_regex_of_vars(tr(x, n, len), n),
{
}

/// Two traces with the same used pairs read the same.
pub proof fn lemma_tr_ext(x: Seq<u64>, y: Seq<u64>, n: nat, len: nat)
    requires
        forall|p: int| 0 <= p < n * len ==> #[trigger] pentry(x, p) == pentry(y, p),
    ensures
        tr(x, n, len) == tr(y, n, len),
{
    assert forall|t: int| 0 <= t < len implies #[trigger] tr(x, n, len)[t] == tr(y, n, len)[t] by {
        assert forall|v: int| 0 <= v < n implies tr(x, n, len)[t][v] == tr(y, n, len)[t][v] by {
            lemma_grid_bound(n, len, t, v);
            assert(pentry(x, n * t + v) == pentry(y, n * t + v));
        }
        assert(tr(x, n, len)[t] =~= tr(y, n, len)[t]);
    }
    assert(tr(x, n, len) =~= tr(y, n, len));
}

/// Different bit pairs (neither `00`) read differently.
pub proof fn lemma_decode_inj(a: bool, b: bool, c: bool, d: bool)
    requires
        a || b,
        c || d,
    ensures
        (decode(a, b) == decode(c, d)) <==> (a == c && b == d),
{
}

} // verus!
