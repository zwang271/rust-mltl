//! Word-level operations on packed trace regexes, and what they compute in
//! terms of `algorithms.rs`: AND is `WEST_and_trace`, OR is
//! `WEST_simp_trace`, the difference test implies `check_simp`, shifting
//! is `shift`, and padding is `pad`.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use mltl_core::properties::*;
use crate::algorithms::*;
use crate::bits::*;
use crate::matching::*;
use crate::packed::*;
use crate::simp::*;

verus! {

pub open spec fn and_w(x: Seq<u64>, y: Seq<u64>) -> Seq<u64> {
    Seq::new(x.len(), |k: int| x[k] & y[k])
}

pub open spec fn or_w(x: Seq<u64>, y: Seq<u64>) -> Seq<u64> {
    Seq::new(x.len(), |k: int| x[k] | y[k])
}

/// The word-level contradiction check passes on every word.
pub open spec fn word_ok(z: u64) -> bool {
    ((z | (z >> 1u64)) & LO) == LO
}

pub open spec fn words_ok(z: Seq<u64>) -> bool {
    forall|k: int| 0 <= k < z.len() ==> #[trigger] word_ok(z[k])
}

/// The difference mask of word `k`: bit `2o` set when pair `o` differs.
pub open spec fn diff_mask(x: u64, y: u64) -> u64 {
    ((x ^ y) | ((x ^ y) >> 1u64)) & LO
}

/// At most one pair differs between the words `x` and `y`.
pub open spec fn one_diff(x: Seq<u64>, y: Seq<u64>) -> bool {
    &&& forall|k: int| 0 <= k < x.len() ==> {
        let e = #[trigger] diff_mask(x[k], y[k]);
        e == 0 || e & sub(e, 1u64) == 0
    }
    &&& forall|k: int, l: int| 0 <= k < l < x.len() ==>
        #[trigger] diff_mask(x[k], y[k]) == 0 || #[trigger] diff_mask(x[l], y[l]) == 0
}

/// `0 ≤ q < d·m ⟹ q / d < m`
pub proof fn div_lt(q: int, d: int, m: int)
    requires
        d > 0,
        0 <= q < d * m,
    ensures
        q / d < m,
{
    lemma_fundamental_div_mod(q, d);
    lemma_mod_bound(q, d);
    if q / d >= m {
        lemma_mul_inequality(m, q / d, d);
        lemma_mul_is_commutative(m, d);
        lemma_mul_is_commutative(q / d, d);
    }
}

// ---------------------------------------------------------------------------
// Bits of combined words
// ---------------------------------------------------------------------------

proof fn gb_and(x: Seq<u64>, y: Seq<u64>, q: int)
    requires
        x.len() == y.len(),
        0 <= q < 64 * x.len(),
    ensures
        gb(and_w(x, y), q) == (gb(x, q) && gb(y, q)),
{
    lemma_div_pos_is_pos(q, 64);
    div_lt(q, 64, x.len() as int);
    lemma_mod_bound(q, 64);
    lemma_bit_and(x[q / 64], y[q / 64], (q % 64) as u64);
}

proof fn gb_or(x: Seq<u64>, y: Seq<u64>, q: int)
    requires
        x.len() == y.len(),
        0 <= q < 64 * x.len(),
    ensures
        gb(or_w(x, y), q) == (gb(x, q) || gb(y, q)),
{
    lemma_div_pos_is_pos(q, 64);
    div_lt(q, 64, x.len() as int);
    lemma_mod_bound(q, 64);
    lemma_bit_or(x[q / 64], y[q / 64], (q % 64) as u64);
}

/// A used pair `p` lies in word `p / 32`, which exists.
proof fn pair_in_words(n: nat, len: nat, w: nat, p: int)
    requires
        0 <= p < n * len,
        w == words_for(n, len),
    ensures
        0 <= p / 32 < w,
        0 <= 2 * p,
        2 * p + 1 < 64 * w,
{
    lemma_words_for(n, len);
    lemma_div_pos_is_pos(p, 32);
    assert(p < 32 * w) by (nonlinear_arith) requires p < n * len, 2 * n * len <= 64 * w;
    div_lt(p, 32, w as int);
}

// ---------------------------------------------------------------------------
// AND = WEST_and_trace
// ---------------------------------------------------------------------------

/// `WEST_and_bitwise` on decoded pairs is the bitwise AND of the pairs.
proof fn and_bitwise_decode(a: bool, b: bool, c: bool, d: bool)
    requires
        a || b,
        c || d,
    ensures
        WEST_and_bitwise_spec(decode(a, b), decode(c, d)) is None <==> !((a && c) || (b && d)),
        WEST_and_bitwise_spec(decode(a, b), decode(c, d)) is Some ==>
            WEST_and_bitwise_spec(decode(a, b), decode(c, d))->Some_0 == decode(a && c, b && d),
{
}

/// Pair `p` of the AND: present exactly when `WEST_and_bitwise` succeeds,
/// and then its value.
pub proof fn and_pair(x: Seq<u64>, y: Seq<u64>, n: nat, len: nat, p: int)
    requires
        twf(x, n, len),
        twf(y, n, len),
        0 <= p < n * len,
    ensures
        pok(and_w(x, y), p) <==> WEST_and_bitwise_spec(pentry(x, p), pentry(y, p)) is Some,
        pok(and_w(x, y), p) ==> WEST_and_bitwise_spec(pentry(x, p), pentry(y, p))->Some_0 == pentry(and_w(x, y), p),
{
    pair_in_words(n, len, x.len(), p);
    gb_and(x, y, 2 * p);
    gb_and(x, y, 2 * p + 1);
    assert(pok(x, p) && pok(y, p));
    and_bitwise_decode(gb(x, 2 * p), gb(x, 2 * p + 1), gb(y, 2 * p), gb(y, 2 * p + 1));
}

/// Every word passing the check means every pair is present.
proof fn words_ok_pairs(z: Seq<u64>, n: nat, len: nat, p: int)
    requires
        words_ok(z),
        z.len() == words_for(n, len),
        0 <= p < n * len,
    ensures
        pok(z, p),
{
    pair_in_words(n, len, z.len(), p);
    lemma_pair_pos(p);
    lemma_pairs_ok_word(z[p / 32]);
    lemma_mod_bound(p, 32);
    assert(word_ok(z[p / 32]));
    assert(pair_ok(z[p / 32], p % 32));
}

proof fn and_w_ok(x: Seq<u64>, y: Seq<u64>, n: nat, len: nat)
    requires
        n >= 1,
        twf(x, n, len),
        twf(y, n, len),
        words_ok(and_w(x, y)),
    ensures
        twf(and_w(x, y), n, len),
        WEST_and_trace_spec(tr(x, n, len), tr(y, n, len)) == Some(tr(and_w(x, y), n, len)),
{
    let z = and_w(x, y);
    let tx = tr(x, n, len);
    let ty = tr(y, n, len);
    let tz = tr(z, n, len);
    lemma_words_for(n, len);
    assert forall|p: int| 0 <= p < n * len implies #[trigger] pok(z, p) by {
        words_ok_pairs(z, n, len, p);
    }
    assert forall|q: int| 2 * n * len <= q < 64 * z.len() implies #[trigger] gb(z, q) by {
        gb_and(x, y, q);
        assert(gb(x, q) && gb(y, q));
    }
    assert forall|t: int| 0 <= t < len implies
        #[trigger] WEST_and_state_spec(tx[t], ty[t]) == Some(tz[t]) by {
        WEST_and_state_index(tx[t], ty[t]);
        assert forall|v: int| 0 <= v < n implies #[trigger] WEST_and_bitwise_spec(tx[t][v], ty[t][v]) is Some
            && WEST_and_bitwise_spec(tx[t][v], ty[t][v])->Some_0 == tz[t][v] by {
            lemma_grid_bound(n, len, t, v);
            words_ok_pairs(z, n, len, n * t + v);
            and_pair(x, y, n, len, n * t + v);
        }
        assert(WEST_and_state_spec(tx[t], ty[t])->Some_0 =~= tz[t]);
    }
    WEST_and_trace_index(tx, ty);
    assert forall|k: int| 0 <= k < tx.len() && k < ty.len() implies
        #[trigger] WEST_and_state_spec(tx[k], ty[k]) is Some by {
        assert(WEST_and_state_spec(tx[k], ty[k]) == Some(tz[k]));
    }
    let r = WEST_and_trace_spec(tx, ty)->Some_0;
    assert forall|t: int| 0 <= t < len implies r[t] == tz[t] by {
        assert(WEST_and_state_spec(tx[t], ty[t]) == Some(tz[t]));
    }
    assert(r =~= tz);
}

proof fn and_w_not_ok(x: Seq<u64>, y: Seq<u64>, n: nat, len: nat)
    requires
        n >= 1,
        twf(x, n, len),
        twf(y, n, len),
        !words_ok(and_w(x, y)),
    ensures
        WEST_and_trace_spec(tr(x, n, len), tr(y, n, len)) is None,
{
    let z = and_w(x, y);
    let tx = tr(x, n, len);
    let ty = tr(y, n, len);
    lemma_words_for(n, len);
    let k = choose|k: int| 0 <= k < z.len() && !#[trigger] word_ok(z[k]);
    lemma_pairs_ok_word(z[k]);
    let o = choose|o: int| 0 <= o < 32 && !#[trigger] pair_ok(z[k], o);
    let p = 32 * k + o;
    lemma_fundamental_div_mod_converse(p, 32, k, o);
    lemma_pair_pos(p);
    assert(!pok(z, p));
    if p >= n * len {
        assert(2 * n * len <= 2 * p) by (nonlinear_arith) requires p >= n * len;
        assert(2 * p < 64 * z.len());
        gb_and(x, y, 2 * p);
        assert(gb(x, 2 * p) && gb(y, 2 * p));
        assert(false);
    }
    and_pair(x, y, n, len, p);
    lemma_grid(n, len, p);
    let t = p / (n as int);
    let v = p % (n as int);
    assert(!(WEST_and_bitwise_spec(tx[t][v], ty[t][v]) is Some));
    WEST_and_state_index(tx[t], ty[t]);
    assert(!(WEST_and_state_spec(tx[t], ty[t]) is Some));
    WEST_and_trace_index(tx, ty);
}

/// AND of two well-formed packed traces: if every word passes the check, the
/// result is well formed and is `WEST_and_trace` of the two; otherwise
/// `WEST_and_trace` is `None`.
pub proof fn and_w_correct(x: Seq<u64>, y: Seq<u64>, n: nat, len: nat)
    requires
        n >= 1,
        twf(x, n, len),
        twf(y, n, len),
    ensures
        words_ok(and_w(x, y)) ==> twf(and_w(x, y), n, len)
            && WEST_and_trace_spec(tr(x, n, len), tr(y, n, len)) == Some(tr(and_w(x, y), n, len)),
        !words_ok(and_w(x, y)) ==> WEST_and_trace_spec(tr(x, n, len), tr(y, n, len)) is None,
{
    if words_ok(and_w(x, y)) {
        and_w_ok(x, y, n, len);
    } else {
        and_w_not_ok(x, y, n, len);
    }
}

// ---------------------------------------------------------------------------
// OR = WEST_simp_trace
// ---------------------------------------------------------------------------

proof fn simp_bitwise_decode(a: bool, b: bool, c: bool, d: bool)
    requires
        a || b,
        c || d,
    ensures
        WEST_simp_bitwise_spec(decode(a, b), decode(c, d)) == decode(a || c, b || d),
{
}

proof fn or_pair(x: Seq<u64>, y: Seq<u64>, n: nat, len: nat, p: int)
    requires
        twf(x, n, len),
        twf(y, n, len),
        0 <= p < n * len,
    ensures
        pok(or_w(x, y), p),
        pentry(or_w(x, y), p) == WEST_simp_bitwise_spec(pentry(x, p), pentry(y, p)),
{
    pair_in_words(n, len, x.len(), p);
    gb_or(x, y, 2 * p);
    gb_or(x, y, 2 * p + 1);
    assert(pok(x, p) && pok(y, p));
    simp_bitwise_decode(gb(x, 2 * p), gb(x, 2 * p + 1), gb(y, 2 * p), gb(y, 2 * p + 1));
}

/// OR of two well-formed packed traces is well formed and is
/// `WEST_simp_trace` of the two.
pub proof fn or_w_correct(x: Seq<u64>, y: Seq<u64>, n: nat, len: nat)
    requires
        n >= 1,
        twf(x, n, len),
        twf(y, n, len),
    ensures
        twf(or_w(x, y), n, len),
        tr(or_w(x, y), n, len) == WEST_simp_trace_spec(tr(x, n, len), tr(y, n, len), n),
{
    let z = or_w(x, y);
    let w = x.len();
    lemma_words_for(n, len);
    assert forall|p: int| 0 <= p < n * len implies #[trigger] pok(z, p) by {
        or_pair(x, y, n, len, p);
    }
    assert forall|q: int| 2 * n * len <= q < 64 * z.len() implies #[trigger] gb(z, q) by {
        gb_or(x, y, q);
        assert(gb(x, q));
    }
    let tx = tr(x, n, len);
    let ty = tr(y, n, len);
    let m = WEST_simp_trace_spec(tx, ty, n);
    assert forall|t: int| 0 <= t < len implies #[trigger] m[t] == tr(z, n, len)[t] by {
        assert forall|v: int| 0 <= v < n implies m[t][v] == tr(z, n, len)[t][v] by {
            lemma_grid_bound(n, len, t, v);
            or_pair(x, y, n, len, n * t + v);
        }
        assert(m[t] =~= tr(z, n, len)[t]);
    }
    assert(m =~= tr(z, n, len));
}

// ---------------------------------------------------------------------------
// The difference test implies check_simp
// ---------------------------------------------------------------------------

proof fn bit_nonzero(e: u64, i: u64)
    requires
        i < 64,
        bit(e, i as int),
    ensures
        e != 0,
{
    assert(((e >> i) & 1u64) == 1u64 ==> e != 0u64) by (bit_vector)
        requires i < 64u64;
}

/// Equal-length states that differ at most at index `i0` have
/// `count_diff_state ≤ 1`; with no difference, 0.
proof fn count_diff_state_unique(s1: StateRegex, s2: StateRegex, i0: int)
    requires
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() && i != i0 ==> #[trigger] s1[i] == s2[i],
    ensures
        count_diff_state(s1, s2) <= 1,
        (0 <= i0 < s1.len() ==> s1[i0] == s2[i0]) ==> count_diff_state(s1, s2) == 0,
    decreases s1.len(),
{
    if s1.len() > 0 {
        let t1 = s1.drop_first();
        let t2 = s2.drop_first();
        assert forall|i: int| 0 <= i < t1.len() && i != i0 - 1 implies #[trigger] t1[i] == t2[i] by {
            assert(t1[i] == s1[i + 1] && t2[i] == s2[i + 1]);
        }
        count_diff_state_unique(t1, t2, i0 - 1);
        if i0 != 0 {
            assert(s1[0] == s2[0]);
            if 0 <= i0 - 1 < t1.len() {
                assert(t1[i0 - 1] == s1[i0] && t2[i0 - 1] == s2[i0]);
            }
        }
    }
}

/// Equal-shape regexes whose entries differ at most at `(k0, i0)` pass
/// `check_simp`.
proof fn check_simp_unique(t1: TraceRegex, t2: TraceRegex, n: nat, k0: int, i0: int)
    requires
        t1.len() == t2.len(),
        trace_regex_of_vars(t1, n),
        trace_regex_of_vars(t2, n),
        forall|k: int, i: int| 0 <= k < t1.len() && 0 <= i < n && (k != k0 || i != i0) ==>
            #[trigger] t1[k][i] == t2[k][i],
    ensures
        count_diff(t1, t2) <= 1,
        (forall|k: int, i: int| 0 <= k < t1.len() && 0 <= i < n ==> #[trigger] t1[k][i] == t2[k][i])
            ==> count_diff(t1, t2) == 0,
        check_simp_spec(t1, t2),
    decreases t1.len(),
{
    if t1.len() > 0 {
        let r1 = t1.drop_first();
        let r2 = t2.drop_first();
        assert(trace_regex_of_vars(r1, n) && trace_regex_of_vars(r2, n)) by {
            assert forall|i: int| 0 <= i < r1.len() implies (#[trigger] r1[i]).len() == n by { assert(r1[i] == t1[i + 1]); }
            assert forall|i: int| 0 <= i < r2.len() implies (#[trigger] r2[i]).len() == n by { assert(r2[i] == t2[i + 1]); }
        }
        assert forall|k: int, i: int| 0 <= k < r1.len() && 0 <= i < n && (k != k0 - 1 || i != i0) implies
            #[trigger] r1[k][i] == r2[k][i] by {
            assert(r1[k] == t1[k + 1] && r2[k] == t2[k + 1]);
            assert(t1[k + 1][i] == t2[k + 1][i]);
        }
        check_simp_unique(r1, r2, n, k0 - 1, i0);
        assert(t1[0].len() == n && t2[0].len() == n);
        let i0s = if k0 == 0 { i0 } else { -1 };
        assert forall|i: int| 0 <= i < t1[0].len() && i != i0s implies #[trigger] t1[0][i] == t2[0][i] by {
            assert(t1[0][i] == t2[0][i]);
        }
        count_diff_state_unique(t1[0], t2[0], i0s);
        if k0 != 0 {
            assert(count_diff_state(t1[0], t2[0]) == 0);
            // the rest differ at most once
        } else {
            // the rest do not differ at all
            assert forall|k: int, i: int| 0 <= k < r1.len() && 0 <= i < n implies #[trigger] r1[k][i] == r2[k][i] by {
                assert(r1[k] == t1[k + 1] && r2[k] == t2[k + 1]);
                assert(t1[k + 1][i] == t2[k + 1][i]);
            }
        }
        if forall|k: int, i: int| 0 <= k < t1.len() && 0 <= i < n ==> #[trigger] t1[k][i] == t2[k][i] {
            assert forall|k: int, i: int| 0 <= k < r1.len() && 0 <= i < n implies #[trigger] r1[k][i] == r2[k][i] by {
                assert(r1[k] == t1[k + 1] && r2[k] == t2[k + 1]);
                assert(t1[k + 1][i] == t2[k + 1][i]);
            }
            assert(count_diff_state(t1[0], t2[0]) == 0) by {
                assert forall|i: int| 0 <= i < t1[0].len() && i != -1 implies #[trigger] t1[0][i] == t2[0][i] by {
                    assert(t1[0][i] == t2[0][i]);
                }
                count_diff_state_unique(t1[0], t2[0], -1);
            }
        }
    }
}

/// Packed traces passing the difference test give `check_simp`.
pub proof fn one_diff_check_simp(x: Seq<u64>, y: Seq<u64>, n: nat, len: nat)
    requires
        n >= 1,
        twf(x, n, len),
        twf(y, n, len),
        one_diff(x, y),
    ensures
        check_simp_spec(tr(x, n, len), tr(y, n, len)),
{
    let tx = tr(x, n, len);
    let ty = tr(y, n, len);
    let w = x.len();
    lemma_words_for(n, len);
    // A differing used pair sets its bit in its word's difference mask.
    assert forall|p: int| 0 <= p < n * len && #[trigger] pentry(x, p) != pentry(y, p) implies
        bit(diff_mask(x[p / 32], y[p / 32]), 2 * (p % 32)) by {
        pair_in_words(n, len, w, p);
        lemma_pair_pos(p);
        lemma_mod_bound(p, 32);
        assert(pok(x, p) && pok(y, p));
        lemma_decode_inj(gb(x, 2 * p), gb(x, 2 * p + 1), gb(y, 2 * p), gb(y, 2 * p + 1));
        let o = (p % 32) as u64;
        lemma_bit_xor(x[p / 32], y[p / 32], (2 * o) as u64);
        lemma_bit_xor(x[p / 32], y[p / 32], (2 * o + 1) as u64);
        lemma_pair_diff(x[p / 32] ^ y[p / 32], o);
    }
    // So at most one used pair differs.
    assert forall|p1: int, p2: int| 0 <= p1 < n * len && 0 <= p2 < n * len
        && #[trigger] pentry(x, p1) != pentry(y, p1) && #[trigger] pentry(x, p2) != pentry(y, p2) implies p1 == p2 by {
        pair_in_words(n, len, w, p1);
        pair_in_words(n, len, w, p2);
        lemma_mod_bound(p1, 32);
        lemma_mod_bound(p2, 32);
        let (k1, k2) = (p1 / 32, p2 / 32);
        let (o1, o2) = ((p1 % 32) as u64, (p2 % 32) as u64);
        bit_nonzero(diff_mask(x[k1], y[k1]), (2 * o1) as u64);
        bit_nonzero(diff_mask(x[k2], y[k2]), (2 * o2) as u64);
        if k1 < k2 {
            assert(diff_mask(x[k1], y[k1]) == 0 || diff_mask(x[k2], y[k2]) == 0);
        } else if k2 < k1 {
            assert(diff_mask(x[k2], y[k2]) == 0 || diff_mask(x[k1], y[k1]) == 0);
        } else {
            let e = diff_mask(x[k1], y[k1]);
            assert(e == 0 || e & sub(e, 1u64) == 0);
            if o1 < o2 {
                lemma_at_most_one_bit(e, (2 * o1) as u64, (2 * o2) as u64);
            } else if o2 < o1 {
                lemma_at_most_one_bit(e, (2 * o2) as u64, (2 * o1) as u64);
            }
            lemma_fundamental_div_mod(p1, 32);
            lemma_fundamental_div_mod(p2, 32);
        }
    }
    lemma_tr_of_vars(x, n, len);
    lemma_tr_of_vars(y, n, len);
    if exists|p: int| 0 <= p < n * len && #[trigger] pentry(x, p) != pentry(y, p) {
        let p0 = choose|p: int| 0 <= p < n * len && #[trigger] pentry(x, p) != pentry(y, p);
        lemma_grid(n, len, p0);
        let (k0, i0) = (p0 / (n as int), p0 % (n as int));
        assert forall|k: int, i: int| 0 <= k < tx.len() && 0 <= i < n && (k != k0 || i != i0) implies
            #[trigger] tx[k][i] == ty[k][i] by {
            lemma_grid_bound(n, len, k, i);
            let p = n * k + i;
            if pentry(x, p) != pentry(y, p) {
                assert(p == p0);
                lemma_fundamental_div_mod_converse(p, n as int, k, i);
            }
        }
        check_simp_unique(tx, ty, n, k0, i0);
    } else {
        assert forall|k: int, i: int| 0 <= k < tx.len() && 0 <= i < n && (k != -1 || i != -1) implies
            #[trigger] tx[k][i] == ty[k][i] by {
            lemma_grid_bound(n, len, k, i);
            assert(pentry(x, n * k + i) == pentry(y, n * k + i));
        }
        check_simp_unique(tx, ty, n, -1, -1);
    }
}

// ---------------------------------------------------------------------------
// Shift = prepend all-S states
// ---------------------------------------------------------------------------

/// Word `i` of `x`, all ones outside `x`.
pub open spec fn getw(x: Seq<u64>, i: int) -> u64 {
    if 0 <= i < x.len() { x[i] } else { !0u64 }
}

/// Bit `q` of `x`, 1 outside `x`.
pub open spec fn gbx(x: Seq<u64>, q: int) -> bool {
    if 0 <= q < 64 * x.len() { gb(x, q) } else { true }
}

/// Word `j` of `x` moved up by `64·ws + bs` bits, ones shifted in.
pub open spec fn shift_word(x: Seq<u64>, j: int, ws: int, bs: u64) -> u64 {
    if bs == 0 {
        getw(x, j - ws)
    } else {
        (getw(x, j - ws) << bs) | (getw(x, j - ws - 1) >> sub(64u64, bs))
    }
}

/// `x` (`len` states) delayed by `k` states.
pub open spec fn shift_w(x: Seq<u64>, n: nat, len: nat, k: nat) -> Seq<u64> {
    let s = 2 * n * k;
    Seq::new(words_for(n, len + k), |j: int| shift_word(x, j, (s / 64) as int, (s % 64) as u64))
}

proof fn getw_bit(x: Seq<u64>, i: int, r: int)
    requires
        0 <= r < 64,
    ensures
        bit(getw(x, i), r) == gbx(x, 64 * i + r),
{
    lemma_fundamental_div_mod_converse(64 * i + r, 64, i, r);
    if !(0 <= i < x.len()) {
        lemma_bit_ones(r as u64);
    }
}

/// Bit `q` of the shifted words is 1 below the shift and the old bit above.
proof fn shift_bit(x: Seq<u64>, n: nat, len: nat, k: nat, q: int)
    requires
        0 <= q < 64 * words_for(n, len + k),
    ensures
        gb(shift_w(x, n, len, k), q) == if q < 2 * n * k { true } else { gbx(x, q - 2 * n * k) },
{
    let s = (2 * n * k) as int;
    let ws = s / 64;
    let bs = (s % 64) as u64;
    lemma_fundamental_div_mod(s, 64);
    lemma_mod_bound(s, 64);
    lemma_fundamental_div_mod(q, 64);
    lemma_mod_bound(q, 64);
    lemma_div_pos_is_pos(q, 64);
    div_lt(q, 64, words_for(n, len + k) as int);
    let j = q / 64;
    let r = q % 64;
    let wd = shift_word(x, j, ws, bs);
    assert(shift_w(x, n, len, k)[j] == wd);
    if bs == 0 {
        getw_bit(x, j - ws, r);
        assert(64 * (j - ws) + r == q - s);
    } else {
        lemma_shift_carry(getw(x, j - ws), getw(x, j - ws - 1), bs, r as u64);
        if r >= bs {
            getw_bit(x, j - ws, r - bs);
            assert(64 * (j - ws) + (r - bs) == q - s);
        } else {
            getw_bit(x, j - ws - 1, 64 - bs + r);
            assert(64 * (j - ws - 1) + (64 - bs + r) == q - s);
        }
    }
    // gbx is 1 at negative positions, which are exactly q < s.
}

/// Pair `p` of the shifted words: below the shift both bits are 1; above,
/// the old pair `p - n·k`.
proof fn shift_pair(x: Seq<u64>, n: nat, len: nat, k: nat, p: int)
    requires
        n >= 1,
        twf(x, n, len),
        0 <= p < n * (len + k),
    ensures
        p < n * k ==> gb(shift_w(x, n, len, k), 2 * p) && gb(shift_w(x, n, len, k), 2 * p + 1),
        p >= n * k ==> 0 <= p - n * k < n * len
            && gb(shift_w(x, n, len, k), 2 * p) == gb(x, 2 * (p - n * k))
            && gb(shift_w(x, n, len, k), 2 * p + 1) == gb(x, 2 * (p - n * k) + 1),
{
    let z = shift_w(x, n, len, k);
    assert(n * (len + k) == n * len + n * k) by (nonlinear_arith);
    assert(2 * n * k == 2 * (n * k)) by (nonlinear_arith);
    pair_in_words(n, (len + k) as nat, z.len(), p);
    assert(z.len() == words_for(n, len + k));
    shift_bit(x, n, len, k, 2 * p);
    shift_bit(x, n, len, k, 2 * p + 1);
    if p >= n * k {
        pair_in_words(n, len, x.len(), p - n * k);
    }
}

/// Shifting by `k` prepends `k` all-`S` states (Isabelle `shift`).
pub proof fn shift_w_correct(x: Seq<u64>, n: nat, len: nat, k: nat)
    requires
        n >= 1,
        twf(x, n, len),
    ensures
        twf(shift_w(x, n, len, k), n, len + k),
        tr(shift_w(x, n, len, k), n, (len + k) as nat) == arbitrary_trace(n, k) + tr(x, n, len),
{
    let z = shift_w(x, n, len, k);
    let s = 2 * n * k;
    lemma_words_for(n, len);
    lemma_words_for(n, len + k);
    assert(2 * n * (len + k) == 2 * n * len + s) by (nonlinear_arith) requires s == 2 * n * k;
    assert(n * (len + k) == n * len + n * k) by (nonlinear_arith);
    assert(s == 2 * (n * k)) by (nonlinear_arith) requires s == 2 * n * k;
    assert forall|p: int| 0 <= p < n * (len + k) implies #[trigger] pok(z, p) by {
        shift_pair(x, n, len, k, p);
        if p >= n * k {
            assert(pok(x, p - n * k));
        }
    }
    assert forall|q: int| 2 * n * (len + k) <= q < 64 * z.len() implies #[trigger] gb(z, q) by {
        shift_bit(x, n, len, k, q);
        if q - s < 64 * x.len() {
            assert(gb(x, q - s));
        }
    }
    let lhs = tr(z, n, (len + k) as nat);
    let rhs = arbitrary_trace(n, k) + tr(x, n, len);
    assert forall|t: int| 0 <= t < len + k implies #[trigger] lhs[t] == rhs[t] by {
        assert forall|v: int| 0 <= v < n implies lhs[t][v] == rhs[t][v] by {
            lemma_grid_bound(n, (len + k) as nat, t, v);
            let p = n * t + v;
            shift_pair(x, n, len, k, p);
            if t < k {
                assert(p < n * k) by (nonlinear_arith) requires t < k, v < n, p == n * t + v, t >= 0;
                assert(rhs[t] == arbitrary_state(n));
            } else {
                assert(p - n * k == n * (t - k) + v) by (nonlinear_arith) requires p == n * t + v;
                assert(p >= n * k) by (nonlinear_arith) requires t >= k, v >= 0, p == n * t + v;
                lemma_grid_bound(n, len, t - k, v);
                assert(rhs[t] == tr(x, n, len)[t - k]);
            }
        }
        assert(lhs[t] =~= rhs[t]);
    }
    assert(lhs =~= rhs);
}

// ---------------------------------------------------------------------------
// Pad = append all-S states
// ---------------------------------------------------------------------------

/// `x` extended to `w2` words with all-ones words.
pub open spec fn pad_w(x: Seq<u64>, w2: nat) -> Seq<u64> {
    x + Seq::new((w2 - x.len()) as nat, |i: int| !0u64)
}

proof fn pad_bit(x: Seq<u64>, w2: nat, q: int)
    requires
        x.len() <= w2,
        0 <= q < 64 * w2,
    ensures
        gb(pad_w(x, w2), q) == gbx(x, q),
{
    lemma_div_pos_is_pos(q, 64);
    div_lt(q, 64, w2 as int);
    lemma_mod_bound(q, 64);
    if q < 64 * x.len() {
        div_lt(q, 64, x.len() as int);
    } else {
        if q / 64 < x.len() {
            lemma_fundamental_div_mod(q, 64);
        }
        lemma_bit_ones((q % 64) as u64);
    }
}

/// Padding to `len2 ≥ len` states appends all-`S` states (Isabelle `pad`).
pub proof fn pad_w_correct(x: Seq<u64>, n: nat, len: nat, len2: nat)
    requires
        n >= 1,
        len <= len2,
        twf(x, n, len),
    ensures
        twf(pad_w(x, words_for(n, len2)), n, len2),
        tr(pad_w(x, words_for(n, len2)), n, len2) == pad_spec(tr(x, n, len), n, (len2 - len) as nat),
{
    let w2 = words_for(n, len2);
    let z = pad_w(x, w2);
    lemma_words_for(n, len);
    lemma_words_for(n, len2);
    assert(x.len() <= w2) by {
        assert(2 * n * len <= 2 * n * len2) by (nonlinear_arith) requires len <= len2;
        lemma_div_is_ordered((2 * n * len + 63) as int, (2 * n * len2 + 63) as int, 64);
    }
    assert(n * len <= n * len2) by (nonlinear_arith) requires len <= len2;
    assert(2 * n * len == 2 * (n * len)) by (nonlinear_arith);
    assert(2 * n * len2 == 2 * (n * len2)) by (nonlinear_arith);
    assert forall|p: int| 0 <= p < n * len2 implies #[trigger] pok(z, p) && (p >= n * len ==> gb(z, 2 * p) && gb(z, 2 * p + 1))
        && (p < n * len ==> pentry(z, p) == pentry(x, p)) by {
        pair_in_words(n, len2, w2, p);
        pad_bit(x, w2, 2 * p);
        pad_bit(x, w2, 2 * p + 1);
        if p < n * len {
            pair_in_words(n, len, x.len(), p);
            assert(pok(x, p));
        } else if 2 * p < 64 * x.len() {
            assert(gb(x, 2 * p));
            if 2 * p + 1 < 64 * x.len() {
                assert(gb(x, 2 * p + 1));
            }
        }
    }
    assert forall|q: int| 2 * n * len2 <= q < 64 * z.len() implies #[trigger] gb(z, q) by {
        pad_bit(x, w2, q);
        if q < 64 * x.len() {
            assert(gb(x, q));
        }
    }
    let lhs = tr(z, n, len2);
    let rhs = pad_spec(tr(x, n, len), n, (len2 - len) as nat);
    assert forall|t: int| 0 <= t < len2 implies #[trigger] lhs[t] == rhs[t] by {
        assert forall|v: int| 0 <= v < n implies lhs[t][v] == rhs[t][v] by {
            lemma_grid_bound(n, len2, t, v);
            let p = n * t + v;
            assert(pok(z, p));
            if t < len {
                lemma_grid_bound(n, len, t, v);
                assert(rhs[t] == tr(x, n, len)[t]);
            } else {
                assert(p >= n * len) by (nonlinear_arith) requires t >= len, v >= 0, p == n * t + v;
                assert(rhs[t] == arbitrary_state(n));
            }
        }
        assert(lhs[t] =~= rhs[t]);
    }
    assert(lhs =~= rhs);
}

// ---------------------------------------------------------------------------
// One-state regexes
// ---------------------------------------------------------------------------

/// All-ones word with pair `o` set to `bits` (`1` = Zero, `2` = One, `3` = S).
pub open spec fn set_pair(o: u64, bits: u64) -> u64 {
    (!0u64 & !(3u64 << mul(2u64, o))) | (bits << mul(2u64, o))
}

/// One state of `n` atoms: `S` except atom `p`, which reads `bits`.
pub open spec fn single_w(n: nat, p: nat, bits: u64) -> Seq<u64> {
    Seq::new(words_for(n, 1), |k: int| if k == p / 32 { set_pair((p % 32) as u64, bits) } else { !0u64 })
}

pub proof fn single_w_correct(n: nat, p: nat, bits: u64)
    requires
        n >= 1,
        p < n,
        1 <= bits <= 3,
    ensures
        twf(single_w(n, p, bits), n, 1),
        tr(single_w(n, p, bits), n, 1)
            == seq![Seq::new(n, |j: int| if p as int == j { decode(bits & 1 == 1, bits & 2 == 2) } else { WestBit::S })],
{
    let z = single_w(n, p, bits);
    let w = words_for(n, 1);
    lemma_words_for(n, 1);
    assert(n * 1 == n);
    assert(2 * n * 1 == 2 * n);
    assert forall|q: int| 0 <= q < 64 * w implies #[trigger] gb(z, q)
        == if q == 2 * p { bits & 1 == 1 } else if q == 2 * p + 1 { bits & 2 == 2 } else { true } by {
        lemma_div_pos_is_pos(q, 64);
        div_lt(q, 64, w as int);
        lemma_mod_bound(q, 64);
        lemma_fundamental_div_mod(q, 64);
        lemma_pair_pos(p as int);
        lemma_mod_bound(p as int, 32);
        if q / 64 == p / 32 {
            lemma_set_pair(bits, (p % 32) as u64, (q % 64) as u64);
        } else {
            lemma_bit_ones((q % 64) as u64);
        }
    }
    assert forall|pp: int| 0 <= pp < n * 1 implies #[trigger] pok(z, pp) by {
        pair_in_words(n, 1, w, pp);
        assert(bits & 1 == 1 || bits & 2 == 2) by (bit_vector) requires 1u64 <= bits, bits <= 3u64;
    }
    assert forall|q: int| 2 * n * 1 <= q < 64 * z.len() implies #[trigger] gb(z, q) by {}
    let lhs = tr(z, n, 1);
    let rhs = seq![Seq::new(n, |j: int| if p as int == j { decode(bits & 1 == 1, bits & 2 == 2) } else { WestBit::S })];
    assert forall|v: int| 0 <= v < n implies lhs[0][v] == rhs[0][v] by {
        pair_in_words(n, 1, w, v);
    }
    assert(lhs[0] =~= rhs[0]);
    assert(lhs =~= rhs);
}

/// All-`S` single state.
pub open spec fn ones_w(w: nat) -> Seq<u64> {
    Seq::new(w, |k: int| !0u64)
}

pub proof fn ones_w_correct(n: nat, len: nat)
    requires
        n >= 1,
    ensures
        twf(ones_w(words_for(n, len)), n, len),
        tr(ones_w(words_for(n, len)), n, len) == arbitrary_trace(n, len),
{
    let w = words_for(n, len);
    let z = ones_w(w);
    lemma_words_for(n, len);
    assert forall|q: int| 0 <= q < 64 * w implies #[trigger] gb(z, q) by {
        lemma_div_pos_is_pos(q, 64);
        div_lt(q, 64, w as int);
        lemma_mod_bound(q, 64);
        lemma_bit_ones((q % 64) as u64);
    }
    assert(2 * n * len == 2 * (n * len)) by (nonlinear_arith);
    assert forall|p: int| 0 <= p < n * len implies #[trigger] pok(z, p) by {
        pair_in_words(n, len, w, p);
    }
    let lhs = tr(z, n, len);
    let rhs = arbitrary_trace(n, len);
    assert forall|t: int| 0 <= t < len implies #[trigger] lhs[t] == rhs[t] by {
        assert forall|v: int| 0 <= v < n implies lhs[t][v] == rhs[t][v] by {
            lemma_grid_bound(n, len, t, v);
            pair_in_words(n, len, w, n * t + v);
            assert(gb(z, 2 * (n * t + v)) && gb(z, 2 * (n * t + v) + 1));
            lemma_tr_entry(z, n, len, t, v);
            assert(rhs[t] == arbitrary_state(n));
            assert(rhs[t][v] == WestBit::S);
        }
        assert(lhs[t] =~= rhs[t]);
    }
    assert(lhs =~= rhs);
}

} // verus!
