//! Fast WEST: packed trace regexes, proved *equivalent* to WEST (D43).
//!
//! Same structure as `WEST_reg`, but each regex list has one length (its
//! traces are padded with `S` to a common length before AND/OR), traces are
//! packed 2 bits per atom per step (`packed.rs`), and simplification merges
//! pairs in any order until no pair merges. The result is not Isabelle's
//! list, but every trace at least `complen φ` long matches it exactly when
//! it satisfies `φ` (`fast_reg`).
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithms::*;
use crate::bits::*;
use crate::matching::*;
use crate::simp::*;
use crate::temporal::*;
use crate::correct::*;
use crate::packed::*;
use crate::packed_ops::*;
use crate::exec::*;

verus! {

/// A list of packed trace regexes, all `len` states of `n` atoms
/// (`w` words each).
pub struct Packed {
    pub n: usize,
    pub len: usize,
    pub w: usize,
    pub traces: Vec<Vec<u64>>,
}

/// Lengths up to `len` fit the word arithmetic.
pub open spec fn fits(n: nat, len: nat) -> bool {
    2 * n * len + 64 <= usize::MAX
}

/// Well-formed packed list.
pub open spec fn pwf(r: Packed) -> bool {
    &&& r.n >= 1
    &&& r.len >= 1
    &&& fits(r.n as nat, r.len as nat)
    &&& r.w == words_for(r.n as nat, r.len as nat)
    &&& forall|i: int| 0 <= i < r.traces.len() ==> twf(#[trigger] r.traces@[i]@, r.n as nat, r.len as nat)
}

pub open spec fn tview_p(x: Vec<u64>, n: nat, len: nat) -> TraceRegex {
    tr(x@, n, len)
}

/// The regex list a packed list stands for.
pub open spec fn pview(r: Packed) -> WestRegex {
    r.traces@.map_values(|x: Vec<u64>| tview_p(x, r.n as nat, r.len as nat))
}

/// Every regex of the list has `n`-wide states and length `len`.
pub proof fn pview_facts(r: Packed)
    requires
        pwf(r),
    ensures
        WEST_regex_of_vars(pview(r), r.n as nat),
        pview(r).len() == r.traces.len(),
        forall|i: int| 0 <= i < pview(r).len() ==> (#[trigger] pview(r)[i]).len() == r.len,
{
    assert forall|i: int| 0 <= i < pview(r).len() implies trace_regex_of_vars(#[trigger] pview(r)[i], r.n as nat) by {
        lemma_tr_of_vars(r.traces@[i]@, r.n as nat, r.len as nat);
    }
}

/// Padding every regex of a list to `len2` keeps the matching traces at
/// least `len2` long.
pub proof fn pad_all_match(pi: WestTrace, l: WestRegex, n: nat, len: nat, len2: nat)
    requires
        len <= len2,
        pi.len() >= len2,
        forall|i: int| 0 <= i < l.len() ==> (#[trigger] l[i]).len() == len,
    ensures
        west_match(pi, l.map_values(|t: TraceRegex| pad_spec(t, n, (len2 - len) as nat))) <==> west_match(pi, l),
{
    let lp = l.map_values(|t: TraceRegex| pad_spec(t, n, (len2 - len) as nat));
    if west_match(pi, lp) {
        let i = choose|i: int| 0 <= i < lp.len() && #[trigger] match_regex(pi, lp[i]);
        pad_match(pi, l[i], n, (len2 - len) as nat);
    }
    if west_match(pi, l) {
        let i = choose|i: int| 0 <= i < l.len() && #[trigger] match_regex(pi, l[i]);
        pad_match(pi, l[i], n, (len2 - len) as nat);
        assert(match_regex(pi, lp[i]));
    }
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

pub fn words_for_exec(n: usize, len: usize) -> (r: usize)
    requires
        len >= 1,
        2 * n * len + 63 <= usize::MAX,
    ensures
        r == words_for(n as nat, len as nat),
{
    assert(2 * n <= 2 * n * len) by (nonlinear_arith) requires len >= 1;
    (2 * n * len + 63) / 64
}

/// The empty list (`False`), length 1.
pub fn p_false(n: usize) -> (r: Packed)
    requires
        n >= 1,
        fits(n as nat, 1),
    ensures
        pwf(r),
        r.n == n,
        r.len == 1,
        pview(r) == WEST_reg_aux_spec(Mltl::False, n as nat),
{
    let r = Packed { n, len: 1, w: words_for_exec(n, 1), traces: Vec::new() };
    assert(pview(r) =~= Seq::<TraceRegex>::empty());
    r
}

/// The all-`S` one-state regex (`True`).
pub fn p_true(n: usize) -> (r: Packed)
    requires
        n >= 1,
        fits(n as nat, 1),
    ensures
        pwf(r),
        r.n == n,
        r.len == 1,
        pview(r) == WEST_reg_aux_spec(Mltl::True, n as nat),
{
    let w = words_for_exec(n, 1);
    let mut x: Vec<u64> = Vec::with_capacity(w);
    let mut k: usize = 0;
    while k < w
        invariant
            k <= w,
            x@ == ones_w(k as nat),
        decreases w - k,
    {
        x.push(!0u64);
        k += 1;
        assert(x@ =~= ones_w(k as nat));
    }
    proof { ones_w_correct(n as nat, 1); }
    let mut traces: Vec<Vec<u64>> = Vec::new();
    traces.push(x);
    let r = Packed { n, len: 1, w, traces };
    proof {
        assert(arbitrary_trace(n as nat, 1) =~= seq![Seq::new(n as nat, |j: int| WestBit::S)]);
        assert(pview(r) =~= seq![tr(x@, n as nat, 1)]);
    }
    r
}

/// The one-state regex with atom `p` `One` (`positive`) or `Zero`.
pub fn p_literal(n: usize, p: usize, positive: bool) -> (r: Packed)
    requires
        p < n,
        fits(n as nat, 1),
    ensures
        pwf(r),
        r.n == n,
        r.len == 1,
        positive ==> pview(r) == WEST_reg_aux_spec(Mltl::Prop(p), n as nat),
        !positive ==> pview(r) == WEST_reg_aux_spec(Mltl::Not(Box::new(Mltl::Prop(p))), n as nat),
{
    let w = words_for_exec(n, 1);
    let bits: u64 = if positive { 2 } else { 1 };
    let o: u64 = (p % 32) as u64;
    assert(o < 32);
    let mut x: Vec<u64> = Vec::with_capacity(w);
    let mut k: usize = 0;
    while k < w
        invariant
            k <= w,
            w == words_for(n as nat, 1),
            o < 32,
            o == (p % 32) as u64,
            x@ == single_w(n as nat, p as nat, bits).subrange(0, k as int),
        decreases w - k,
    {
        if k == p / 32 {
            x.push((!0u64 & !(3u64 << (2 * o))) | (bits << (2 * o)));
        } else {
            x.push(!0u64);
        }
        k += 1;
        assert(x@ =~= single_w(n as nat, p as nat, bits).subrange(0, k as int));
    }
    assert(x@ =~= single_w(n as nat, p as nat, bits));
    proof {
        single_w_correct(n as nat, p as nat, bits);
        assert(bits & 1 == 1 <==> !positive) by (bit_vector) requires bits == 2u64 || bits == 1u64, positive <==> bits == 2u64;
        assert(bits & 2 == 2 <==> positive) by (bit_vector) requires bits == 2u64 || bits == 1u64, positive <==> bits == 2u64;
    }
    let mut traces: Vec<Vec<u64>> = Vec::new();
    traces.push(x);
    let r = Packed { n, len: 1, w, traces };
    proof {
        reveal_with_fuel(WEST_reg_aux_spec, 2);
        assert(pview(r) =~= seq![tr(x@, n as nat, 1)]);
        if positive {
            assert(tr(x@, n as nat, 1)[0] =~= Seq::new(n as nat, |j: int| if p as int == j { WestBit::One } else { WestBit::S }));
        } else {
            assert(tr(x@, n as nat, 1)[0] =~= Seq::new(n as nat, |j: int| if p as int == j { WestBit::Zero } else { WestBit::S }));
        }
    }
    r
}

// ---------------------------------------------------------------------------
// Shift and pad
// ---------------------------------------------------------------------------

fn shift_trace(x: &Vec<u64>, n: usize, len: usize, k: usize, w2: usize) -> (t: Vec<u64>)
    requires
        len >= 1,
        x@.len() == words_for(n as nat, len as nat),
        w2 == words_for(n as nat, (len + k) as nat),
        fits(n as nat, (len + k) as nat),
    ensures
        t@ == shift_w(x@, n as nat, len as nat, k as nat),
{
    assert(2 * n * k <= 2 * n * (len + k)) by (nonlinear_arith);
    assert(2 * n <= 2 * n * (len + k)) by (nonlinear_arith) requires len >= 1;
    let s = 2 * n * k;
    let ws = s / 64;
    let bs: u64 = (s % 64) as u64;
    let w = x.len();
    let mut t: Vec<u64> = Vec::with_capacity(w2);
    let mut j: usize = 0;
    while j < w2
        invariant
            j <= w2,
            w == x@.len(),
            s == 2 * n * k,
            ws == s / 64,
            bs == s % 64,
            w2 == words_for(n as nat, (len + k) as nat),
            t@ == shift_w(x@, n as nat, len as nat, k as nat).subrange(0, j as int),
        decreases w2 - j,
    {
        let hi = if j >= ws && j - ws < w { x[j - ws] } else { !0u64 };
        let v = if bs == 0 {
            hi
        } else {
            let lo = if j >= ws + 1 && j - ws - 1 < w { x[j - ws - 1] } else { !0u64 };
            (hi << bs) | (lo >> (64 - bs))
        };
        proof {
            assert(hi == getw(x@, j - ws));
            if bs != 0 {
                assert(sub(64u64, bs) == 64 - bs);
            }
            assert(v == shift_word(x@, j as int, ws as int, bs));
        }
        t.push(v);
        j += 1;
        assert(t@ =~= shift_w(x@, n as nat, len as nat, k as nat).subrange(0, j as int));
    }
    assert(t@ =~= shift_w(x@, n as nat, len as nat, k as nat));
    t
}

/// `shift L n k`: every regex delayed by `k` states.
pub fn p_shift(r: &Packed, k: usize) -> (out: Packed)
    requires
        pwf(*r),
        fits(r.n as nat, (r.len + k) as nat),
    ensures
        pwf(out),
        out.n == r.n,
        out.len == r.len + k,
        pview(out) == shift_spec(pview(*r), r.n as nat, k as nat),
{
    let n = r.n;
    assert(r.len + k <= 2 * n * (r.len + k)) by (nonlinear_arith) requires n >= 1;
    let len2 = r.len + k;
    let w2 = words_for_exec(n, len2);
    let mut ts: Vec<Vec<u64>> = Vec::with_capacity(r.traces.len());
    let mut i: usize = 0;
    while i < r.traces.len()
        invariant
            pwf(*r),
            n == r.n,
            len2 == r.len + k,
            w2 == words_for(n as nat, len2 as nat),
            fits(n as nat, len2 as nat),
            i <= r.traces.len(),
            ts.len() == i,
            forall|m: int| 0 <= m < i ==> twf(#[trigger] ts@[m]@, n as nat, len2 as nat)
                && tr(ts@[m]@, n as nat, len2 as nat) == arbitrary_trace(n as nat, k as nat) + tr(r.traces@[m]@, n as nat, r.len as nat),
        decreases r.traces.len() - i,
    {
        assert(twf(r.traces@[i as int]@, n as nat, r.len as nat));
        let t = shift_trace(&r.traces[i], n, r.len, k, w2);
        proof { shift_w_correct(r.traces@[i as int]@, n as nat, r.len as nat, k as nat); }
        ts.push(t);
        i += 1;
    }
    let out = Packed { n, len: len2, w: w2, traces: ts };
    proof {
        let lhs = pview(out);
        let rhs = shift_spec(pview(*r), n as nat, k as nat);
        assert forall|m: int| 0 <= m < lhs.len() implies lhs[m] == rhs[m] by {
            assert(twf(ts@[m]@, n as nat, len2 as nat));
        }
        assert(lhs =~= rhs);
    }
    out
}

fn pad_trace(x: &Vec<u64>, w2: usize) -> (t: Vec<u64>)
    requires
        x@.len() <= w2,
    ensures
        t@ == pad_w(x@, w2 as nat),
{
    let mut t: Vec<u64> = Vec::with_capacity(w2);
    let mut j: usize = 0;
    while j < w2
        invariant
            j <= w2,
            x@.len() <= w2,
            t@ == pad_w(x@, w2 as nat).subrange(0, j as int),
        decreases w2 - j,
    {
        if j < x.len() {
            t.push(x[j]);
        } else {
            t.push(!0u64);
        }
        j += 1;
        assert(t@ =~= pad_w(x@, w2 as nat).subrange(0, j as int));
    }
    assert(t@ =~= pad_w(x@, w2 as nat));
    t
}

proof fn words_for_mono(n: nat, len: nat, len2: nat)
    requires
        len <= len2,
    ensures
        words_for(n, len) <= words_for(n, len2),
{
    assert(2 * n * len <= 2 * n * len2) by (nonlinear_arith) requires len <= len2;
    vstd::arithmetic::div_mod::lemma_div_is_ordered((2 * n * len + 63) as int, (2 * n * len2 + 63) as int, 64);
}

/// Every regex padded with all-`S` states to `len2` (a copy).
pub fn p_pad(r: &Packed, len2: usize) -> (out: Packed)
    requires
        pwf(*r),
        r.len <= len2,
        fits(r.n as nat, len2 as nat),
    ensures
        pwf(out),
        out.n == r.n,
        out.len == len2,
        pview(out) == pview(*r).map_values(|t: TraceRegex| pad_spec(t, r.n as nat, (len2 - r.len) as nat)),
{
    let n = r.n;
    let w2 = words_for_exec(n, len2);
    proof { words_for_mono(n as nat, r.len as nat, len2 as nat); }
    let mut ts: Vec<Vec<u64>> = Vec::with_capacity(r.traces.len());
    let mut i: usize = 0;
    while i < r.traces.len()
        invariant
            pwf(*r),
            n == r.n,
            r.len <= len2,
            w2 == words_for(n as nat, len2 as nat),
            r.w <= w2,
            i <= r.traces.len(),
            ts.len() == i,
            forall|m: int| 0 <= m < i ==> twf(#[trigger] ts@[m]@, n as nat, len2 as nat)
                && tr(ts@[m]@, n as nat, len2 as nat) == pad_spec(tr(r.traces@[m]@, n as nat, r.len as nat), n as nat, (len2 - r.len) as nat),
        decreases r.traces.len() - i,
    {
        assert(twf(r.traces@[i as int]@, n as nat, r.len as nat));
        let t = pad_trace(&r.traces[i], w2);
        proof { pad_w_correct(r.traces@[i as int]@, n as nat, r.len as nat, len2 as nat); }
        ts.push(t);
        i += 1;
    }
    let out = Packed { n, len: len2, w: w2, traces: ts };
    proof {
        let lhs = pview(out);
        let rhs = pview(*r).map_values(|t: TraceRegex| pad_spec(t, n as nat, (len2 - r.len) as nat));
        assert forall|m: int| 0 <= m < lhs.len() implies lhs[m] == rhs[m] by {
            assert(twf(ts@[m]@, n as nat, len2 as nat));
        }
        assert(lhs =~= rhs);
    }
    out
}

// ---------------------------------------------------------------------------
// AND (cross product) — exactly WEST_and on equal-length lists
// ---------------------------------------------------------------------------

fn and_trace_p(x: &Vec<u64>, y: &Vec<u64>) -> (r: Option<Vec<u64>>)
    requires
        x@.len() == y@.len(),
    ensures
        match r {
            Some(z) => z@ == and_w(x@, y@) && words_ok(z@),
            None => !words_ok(and_w(x@, y@)),
        },
{
    let mut z: Vec<u64> = Vec::with_capacity(x.len());
    let mut k: usize = 0;
    while k < x.len()
        invariant
            k <= x@.len(),
            x@.len() == y@.len(),
            z@ == and_w(x@, y@).subrange(0, k as int),
            forall|j: int| 0 <= j < k ==> #[trigger] word_ok(z@[j]),
        decreases x.len() - k,
    {
        let v = x[k] & y[k];
        if ((v | (v >> 1u64)) & LO) != LO {
            assert(!word_ok(and_w(x@, y@)[k as int]));
            return None;
        }
        z.push(v);
        k += 1;
        assert(z@ =~= and_w(x@, y@).subrange(0, k as int));
    }
    assert(z@ =~= and_w(x@, y@));
    Some(z)
}

/// `WEST_and` of two lists of the same length and width.
pub fn p_and_cross(a: &Packed, b: &Packed) -> (out: Packed)
    requires
        pwf(*a),
        pwf(*b),
        a.n == b.n,
        a.len == b.len,
    ensures
        pwf(out),
        out.n == a.n,
        out.len == a.len,
        pview(out) == WEST_and_spec(pview(*a), pview(*b)),
{
    let n = a.n;
    let len = a.len;
    let ghost v1 = pview(*a);
    let ghost v2 = pview(*b);
    let mut out: Vec<Vec<u64>> = Vec::new();
    let ghost mk = |ts: Seq<Vec<u64>>| ts.map_values(|x: Vec<u64>| tview_p(x, n as nat, len as nat));
    if b.traces.len() == 0 {
        let r = Packed { n, len, w: a.w, traces: out };
        assert(pview(r) =~= Seq::<TraceRegex>::empty());
        return r;
    }
    let mut i: usize = 0;
    assert(v1.skip(0) =~= v1);
    assert(mk(out@) + WEST_and_spec(v1.skip(0), v2) =~= WEST_and_spec(v1, v2));
    while i < a.traces.len()
        invariant
            pwf(*a),
            pwf(*b),
            n == a.n && n == b.n,
            len == a.len && len == b.len,
            i <= a.traces.len(),
            b.traces.len() > 0,
            v1 == pview(*a),
            v2 == pview(*b),
            mk == |ts: Seq<Vec<u64>>| ts.map_values(|x: Vec<u64>| tview_p(x, n as nat, len as nat)),
            forall|m: int| 0 <= m < out.len() ==> twf(#[trigger] out@[m]@, n as nat, len as nat),
            mk(out@) + WEST_and_spec(v1.skip(i as int), v2) == WEST_and_spec(v1, v2),
        decreases a.traces.len() - i,
    {
        proof { WEST_and_unfold(v1, v2, i as int); }
        let mut j: usize = 0;
        assert(v2.skip(0) =~= v2);
        assert(mk(out@) + WEST_and_helper_spec(v1[i as int], v2.skip(0)) + WEST_and_spec(v1.skip(i + 1), v2)
            =~= WEST_and_spec(v1, v2));
        while j < b.traces.len()
            invariant
                pwf(*a),
                pwf(*b),
                n == a.n && n == b.n,
                len == a.len && len == b.len,
                i < a.traces.len(),
                j <= b.traces.len(),
                v1 == pview(*a),
                v2 == pview(*b),
                mk == |ts: Seq<Vec<u64>>| ts.map_values(|x: Vec<u64>| tview_p(x, n as nat, len as nat)),
                forall|m: int| 0 <= m < out.len() ==> twf(#[trigger] out@[m]@, n as nat, len as nat),
                mk(out@) + WEST_and_helper_spec(v1[i as int], v2.skip(j as int)) + WEST_and_spec(v1.skip(i + 1), v2)
                    == WEST_and_spec(v1, v2),
            decreases b.traces.len() - j,
        {
            proof { WEST_and_helper_unfold(v1[i as int], v2, j as int); }
            let ghost before = mk(out@);
            let ghost rest = WEST_and_helper_spec(v1[i as int], v2.skip(j + 1));
            let ghost tail = WEST_and_spec(v1.skip(i + 1), v2);
            let ghost xs = a.traces@[i as int]@;
            let ghost ys = b.traces@[j as int]@;
            assert(twf(xs, n as nat, len as nat) && twf(ys, n as nat, len as nat));
            proof { and_w_correct(xs, ys, n as nat, len as nat); }
            match and_trace_p(&a.traces[i], &b.traces[j]) {
                None => {
                    assert(Seq::<TraceRegex>::empty() + rest =~= rest);
                },
                Some(z) => {
                    let ghost zv = tview_p(z, n as nat, len as nat);
                    out.push(z);
                    assert(mk(out@) =~= before + seq![zv]);
                    assert(before + (seq![zv] + rest) + tail =~= mk(out@) + rest + tail);
                },
            }
            j += 1;
        }
        assert(v2.skip(b.traces.len() as int) =~= Seq::<TraceRegex>::empty());
        assert(mk(out@) + Seq::<TraceRegex>::empty() =~= mk(out@));
        i += 1;
    }
    assert(v1.skip(a.traces.len() as int) =~= Seq::<TraceRegex>::empty());
    assert(mk(out@) + Seq::<TraceRegex>::empty() =~= mk(out@));
    let r = Packed { n, len, w: a.w, traces: out };
    assert(pview(r) == mk(out@));
    r
}

// ---------------------------------------------------------------------------
// Simplification: merge pairs until no pair merges
// ---------------------------------------------------------------------------

fn one_diff_p(x: &Vec<u64>, y: &Vec<u64>) -> (r: bool)
    requires
        x@.len() == y@.len(),
    ensures
        r ==> one_diff(x@, y@),
{
    let mut found = false;
    let mut k: usize = 0;
    while k < x.len()
        invariant
            k <= x@.len(),
            x@.len() == y@.len(),
            forall|j: int| 0 <= j < k ==> {
                let e = #[trigger] diff_mask(x@[j], y@[j]);
                e == 0 || e & sub(e, 1u64) == 0
            },
            forall|j: int, l: int| 0 <= j < l < k ==>
                #[trigger] diff_mask(x@[j], y@[j]) == 0 || #[trigger] diff_mask(x@[l], y@[l]) == 0,
            !found ==> forall|j: int| 0 <= j < k ==> #[trigger] diff_mask(x@[j], y@[j]) == 0,
        decreases x.len() - k,
    {
        let d = x[k] ^ y[k];
        let e = (d | (d >> 1u64)) & LO;
        assert(e == diff_mask(x@[k as int], y@[k as int]));
        if e != 0 {
            if found {
                return false;
            }
            let e1 = e & (e - 1);
            assert(e1 == e & sub(e, 1u64)) by (bit_vector) requires e != 0u64, e1 == e & ((e - 1) as u64);
            if e1 != 0 {
                return false;
            }
            found = true;
        }
        k += 1;
    }
    true
}

/// One merge step on the views: `L[i]` becomes `m`, then `L[j]` is removed
/// by moving the last element into its place.
pub open spec fn merge_step(l: WestRegex, i: int, j: int, m: TraceRegex) -> WestRegex {
    let u = l.update(i, m);
    if j == l.len() - 1 { u.drop_last() } else { u.update(j, l.last()).drop_last() }
}

pub proof fn merge_step_match(pi: WestTrace, l: WestRegex, i: int, j: int, m: TraceRegex)
    requires
        0 <= i < j < l.len(),
        match_regex(pi, m) <==> (match_regex(pi, l[i]) || match_regex(pi, l[j])),
    ensures
        west_match(pi, merge_step(l, i, j, m)) <==> west_match(pi, l),
{
    let r = merge_step(l, i, j, m);
    let last = l.len() - 1;
    // r holds l with l[i], l[j] replaced by m (and l[last] moved to j).
    assert forall|k: int| 0 <= k < r.len() implies #[trigger] r[k] == if k == i { m } else if k == j { l[last] } else { l[k] } by {}
    if west_match(pi, r) {
        let k = choose|k: int| 0 <= k < r.len() && #[trigger] match_regex(pi, r[k]);
        if k == i {
        } else if k == j {
            assert(match_regex(pi, l[last]));
        } else {
            assert(match_regex(pi, l[k]));
        }
    }
    if west_match(pi, l) {
        let k = choose|k: int| 0 <= k < l.len() && #[trigger] match_regex(pi, l[k]);
        if k == i || k == j {
            assert(match_regex(pi, r[i]));
        } else if k == last {
            assert(match_regex(pi, r[j]));
        } else {
            assert(match_regex(pi, r[k]));
        }
    }
}

/// Merge to a fixpoint. Matches exactly the traces the input matches.
pub fn p_simp(r: Packed) -> (out: Packed)
    requires
        pwf(r),
    ensures
        pwf(out),
        out.n == r.n,
        out.len == r.len,
        forall|pi: WestTrace| #[trigger] west_match(pi, pview(out)) == west_match(pi, pview(r)),
{
    let ghost v0 = pview(r);
    let Packed { n, len, w, traces } = r;
    let mut ts = traces;
    let ghost mk = |ts: Seq<Vec<u64>>| ts.map_values(|x: Vec<u64>| tview_p(x, n as nat, len as nat));
    assert(mk(ts@) == v0);
    loop
        invariant
            n >= 1,
            len >= 1,
            fits(n as nat, len as nat),
            w == words_for(n as nat, len as nat),
            forall|m: int| 0 <= m < ts.len() ==> twf(#[trigger] ts@[m]@, n as nat, len as nat),
            mk == |ts: Seq<Vec<u64>>| ts.map_values(|x: Vec<u64>| tview_p(x, n as nat, len as nat)),
            forall|pi: WestTrace| #[trigger] west_match(pi, mk(ts@)) == west_match(pi, v0),
        decreases ts.len(),
    {
        let before = ts.len();
        let mut i: usize = 0;
        while i < ts.len()
            invariant
                n >= 1,
                fits(n as nat, len as nat),
                ts.len() <= before,
                forall|m: int| 0 <= m < ts.len() ==> twf(#[trigger] ts@[m]@, n as nat, len as nat),
                mk == |ts: Seq<Vec<u64>>| ts.map_values(|x: Vec<u64>| tview_p(x, n as nat, len as nat)),
                forall|pi: WestTrace| #[trigger] west_match(pi, mk(ts@)) == west_match(pi, v0),
            decreases ts.len() - i,
        {
            let ghost len_i = ts.len();
            let mut j: usize = i + 1;
            while j < ts.len()
                invariant
                    ts.len() <= len_i,
                    n >= 1,
                    fits(n as nat, len as nat),
                    i < j,
                    i < ts.len(),
                    ts.len() <= before,
                    forall|m: int| 0 <= m < ts.len() ==> twf(#[trigger] ts@[m]@, n as nat, len as nat),
                    mk == |ts: Seq<Vec<u64>>| ts.map_values(|x: Vec<u64>| tview_p(x, n as nat, len as nat)),
                    forall|pi: WestTrace| #[trigger] west_match(pi, mk(ts@)) == west_match(pi, v0),
                decreases ts.len() - j,
            {
                let ghost xs = ts@[i as int]@;
                let ghost ys = ts@[j as int]@;
                assert(twf(xs, n as nat, len as nat) && twf(ys, n as nat, len as nat));
                if one_diff_p(&ts[i], &ts[j]) {
                    // merged = ts[i] | ts[j]
                    let mut z: Vec<u64> = Vec::with_capacity(ts[i].len());
                    let mut k: usize = 0;
                    while k < ts[i].len()
                        invariant
                            i < j < ts.len(),
                            ts@[i as int]@.len() == ts@[j as int]@.len(),
                            k <= ts@[i as int]@.len(),
                            z@ == or_w(ts@[i as int]@, ts@[j as int]@).subrange(0, k as int),
                        decreases ts@[i as int]@.len() - k,
                    {
                        z.push(ts[i][k] | ts[j][k]);
                        k += 1;
                        assert(z@ =~= or_w(ts@[i as int]@, ts@[j as int]@).subrange(0, k as int));
                    }
                    assert(z@ =~= or_w(xs, ys));
                    proof {
                        or_w_correct(xs, ys, n as nat, len as nat);
                        one_diff_check_simp(xs, ys, n as nat, len as nat);
                        lemma_tr_of_vars(xs, n as nat, len as nat);
                        lemma_tr_of_vars(ys, n as nat, len as nat);
                    }
                    let ghost l = mk(ts@);
                    let ghost mv = tview_p(z, n as nat, len as nat);
                    let ghost old_ts = ts@;
                    let last = ts.pop().unwrap();
                    if j < ts.len() {
                        ts.set(j, last);
                    }
                    ts.set(i, z);
                    proof {
                        assert(l[i as int] == tr(xs, n as nat, len as nat));
                        assert(l[j as int] == tr(ys, n as nat, len as nat));
                        assert(mk(ts@) =~= merge_step(l, i as int, j as int, mv));
                        assert forall|pi: WestTrace| #[trigger] west_match(pi, mk(ts@)) == west_match(pi, v0) by {
                            WEST_simp_trace_correct(pi, l[i as int], l[j as int], n as nat);
                            merge_step_match(pi, l, i as int, j as int, mv);
                        }
                        assert forall|m: int| 0 <= m < ts.len() implies twf(#[trigger] ts@[m]@, n as nat, len as nat) by {
                            if m != i && m != j {
                                assert(ts@[m] == old_ts[m]);
                            } else if m == j {
                                assert(ts@[m] == old_ts[old_ts.len() - 1]);
                            }
                        }
                    }
                } else {
                    j += 1;
                }
            }
            i += 1;
        }
        if ts.len() == before {
            break;
        }
    }
    let out = Packed { n, len, w, traces: ts };
    assert(pview(out) == mk(ts@));
    out
}

// ---------------------------------------------------------------------------
// OR and AND of lists (pad to the longer length first)
// ---------------------------------------------------------------------------

/// `L1 ∨ L2` at length `max`: on traces at least that long, matches what
/// either list matches.
pub fn p_or(a: Packed, b: Packed) -> (out: Packed)
    requires
        pwf(a),
        pwf(b),
        a.n == b.n,
    ensures
        pwf(out),
        out.n == a.n,
        out.len == if a.len >= b.len { a.len } else { b.len },
        forall|pi: WestTrace| pi.len() >= out.len ==>
            (#[trigger] west_match(pi, pview(out)) <==> (west_match(pi, pview(a)) || west_match(pi, pview(b)))),
{
    let n = a.n;
    let len = if a.len >= b.len { a.len } else { b.len };
    let pa = if a.len == len { a } else { p_pad(&a, len) };
    let pb = if b.len == len { b } else { p_pad(&b, len) };
    let ghost va = pview(pa);
    let ghost vb = pview(pb);
    let Packed { n: _, len: _, w, traces: mut ta } = pa;
    let Packed { n: _, len: _, w: _, traces: mut tb } = pb;
    ta.append(&mut tb);
    let c = Packed { n, len, w, traces: ta };
    proof {
        assert(pview(c) =~= va + vb);
        assert forall|m: int| 0 <= m < c.traces.len() implies twf(#[trigger] c.traces@[m]@, n as nat, len as nat) by {
            if m < va.len() {
                assert(c.traces@[m] == pa.traces@[m]);
            } else {
                assert(c.traces@[m] == pb.traces@[m - va.len()]);
            }
        }
    }
    let out = p_simp(c);
    proof {
        pview_facts(a);
        pview_facts(b);
        assert forall|pi: WestTrace| pi.len() >= out.len implies
            (#[trigger] west_match(pi, pview(out)) <==> (west_match(pi, pview(a)) || west_match(pi, pview(b)))) by {
            west_match_append(pi, va, vb);
            if a.len != len {
                pad_all_match(pi, pview(a), n as nat, a.len as nat, len as nat);
            }
            if b.len != len {
                pad_all_match(pi, pview(b), n as nat, b.len as nat, len as nat);
            }
        }
    }
    out
}

/// `L1 ∧ L2` at length `max`: on traces at least that long, matches what
/// both lists match.
pub fn p_and(a: &Packed, b: &Packed) -> (out: Packed)
    requires
        pwf(*a),
        pwf(*b),
        a.n == b.n,
    ensures
        pwf(out),
        out.n == a.n,
        out.len == if a.len >= b.len { a.len } else { b.len },
        forall|pi: WestTrace| pi.len() >= out.len ==>
            (#[trigger] west_match(pi, pview(out)) <==> (west_match(pi, pview(*a)) && west_match(pi, pview(*b)))),
{
    let n = a.n;
    let len = if a.len >= b.len { a.len } else { b.len };
    let c = if a.len == len && b.len == len {
        p_and_cross(a, b)
    } else if a.len == len {
        let pb = p_pad(b, len);
        p_and_cross(a, &pb)
    } else {
        let pa = p_pad(a, len);
        p_and_cross(&pa, b)
    };
    proof {
        pview_facts(*a);
        pview_facts(*b);
        // c is WEST_and of the padded views.
    }
    let ghost pa_v = if a.len == len { pview(*a) } else {
        pview(*a).map_values(|t: TraceRegex| pad_spec(t, n as nat, (len - a.len) as nat)) };
    let ghost pb_v = if b.len == len { pview(*b) } else {
        pview(*b).map_values(|t: TraceRegex| pad_spec(t, n as nat, (len - b.len) as nat)) };
    assert(pview(c) == WEST_and_spec(pa_v, pb_v));
    proof {
        assert(WEST_regex_of_vars(pa_v, n as nat)) by {
            assert forall|k: int| 0 <= k < pa_v.len() implies trace_regex_of_vars(#[trigger] pa_v[k], n as nat) by {
                if a.len != len {
                    pad_match(Seq::empty(), pview(*a)[k], n as nat, (len - a.len) as nat);
                }
            }
        }
        assert(WEST_regex_of_vars(pb_v, n as nat)) by {
            assert forall|k: int| 0 <= k < pb_v.len() implies trace_regex_of_vars(#[trigger] pb_v[k], n as nat) by {
                if b.len != len {
                    pad_match(Seq::empty(), pview(*b)[k], n as nat, (len - b.len) as nat);
                }
            }
        }
    }
    let out = p_simp(c);
    proof {
        assert forall|pi: WestTrace| pi.len() >= out.len implies
            (#[trigger] west_match(pi, pview(out)) <==> (west_match(pi, pview(*a)) && west_match(pi, pview(*b)))) by {
            WEST_and_correct(pi, pa_v, pb_v, n as nat);
            if a.len != len {
                pad_all_match(pi, pview(*a), n as nat, a.len as nat, len as nat);
            }
            if b.len != len {
                pad_all_match(pi, pview(*b), n as nat, b.len as nat, len as nat);
            }
        }
    }
    out
}

} // verus!
