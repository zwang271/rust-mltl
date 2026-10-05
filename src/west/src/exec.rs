//! Executable WEST, equal to the specification.
//!
//! Every function here returns exactly what its `<name>_spec` in
//! `algorithms.rs` computes (D20), so the theorems of `correct.rs` apply to
//! its output; `WEST_reg` and `simp_pad_WEST_reg` state them in their
//! `ensures`. Regexes are `Vec<Vec<Vec<WestBit>>>`, read by `rview`.
//! Loops replace Isabelle's recursion; the temporal operators keep the
//! running `WEST_global` instead of recomputing it (same value, fewer steps).
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithms::*;
use crate::matching::*;
use crate::simp::*;
use crate::temporal::*;
use crate::correct::*;

verus! {

/// Executable state regex.
pub type ExecState = Vec<WestBit>;
/// Executable trace regex.
pub type ExecTrace = Vec<Vec<WestBit>>;
/// Executable WEST regex.
pub type ExecRegex = Vec<Vec<Vec<WestBit>>>;

pub open spec fn sview(s: Vec<WestBit>) -> StateRegex {
    s@
}

pub open spec fn tview(t: ExecTrace) -> TraceRegex {
    t@.map_values(|s: Vec<WestBit>| sview(s))
}

pub open spec fn rview(r: ExecRegex) -> WestRegex {
    r@.map_values(|t: ExecTrace| tview(t))
}

// ---------------------------------------------------------------------------
// Copies and constant states
// ---------------------------------------------------------------------------

fn copy_state(s: &Vec<WestBit>) -> (r: Vec<WestBit>)
    ensures
        r@ == s@,
{
    let mut r: Vec<WestBit> = Vec::with_capacity(s.len());
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            r@ == s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        r.push(s[i]);
        i += 1;
    }
    assert(r@ =~= s@);
    r
}

fn copy_trace(t: &ExecTrace) -> (r: ExecTrace)
    ensures
        tview(r) == tview(*t),
{
    let mut r: ExecTrace = Vec::with_capacity(t.len());
    let mut i: usize = 0;
    while i < t.len()
        invariant
            i <= t.len(),
            tview(r) == tview(*t).subrange(0, i as int),
        decreases t.len() - i,
    {
        let s = copy_state(&t[i]);
        let ghost before = tview(r);
        r.push(s);
        assert(tview(*t)[i as int] == t@[i as int]@);
        assert(tview(r) =~= before.push(s@));
        assert(tview(r) =~= tview(*t).subrange(0, i + 1));
        i += 1;
    }
    assert(tview(r) =~= tview(*t));
    r
}

/// `arbitrary_state n`
pub fn arbitrary_state_exec(n: usize) -> (r: Vec<WestBit>)
    ensures
        r@ == arbitrary_state(n as nat),
{
    let mut r: Vec<WestBit> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r@ == Seq::new(i as nat, |k: int| WestBit::S),
        decreases n - i,
    {
        r.push(WestBit::S);
        i += 1;
        assert(r@ =~= Seq::new(i as nat, |k: int| WestBit::S));
    }
    r
}

/// The one-state regex with `bit` at `p` and `S` elsewhere.
fn single_state(n: usize, p: usize, bit: WestBit) -> (r: Vec<WestBit>)
    ensures
        r@ == Seq::new(n as nat, |j: int| if p as int == j { bit } else { WestBit::S }),
{
    let mut r: Vec<WestBit> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r@ == Seq::new(i as nat, |j: int| if p as int == j { bit } else { WestBit::S }),
        decreases n - i,
    {
        if i == p {
            r.push(bit);
        } else {
            r.push(WestBit::S);
        }
        i += 1;
        assert(r@ =~= Seq::new(i as nat, |j: int| if p as int == j { bit } else { WestBit::S }));
    }
    r
}

// ---------------------------------------------------------------------------
// AND
// ---------------------------------------------------------------------------

/// `WEST_and_bitwise`
pub fn WEST_and_bitwise(b: WestBit, c: WestBit) -> (r: Option<WestBit>)
    ensures
        r == WEST_and_bitwise_spec(b, c),
{
    match c {
        WestBit::One => match b {
            WestBit::Zero => None,
            _ => Some(WestBit::One),
        },
        WestBit::Zero => match b {
            WestBit::One => None,
            _ => Some(WestBit::Zero),
        },
        WestBit::S => Some(b),
    }
}

/// `WEST_and_state`
pub fn WEST_and_state(s1: &Vec<WestBit>, s2: &Vec<WestBit>) -> (r: Option<Vec<WestBit>>)
    ensures
        match r {
            None => WEST_and_state_spec(s1@, s2@) is None,
            Some(v) => WEST_and_state_spec(s1@, s2@) == Some(v@),
        },
{
    proof { WEST_and_state_index(s1@, s2@); }
    if s1.len() != s2.len() {
        return None;
    }
    let mut out: Vec<WestBit> = Vec::with_capacity(s1.len());
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            s1.len() == s2.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] WEST_and_bitwise_spec(s1@[k], s2@[k]) is Some
                && out@[k] == WEST_and_bitwise_spec(s1@[k], s2@[k])->Some_0,
        decreases s1.len() - i,
    {
        match WEST_and_bitwise(s1[i], s2[i]) {
            None => {
                assert(!(WEST_and_bitwise_spec(s1@[i as int], s2@[i as int]) is Some));
                proof { WEST_and_state_index(s1@, s2@); }
                return None;
            },
            Some(x) => {
                out.push(x);
            },
        }
        i += 1;
    }
    proof {
        assert(out@ =~= WEST_and_state_spec(s1@, s2@)->Some_0);
    }
    Some(out)
}

/// `WEST_and_trace`
pub fn WEST_and_trace(t1: &ExecTrace, t2: &ExecTrace) -> (r: Option<ExecTrace>)
    ensures
        match r {
            None => WEST_and_trace_spec(tview(*t1), tview(*t2)) is None,
            Some(v) => WEST_and_trace_spec(tview(*t1), tview(*t2)) == Some(tview(v)),
        },
{
    let ghost v1 = tview(*t1);
    let ghost v2 = tview(*t2);
    proof { WEST_and_trace_index(v1, v2); }
    let m = if t1.len() < t2.len() { t1.len() } else { t2.len() };
    let mut out: ExecTrace = Vec::new();
    let mut k: usize = 0;
    while k < m
        invariant
            k <= m,
            m == t1.len() || m == t2.len(),
            m <= t1.len() && m <= t2.len(),
            v1 == tview(*t1),
            v2 == tview(*t2),
            out@.len() == k,
            forall|j: int| 0 <= j < k ==> #[trigger] WEST_and_state_spec(v1[j], v2[j]) is Some
                && tview(out)[j] == WEST_and_state_spec(v1[j], v2[j])->Some_0,
        decreases m - k,
    {
        assert(v1[k as int] == t1@[k as int]@ && v2[k as int] == t2@[k as int]@);
        match WEST_and_state(&t1[k], &t2[k]) {
            None => {
                assert(!(WEST_and_state_spec(v1[k as int], v2[k as int]) is Some));
                proof { WEST_and_trace_index(v1, v2); }
                return None;
            },
            Some(s) => {
                let ghost before = tview(out);
                out.push(s);
                assert(tview(out) =~= before.push(s@));
            },
        }
        k += 1;
    }
    let longer = if t1.len() > m { t1 } else { t2 };
    let ghost vl = tview(*longer);
    while k < longer.len()
        invariant
            m <= k <= longer.len(),
            m == t1.len() || m == t2.len(),
            m <= t1.len() && m <= t2.len(),
            longer.len() == max_nat(t1.len() as nat, t2.len() as nat),
            vl == tview(*longer),
            vl == (if t1.len() > m { v1 } else { v2 }),
            v1 == tview(*t1),
            v2 == tview(*t2),
            out@.len() == k,
            forall|j: int| 0 <= j < m ==> #[trigger] WEST_and_state_spec(v1[j], v2[j]) is Some
                && tview(out)[j] == WEST_and_state_spec(v1[j], v2[j])->Some_0,
            forall|j: int| m <= j < k ==> #[trigger] tview(out)[j] == vl[j],
        decreases longer.len() - k,
    {
        let s = copy_state(&longer[k]);
        assert(vl[k as int] == longer@[k as int]@);
        let ghost before = tview(out);
        out.push(s);
        assert(tview(out) =~= before.push(s@));
        k += 1;
    }
    proof {
        let t = WEST_and_trace_spec(v1, v2)->Some_0;
        assert forall|j: int| 0 <= j < t.len() implies tview(out)[j] == t[j] by {
            if j >= m {
                if t1.len() > m {
                    assert(j < v1.len());
                } else {
                    assert(j < v2.len());
                }
            }
        }
        assert(tview(out) =~= t);
    }
    Some(out)
}

pub proof fn WEST_and_unfold(l1: WestRegex, l2: WestRegex, i: int)
    requires
        0 <= i < l1.len(),
        l2.len() > 0,
    ensures
        WEST_and_spec(l1.skip(i), l2) == WEST_and_helper_spec(l1[i], l2) + WEST_and_spec(l1.skip(i + 1), l2),
{
    let s = l1.skip(i);
    assert(s[0] == l1[i]);
    assert(s.drop_first() =~= l1.skip(i + 1));
    let h = WEST_and_helper_spec(l1[i], l2);
    if h.len() == 0 {
        assert(h + WEST_and_spec(l1.skip(i + 1), l2) =~= WEST_and_spec(l1.skip(i + 1), l2));
    }
}

pub proof fn WEST_and_helper_unfold(t: TraceRegex, ts: WestRegex, j: int)
    requires
        0 <= j < ts.len(),
    ensures
        WEST_and_helper_spec(t, ts.skip(j)) == (match WEST_and_trace_spec(t, ts[j]) {
            None => Seq::<TraceRegex>::empty(),
            Some(res) => seq![res],
        }) + WEST_and_helper_spec(t, ts.skip(j + 1)),
{
    let s = ts.skip(j);
    assert(s[0] == ts[j]);
    assert(s.drop_first() =~= ts.skip(j + 1));
    let rest = WEST_and_helper_spec(t, ts.skip(j + 1));
    assert(Seq::<TraceRegex>::empty() + rest =~= rest);
}

/// `WEST_and`
pub fn WEST_and(l1: &ExecRegex, l2: &ExecRegex) -> (r: ExecRegex)
    ensures
        rview(r) == WEST_and_spec(rview(*l1), rview(*l2)),
{
    let ghost v1 = rview(*l1);
    let ghost v2 = rview(*l2);
    let mut out: ExecRegex = Vec::new();
    if l2.len() == 0 {
        assert(rview(out) =~= Seq::<TraceRegex>::empty());
        return out;
    }
    let mut i: usize = 0;
    assert(v1.skip(0) =~= v1);
    assert(rview(out) + WEST_and_spec(v1.skip(0), v2) =~= WEST_and_spec(v1, v2));
    while i < l1.len()
        invariant
            i <= l1.len(),
            l2.len() > 0,
            v1 == rview(*l1),
            v2 == rview(*l2),
            rview(out) + WEST_and_spec(v1.skip(i as int), v2) == WEST_and_spec(v1, v2),
        decreases l1.len() - i,
    {
        proof { WEST_and_unfold(v1, v2, i as int); }
        let mut j: usize = 0;
        assert(v2.skip(0) =~= v2);
        assert(rview(out) + WEST_and_helper_spec(v1[i as int], v2.skip(0)) + WEST_and_spec(v1.skip(i + 1), v2)
            =~= WEST_and_spec(v1, v2));
        while j < l2.len()
            invariant
                i < l1.len(),
                j <= l2.len(),
                v1 == rview(*l1),
                v2 == rview(*l2),
                rview(out) + WEST_and_helper_spec(v1[i as int], v2.skip(j as int)) + WEST_and_spec(v1.skip(i + 1), v2)
                    == WEST_and_spec(v1, v2),
            decreases l2.len() - j,
        {
            proof { WEST_and_helper_unfold(v1[i as int], v2, j as int); }
            let ghost before = rview(out);
            let ghost rest = WEST_and_helper_spec(v1[i as int], v2.skip(j + 1));
            let ghost tail = WEST_and_spec(v1.skip(i + 1), v2);
            assert(v1[i as int] == tview(l1@[i as int]) && v2[j as int] == tview(l2@[j as int]));
            match WEST_and_trace(&l1[i], &l2[j]) {
                None => {
                    assert(Seq::<TraceRegex>::empty() + rest =~= rest);
                },
                Some(res) => {
                    let ghost rv = tview(res);
                    out.push(res);
                    assert(rview(out) =~= before + seq![rv]);
                    assert(before + (seq![rv] + rest) + tail =~= rview(out) + rest + tail);
                },
            }
            j += 1;
        }
        assert(v2.skip(l2.len() as int) =~= Seq::<TraceRegex>::empty());
        assert(rview(out) + Seq::<TraceRegex>::empty() =~= rview(out));
        i += 1;
    }
    assert(v1.skip(l1.len() as int) =~= Seq::<TraceRegex>::empty());
    assert(rview(out) + Seq::<TraceRegex>::empty() =~= rview(out));
    out
}

// ---------------------------------------------------------------------------
// Simplification
// ---------------------------------------------------------------------------

/// `WEST_simp_bitwise`
pub fn WEST_simp_bitwise(b: WestBit, c: WestBit) -> (r: WestBit)
    ensures
        r == WEST_simp_bitwise_spec(b, c),
{
    match c {
        WestBit::S => WestBit::S,
        WestBit::Zero => match b {
            WestBit::Zero => WestBit::Zero,
            _ => WestBit::S,
        },
        WestBit::One => match b {
            WestBit::One => WestBit::One,
            _ => WestBit::S,
        },
    }
}

/// `WEST_simp_state` (needs `s2` at least as long as `s1`, as Isabelle's
/// `s2 ! k` does to be meaningful).
pub fn WEST_simp_state(s1: &Vec<WestBit>, s2: &Vec<WestBit>) -> (r: Vec<WestBit>)
    requires
        s1.len() <= s2.len(),
    ensures
        r@ == WEST_simp_state_spec(s1@, s2@),
{
    let mut r: Vec<WestBit> = Vec::with_capacity(s1.len());
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            s1.len() <= s2.len(),
            r@ == Seq::new(i as nat, |k: int| WEST_simp_bitwise_spec(s1@[k], s2@[k])),
        decreases s1.len() - i,
    {
        r.push(WEST_simp_bitwise(s1[i], s2[i]));
        i += 1;
        assert(r@ =~= Seq::new(i as nat, |k: int| WEST_simp_bitwise_spec(s1@[k], s2@[k])));
    }
    r
}

/// `WEST_simp_trace` (states of width `n`).
pub fn WEST_simp_trace(t1: &ExecTrace, t2: &ExecTrace, n: usize) -> (r: ExecTrace)
    requires
        trace_regex_of_vars(tview(*t1), n as nat),
        trace_regex_of_vars(tview(*t2), n as nat),
    ensures
        tview(r) == WEST_simp_trace_spec(tview(*t1), tview(*t2), n as nat),
{
    let ghost v1 = tview(*t1);
    let ghost v2 = tview(*t2);
    let all_s = arbitrary_state_exec(n);
    let m = if t1.len() < t2.len() { t2.len() } else { t1.len() };
    let mut r: ExecTrace = Vec::with_capacity(m);
    let mut k: usize = 0;
    while k < m
        invariant
            k <= m,
            m as nat == max_nat(t1.len() as nat, t2.len() as nat),
            v1 == tview(*t1),
            v2 == tview(*t2),
            trace_regex_of_vars(v1, n as nat),
            trace_regex_of_vars(v2, n as nat),
            all_s@ == arbitrary_state(n as nat),
            tview(r) == Seq::new(k as nat, |j: int| WEST_simp_state_spec(
                WEST_get_state(v1, j as nat, n as nat), WEST_get_state(v2, j as nat, n as nat))),
        decreases m - k,
    {
        let a = if k < t1.len() { &t1[k] } else { &all_s };
        let b = if k < t2.len() { &t2[k] } else { &all_s };
        assert(a@ == WEST_get_state(v1, k as nat, n as nat)) by {
            if k < t1.len() { assert(v1[k as int] == t1@[k as int]@); }
        }
        assert(b@ == WEST_get_state(v2, k as nat, n as nat)) by {
            if k < t2.len() { assert(v2[k as int] == t2@[k as int]@); }
        }
        assert(a@.len() == n && b@.len() == n) by {
            if k < t1.len() { assert(v1[k as int].len() == n); }
            if k < t2.len() { assert(v2[k as int].len() == n); }
        }
        let s = WEST_simp_state(a, b);
        let ghost before = tview(r);
        r.push(s);
        assert(tview(r) =~= before.push(s@));
        k += 1;
        assert(tview(r) =~= Seq::new(k as nat, |j: int| WEST_simp_state_spec(
            WEST_get_state(v1, j as nat, n as nat), WEST_get_state(v2, j as nat, n as nat))));
    }
    r
}

fn bit_eq(b: WestBit, c: WestBit) -> (r: bool)
    ensures
        r == (b == c),
{
    match (b, c) {
        (WestBit::Zero, WestBit::Zero) | (WestBit::One, WestBit::One) | (WestBit::S, WestBit::S) => true,
        _ => false,
    }
}

/// `count_diff_state` of equal-length states.
fn count_diff_state_exec(s1: &Vec<WestBit>, s2: &Vec<WestBit>) -> (r: usize)
    requires
        s1.len() == s2.len(),
    ensures
        r == count_diff_state(s1@, s2@),
{
    let mut acc: usize = 0;
    let mut i: usize = 0;
    assert(s1@.skip(0) =~= s1@ && s2@.skip(0) =~= s2@);
    while i < s1.len()
        invariant
            i <= s1.len(),
            s1.len() == s2.len(),
            acc <= i,
            acc + count_diff_state(s1@.skip(i as int), s2@.skip(i as int)) == count_diff_state(s1@, s2@),
        decreases s1.len() - i,
    {
        let ghost a = s1@.skip(i as int);
        let ghost b = s2@.skip(i as int);
        assert(a[0] == s1@[i as int] && b[0] == s2@[i as int]);
        assert(a.drop_first() =~= s1@.skip(i + 1) && b.drop_first() =~= s2@.skip(i + 1));
        if !bit_eq(s1[i], s2[i]) {
            acc += 1;
        }
        i += 1;
    }
    assert(s1@.skip(i as int).len() == 0 && s2@.skip(i as int).len() == 0);
    acc
}

/// `check_simp` of regexes with `n`-wide states.
pub fn check_simp(t1: &ExecTrace, t2: &ExecTrace, n: Ghost<nat>) -> (r: bool)
    requires
        trace_regex_of_vars(tview(*t1), n@),
        trace_regex_of_vars(tview(*t2), n@),
    ensures
        r == check_simp_spec(tview(*t1), tview(*t2)),
{
    let ghost v1 = tview(*t1);
    let ghost v2 = tview(*t2);
    if t1.len() != t2.len() {
        return false;
    }
    let mut acc: usize = 0;
    let mut k: usize = 0;
    assert(v1.skip(0) =~= v1 && v2.skip(0) =~= v2);
    while k < t1.len()
        invariant
            k <= t1.len(),
            t1.len() == t2.len(),
            v1 == tview(*t1),
            v2 == tview(*t2),
            trace_regex_of_vars(v1, n@),
            trace_regex_of_vars(v2, n@),
            acc <= 1,
            acc + count_diff(v1.skip(k as int), v2.skip(k as int)) == count_diff(v1, v2),
        decreases t1.len() - k,
    {
        let ghost a = v1.skip(k as int);
        let ghost b = v2.skip(k as int);
        assert(a[0] == v1[k as int] && b[0] == v2[k as int]);
        assert(a.drop_first() =~= v1.skip(k + 1) && b.drop_first() =~= v2.skip(k + 1));
        assert(v1[k as int] == t1@[k as int]@ && v2[k as int] == t2@[k as int]@);
        assert(v1[k as int].len() == n@ && v2[k as int].len() == n@);
        let c = count_diff_state_exec(&t1[k], &t2[k]);
        if c > 1 || acc + c > 1 {
            return false;
        }
        acc += c;
        k += 1;
    }
    assert(v1.skip(k as int).len() == 0 && v2.skip(k as int).len() == 0);
    true
}

/// Offset of row `a` in `enumerate_pairs [lo..<n]`: the rows `lo..a-1`
/// have `n-1-x` pairs each.
pub open spec fn pair_off(lo: nat, a: nat, n: nat) -> nat
    decreases a - lo,
{
    if lo >= a || lo >= n {
        0
    } else {
        (n - lo - 1) as nat + pair_off(lo + 1, a, n)
    }
}

proof fn pair_off_step(lo: nat, a: nat, n: nat)
    requires
        lo <= a < n,
    ensures
        pair_off(lo, a + 1, n) == pair_off(lo, a, n) + (n - a - 1),
    decreases a - lo,
{
    reveal_with_fuel(pair_off, 2);
    if lo < a {
        pair_off_step(lo + 1, a, n);
    }
}

proof fn pair_off_mono(lo: nat, a: nat, c: nat, n: nat)
    requires
        lo <= a <= c <= n,
    ensures
        pair_off(lo, a, n) <= pair_off(lo, c, n),
    decreases c - a,
{
    if a < c {
        pair_off_mono(lo, a, (c - 1) as nat, n);
        pair_off_step(lo, (c - 1) as nat, n);
    }
}

proof fn enumerate_pairs_unfold(lo: nat, n: nat)
    requires
        lo < n,
    ensures
        enumerate_pairs(upt_from(lo, n)) == upt_from(lo + 1, n).map_values(|y: nat| (lo, y))
            + enumerate_pairs(upt_from(lo + 1, n)),
{
    let xs = upt_from(lo, n);
    assert(xs.drop_first() =~= upt_from(lo + 1, n));
    assert(xs[0] == lo);
}

/// `enumerate_pairs [lo..<n]` has `pair_off lo n n` entries.
proof fn enumerate_pairs_len(lo: nat, n: nat)
    requires
        lo <= n,
    ensures
        enumerate_pairs(upt_from(lo, n)).len() == pair_off(lo, n, n),
    decreases n - lo,
{
    if lo < n {
        enumerate_pairs_unfold(lo, n);
        enumerate_pairs_len(lo + 1, n);
    } else {
        assert(upt_from(lo, n).len() == 0);
    }
}

/// Pair `(a, b)` sits at `pair_off lo a n + (b - a - 1)` of
/// `enumerate_pairs [lo..<n]`.
proof fn enumerate_pairs_at(lo: nat, n: nat, a: nat, b: nat)
    requires
        lo <= a < b < n,
    ensures
        pair_off(lo, a, n) + (b - a - 1) < enumerate_pairs(upt_from(lo, n)).len(),
        enumerate_pairs(upt_from(lo, n))[pair_off(lo, a, n) + (b - a - 1)] == (a, b),
    decreases a - lo,
{
    enumerate_pairs_unfold(lo, n);
    enumerate_pairs_len(lo, n);
    enumerate_pairs_len(lo + 1, n);
    let row = upt_from(lo + 1, n).map_values(|y: nat| (lo, y));
    let rest = enumerate_pairs(upt_from(lo + 1, n));
    let all = enumerate_pairs(upt_from(lo, n));
    assert(row.len() == n - lo - 1);
    if a == lo {
        let j = b - a - 1;
        assert(upt_from(lo + 1, n)[j] == b);
        assert(all[j] == row[j]);
    } else {
        enumerate_pairs_at(lo + 1, n, a, b);
        let j = pair_off(lo + 1, a, n) + (b - a - 1);
        assert(pair_off(lo, a, n) + (b - a - 1) == row.len() + j);
        assert(all[row.len() + j] == rest[j]);
    }
}

proof fn enum_pairs_len<T>(l: Seq<T>)
    ensures
        enum_pairs(l).len() == pair_off(0, l.len(), l.len()),
{
    assert(upt_from(0, l.len()) =~= upt(l.len()));
    enumerate_pairs_len(0, l.len());
}

proof fn enum_pairs_at<T>(l: Seq<T>, a: nat, b: nat)
    requires
        a < b < l.len(),
    ensures
        pair_off(0, a, l.len()) + (b - a - 1) < enum_pairs(l).len(),
        enum_pairs(l)[pair_off(0, a, l.len()) + (b - a - 1)] == (a, b),
{
    assert(upt_from(0, l.len()) =~= upt(l.len()));
    enumerate_pairs_at(0, l.len(), a, b);
}

/// `update_L L (a, b) n` in place: merge the traces at `a < b`, remove both,
/// append the merge.
fn update_L_exec(l: &mut ExecRegex, a: usize, b: usize, n: usize)
    requires
        a < b < old(l).len(),
        WEST_regex_of_vars(rview(*old(l)), n as nat),
    ensures
        rview(*final(l)) == update_L(rview(*old(l)), (a as nat, b as nat), n as nat),
{
    let ghost v = rview(*l);
    assert(v[a as int] == tview(l@[a as int]) && v[b as int] == tview(l@[b as int]));
    assert(trace_regex_of_vars(v[a as int], n as nat) && trace_regex_of_vars(v[b as int], n as nat));
    let merged = WEST_simp_trace(&l[a], &l[b], n);
    let ghost mv = tview(merged);
    let _ = l.remove(b);
    let ghost r1 = rview(*l);
    assert(r1 =~= v.remove(b as int));
    assert(v.remove(b as int) =~= remove_element_at_index(b as nat, v));
    let _ = l.remove(a);
    let ghost r2 = rview(*l);
    assert(r2 =~= r1.remove(a as int));
    assert(r1.remove(a as int) =~= remove_element_at_index(a as nat, r1));
    l.push(merged);
    assert(rview(*l) =~= r2 + seq![mv]);
}

/// `WEST_simp L n`. Scans pairs `(a, b)` in `enum_pairs` order; on a merge,
/// restarts from `(0, 1)` as `WEST_simp_helper` does.
pub fn WEST_simp(input: ExecRegex, n: usize) -> (r: ExecRegex)
    requires
        WEST_regex_of_vars(rview(input), n as nat),
    ensures
        rview(r) == WEST_simp_spec(rview(input), n as nat),
{
    let ghost l0 = rview(input);
    let ghost target = WEST_simp_spec(l0, n as nat);
    let mut l = input;
    let mut a: usize = 0;
    let mut b: usize = 1;
    let ghost mut idx: nat = 0;
    proof { enum_pairs_len(rview(l)); }
    loop
        invariant
            WEST_regex_of_vars(rview(l), n as nat),
            l0 == rview(input),
            target == WEST_simp_spec(l0, n as nat),
            target == WEST_simp_helper_spec(rview(l), enum_pairs(rview(l)), idx, n as nat),
            a < b,
            a == 0 || a < l.len(),
            b <= l.len() || b == a + 1,
            a + 1 >= l.len() ==> b == a + 1,
            idx == pair_off(0, a as nat, l.len() as nat) + (b - a - 1),
            idx <= enum_pairs(rview(l)).len(),
        decreases simp_measure(rview(l), enum_pairs(rview(l)), idx), l.len() - a,
    {
        let ghost v = rview(l);
        proof {
            enum_pairs_len(v);
            enum_pairs_facts(v);
        }
        if a + 1 >= l.len() {
            proof {
                assert(v.len() == l.len());
                if l.len() >= 1 {
                    assert(a == l.len() - 1);
                    pair_off_step(0, (l.len() - 1) as nat, l.len() as nat);
                } else {
                    assert(a == 0);
                    assert(pair_off(0, 0, 0) == 0);
                }
                assert(idx >= enum_pairs(v).len());
                assert(WEST_simp_helper_spec(v, enum_pairs(v), idx, n as nat) == v);
            }
            return l;
        }
        if b == l.len() {
            proof {
                pair_off_step(0, a as nat, l.len() as nat);
                pair_off_mono(0, (a + 1) as nat, l.len() as nat, l.len() as nat);
            }
            a += 1;
            b = a + 1;
            continue;
        }
        let ghost h = (a as nat, b as nat);
        proof { enum_pairs_at(v, a as nat, b as nat); }
        assert(enum_pairs(v)[idx as int] == h);
        assert(v[a as int] == tview(l@[a as int]) && v[b as int] == tview(l@[b as int]));
        if check_simp(&l[a], &l[b], Ghost(n as nat)) {
            proof {
                update_L_len(v, h, n as nat);
                update_L_correct(Seq::empty(), v, h, n as nat);
            }
            update_L_exec(&mut l, a, b, n);
            proof {
                let m = l.len() as nat;
                let nn = v.len();
                assert(m * m * m + m * m < nn * nn * nn) by (nonlinear_arith)
                    requires m + 1 == nn;
                enum_pairs_facts(rview(l));
                enum_pairs_len(rview(l));
                idx = 0;
                assert(pair_off(0, 0, m) == 0);
            }
            a = 0;
            b = 1;
        } else {
            proof {
                idx = idx + 1;
                pair_off_step(0, a as nat, l.len() as nat);
                pair_off_mono(0, (a + 1) as nat, l.len() as nat, l.len() as nat);
            }
            b += 1;
        }
    }
}

/// `WEST_and_simp`
pub fn WEST_and_simp(l1: &ExecRegex, l2: &ExecRegex, n: usize) -> (r: ExecRegex)
    requires
        WEST_regex_of_vars(rview(*l1), n as nat),
        WEST_regex_of_vars(rview(*l2), n as nat),
    ensures
        rview(r) == WEST_and_simp_spec(rview(*l1), rview(*l2), n as nat),
        WEST_regex_of_vars(rview(r), n as nat),
{
    let x = WEST_and(l1, l2);
    proof {
        WEST_and_correct(Seq::empty(), rview(*l1), rview(*l2), n as nat);
        WEST_and_simp_correct(Seq::empty(), rview(*l1), rview(*l2), n as nat);
    }
    WEST_simp(x, n)
}

/// `WEST_or_simp`
pub fn WEST_or_simp(l1: ExecRegex, l2: ExecRegex, n: usize) -> (r: ExecRegex)
    requires
        WEST_regex_of_vars(rview(l1), n as nat),
        WEST_regex_of_vars(rview(l2), n as nat),
    ensures
        rview(r) == WEST_or_simp_spec(rview(l1), rview(l2), n as nat),
        WEST_regex_of_vars(rview(r), n as nat),
{
    let ghost v1 = rview(l1);
    let ghost v2 = rview(l2);
    let mut l1 = l1;
    let mut l2 = l2;
    l1.append(&mut l2);
    assert(rview(l1) =~= v1 + v2);
    proof {
        regex_of_vars_append(v1, v2, n as nat);
        WEST_or_simp_correct(Seq::empty(), v1, v2, n as nat);
    }
    WEST_simp(l1, n)
}

// ---------------------------------------------------------------------------
// Shift and pad
// ---------------------------------------------------------------------------

/// `shift L n a`
pub fn shift(l: &ExecRegex, n: usize, a: usize) -> (r: ExecRegex)
    ensures
        rview(r) == shift_spec(rview(*l), n as nat, a as nat),
{
    let ghost v = rview(*l);
    let mut r: ExecRegex = Vec::with_capacity(l.len());
    let mut i: usize = 0;
    while i < l.len()
        invariant
            i <= l.len(),
            v == rview(*l),
            rview(r) == shift_spec(v, n as nat, a as nat).subrange(0, i as int),
        decreases l.len() - i,
    {
        let mut t: ExecTrace = Vec::new();
        let mut k: usize = 0;
        while k < a
            invariant
                k <= a,
                tview(t) == arbitrary_trace(n as nat, k as nat),
            decreases a - k,
        {
            let s = arbitrary_state_exec(n);
            let ghost before = tview(t);
            t.push(s);
            assert(tview(t) =~= before.push(s@));
            k += 1;
            assert(tview(t) =~= arbitrary_trace(n as nat, k as nat));
        }
        let src = &l[i];
        assert(v[i as int] == tview(*src));
        let mut j: usize = 0;
        while j < src.len()
            invariant
                j <= src.len(),
                tview(t) == arbitrary_trace(n as nat, a as nat) + tview(*src).subrange(0, j as int),
            decreases src.len() - j,
        {
            let s = copy_state(&src[j]);
            let ghost before = tview(t);
            t.push(s);
            assert(tview(t) =~= before.push(s@));
            assert(tview(*src)[j as int] == src@[j as int]@);
            j += 1;
            assert(tview(t) =~= arbitrary_trace(n as nat, a as nat) + tview(*src).subrange(0, j as int));
        }
        assert(tview(*src).subrange(0, src.len() as int) =~= tview(*src));
        let ghost tv = tview(t);
        let ghost before = rview(r);
        r.push(t);
        assert(rview(r) =~= before.push(tv));
        i += 1;
        assert(rview(r) =~= shift_spec(v, n as nat, a as nat).subrange(0, i as int));
    }
    assert(rview(r) =~= shift_spec(v, n as nat, a as nat));
    r
}

/// `pad trace n k`
pub fn pad(t: ExecTrace, n: usize, k: usize) -> (r: ExecTrace)
    ensures
        tview(r) == pad_spec(tview(t), n as nat, k as nat),
{
    let ghost v = tview(t);
    let mut t = t;
    let mut i: usize = 0;
    while i < k
        invariant
            i <= k,
            tview(t) == v + arbitrary_trace(n as nat, i as nat),
        decreases k - i,
    {
        let s = arbitrary_state_exec(n);
        let ghost before = tview(t);
        t.push(s);
        assert(tview(t) =~= before.push(s@));
        i += 1;
        assert(tview(t) =~= v + arbitrary_trace(n as nat, i as nat));
    }
    t
}

// ---------------------------------------------------------------------------
// Temporal operations
// ---------------------------------------------------------------------------

proof fn shift_of_vars(l: WestRegex, n: nat, a: nat)
    requires
        WEST_regex_of_vars(l, n),
    ensures
        WEST_regex_of_vars(shift_spec(l, n, a), n),
{
    shift_correct(Seq::empty(), l, n, a);
}

/// `WEST_global L a b n`
pub fn WEST_global(l: &ExecRegex, a: usize, b: usize, n: usize) -> (r: ExecRegex)
    requires
        WEST_regex_of_vars(rview(*l), n as nat),
    ensures
        rview(r) == WEST_global_spec(rview(*l), a as nat, b as nat, n as nat),
        WEST_regex_of_vars(rview(r), n as nat),
{
    let ghost v = rview(*l);
    if a > b {
        let r: ExecRegex = Vec::new();
        assert(rview(r) =~= Seq::<TraceRegex>::empty());
        return r;
    }
    let mut acc = shift(l, n, a);
    proof { shift_of_vars(v, n as nat, a as nat); }
    let mut k = a;
    while k < b
        invariant
            a <= k <= b,
            v == rview(*l),
            WEST_regex_of_vars(v, n as nat),
            rview(acc) == WEST_global_spec(v, a as nat, k as nat, n as nat),
            WEST_regex_of_vars(rview(acc), n as nat),
        decreases b - k,
    {
        k += 1;
        let s = shift(l, n, k);
        proof { shift_of_vars(v, n as nat, k as nat); }
        acc = WEST_and_simp(&s, &acc, n);
    }
    acc
}

/// `WEST_future L a b n`
pub fn WEST_future(l: &ExecRegex, a: usize, b: usize, n: usize) -> (r: ExecRegex)
    requires
        WEST_regex_of_vars(rview(*l), n as nat),
    ensures
        rview(r) == WEST_future_spec(rview(*l), a as nat, b as nat, n as nat),
        WEST_regex_of_vars(rview(r), n as nat),
{
    let ghost v = rview(*l);
    if a > b {
        let r: ExecRegex = Vec::new();
        assert(rview(r) =~= Seq::<TraceRegex>::empty());
        return r;
    }
    let mut acc = shift(l, n, a);
    proof { shift_of_vars(v, n as nat, a as nat); }
    let mut k = a;
    while k < b
        invariant
            a <= k <= b,
            v == rview(*l),
            WEST_regex_of_vars(v, n as nat),
            rview(acc) == WEST_future_spec(v, a as nat, k as nat, n as nat),
            WEST_regex_of_vars(rview(acc), n as nat),
        decreases b - k,
    {
        k += 1;
        let s = shift(l, n, k);
        proof { shift_of_vars(v, n as nat, k as nat); }
        acc = WEST_or_simp(s, acc, n);
    }
    acc
}

/// `WEST_until Lφ Lψ a b n`; keeps `WEST_global Lφ a k` from step to step.
pub fn WEST_until(l_phi: &ExecRegex, l_psi: &ExecRegex, a: usize, b: usize, n: usize) -> (r: ExecRegex)
    requires
        WEST_regex_of_vars(rview(*l_phi), n as nat),
        WEST_regex_of_vars(rview(*l_psi), n as nat),
    ensures
        rview(r) == WEST_until_spec(rview(*l_phi), rview(*l_psi), a as nat, b as nat, n as nat),
        WEST_regex_of_vars(rview(r), n as nat),
{
    let ghost vp = rview(*l_phi);
    let ghost vq = rview(*l_psi);
    if a > b {
        let r: ExecRegex = Vec::new();
        assert(rview(r) =~= Seq::<TraceRegex>::empty());
        return r;
    }
    let mut acc = shift(l_psi, n, a);
    let mut g = shift(l_phi, n, a);
    proof {
        shift_of_vars(vq, n as nat, a as nat);
        shift_of_vars(vp, n as nat, a as nat);
    }
    let mut k = a;
    while k < b
        invariant
            a <= k <= b,
            vp == rview(*l_phi),
            vq == rview(*l_psi),
            WEST_regex_of_vars(vp, n as nat),
            WEST_regex_of_vars(vq, n as nat),
            rview(acc) == WEST_until_spec(vp, vq, a as nat, k as nat, n as nat),
            WEST_regex_of_vars(rview(acc), n as nat),
            k < b ==> rview(g) == WEST_global_spec(vp, a as nat, k as nat, n as nat),
            WEST_regex_of_vars(rview(g), n as nat),
        decreases b - k,
    {
        k += 1;
        let s = shift(l_psi, n, k);
        proof { shift_of_vars(vq, n as nat, k as nat); }
        let step = WEST_and_simp(&g, &s, n);
        acc = WEST_or_simp(acc, step, n);
        if k < b {
            let sp = shift(l_phi, n, k);
            proof { shift_of_vars(vp, n as nat, k as nat); }
            g = WEST_and_simp(&sp, &g, n);
        }
    }
    acc
}

/// `WEST_release_helper Lφ Lψ a ub n`; keeps `WEST_global Lψ a k`.
pub fn WEST_release_helper(l_phi: &ExecRegex, l_psi: &ExecRegex, a: usize, ub: usize, n: usize) -> (r: ExecRegex)
    requires
        WEST_regex_of_vars(rview(*l_phi), n as nat),
        WEST_regex_of_vars(rview(*l_psi), n as nat),
    ensures
        rview(r) == WEST_release_helper_spec(rview(*l_phi), rview(*l_psi), a as nat, ub as nat, n as nat),
        WEST_regex_of_vars(rview(r), n as nat),
{
    let ghost vp = rview(*l_phi);
    let ghost vq = rview(*l_psi);
    if a > ub {
        let r: ExecRegex = Vec::new();
        assert(rview(r) =~= Seq::<TraceRegex>::empty());
        return r;
    }
    let sp = shift(l_phi, n, a);
    let mut gq = shift(l_psi, n, a);
    proof {
        shift_of_vars(vq, n as nat, a as nat);
        shift_of_vars(vp, n as nat, a as nat);
    }
    let mut acc = WEST_and_simp(&sp, &gq, n);
    let mut k = a;
    while k < ub
        invariant
            a <= k <= ub,
            vp == rview(*l_phi),
            vq == rview(*l_psi),
            WEST_regex_of_vars(vp, n as nat),
            WEST_regex_of_vars(vq, n as nat),
            rview(acc) == WEST_release_helper_spec(vp, vq, a as nat, k as nat, n as nat),
            WEST_regex_of_vars(rview(acc), n as nat),
            rview(gq) == WEST_global_spec(vq, a as nat, k as nat, n as nat),
            WEST_regex_of_vars(rview(gq), n as nat),
        decreases ub - k,
    {
        k += 1;
        let sq = shift(l_psi, n, k);
        proof { shift_of_vars(vq, n as nat, k as nat); }
        gq = WEST_and_simp(&sq, &gq, n);
        let sp = shift(l_phi, n, k);
        proof { shift_of_vars(vp, n as nat, k as nat); }
        let step = WEST_and_simp(&gq, &sp, n);
        acc = WEST_or_simp(acc, step, n);
    }
    acc
}

/// `WEST_release Lφ Lψ a b n`
pub fn WEST_release(l_phi: &ExecRegex, l_psi: &ExecRegex, a: usize, b: usize, n: usize) -> (r: ExecRegex)
    requires
        WEST_regex_of_vars(rview(*l_phi), n as nat),
        WEST_regex_of_vars(rview(*l_psi), n as nat),
    ensures
        rview(r) == WEST_release_spec(rview(*l_phi), rview(*l_psi), a as nat, b as nat, n as nat),
        WEST_regex_of_vars(rview(r), n as nat),
{
    let g = WEST_global(l_psi, a, b, n);
    if b > a {
        let h = WEST_release_helper(l_phi, l_psi, a, b - 1, n);
        WEST_or_simp(g, h, n)
    } else {
        g
    }
}

// ---------------------------------------------------------------------------
// WEST_reg
// ---------------------------------------------------------------------------

/// `WEST_reg_aux F n` for `F` in negation normal form (the only input
/// `WEST_reg` gives it; Isabelle's other `Not` cases rewrite to these).
pub fn WEST_reg_aux(f: &Mltl<usize>, n: usize) -> (r: ExecRegex)
    requires
        is_nnf(*f),
    ensures
        rview(r) == WEST_reg_aux_spec(*f, n as nat),
        WEST_regex_of_vars(rview(r), n as nat),
    decreases f,
{
    proof { WEST_reg_aux_of_vars(*f, n as nat); }
    match f {
        Mltl::True => {
            let s = arbitrary_state_exec(n);
            let mut t: ExecTrace = Vec::new();
            t.push(s);
            let mut r: ExecRegex = Vec::new();
            r.push(t);
            assert(s@ =~= Seq::new(n as nat, |j: int| WestBit::S));
            assert(tview(r@[0]) =~= seq![s@]);
            assert(rview(r) =~= seq![seq![Seq::new(n as nat, |j: int| WestBit::S)]]);
            r
        },
        Mltl::False => {
            let r: ExecRegex = Vec::new();
            assert(rview(r) =~= Seq::<TraceRegex>::empty());
            r
        },
        Mltl::Prop(p) => {
            let s = single_state(n, *p, WestBit::One);
            let mut t: ExecTrace = Vec::new();
            t.push(s);
            let mut r: ExecRegex = Vec::new();
            r.push(t);
            assert(tview(r@[0]) =~= seq![s@]);
            assert(rview(r) =~= seq![seq![s@]]);
            r
        },
        Mltl::Not(g) => {
            match &**g {
                Mltl::Prop(p) => {
                    let s = single_state(n, *p, WestBit::Zero);
                    let mut t: ExecTrace = Vec::new();
                    t.push(s);
                    let mut r: ExecRegex = Vec::new();
                    r.push(t);
                    assert(tview(r@[0]) =~= seq![s@]);
                    assert(rview(r) =~= seq![seq![s@]]);
                    r
                },
                _ => {
                    assert(false);
                    Vec::new()
                },
            }
        },
        Mltl::Or(phi, psi) => {
            let x = WEST_reg_aux(phi, n);
            let y = WEST_reg_aux(psi, n);
            WEST_or_simp(x, y, n)
        },
        Mltl::And(phi, psi) => {
            let x = WEST_reg_aux(phi, n);
            let y = WEST_reg_aux(psi, n);
            WEST_and_simp(&x, &y, n)
        },
        Mltl::Future(a, b, phi) => {
            let x = WEST_reg_aux(phi, n);
            WEST_future(&x, *a, *b, n)
        },
        Mltl::Global(a, b, phi) => {
            let x = WEST_reg_aux(phi, n);
            WEST_global(&x, *a, *b, n)
        },
        Mltl::Until(phi, a, b, psi) => {
            let x = WEST_reg_aux(phi, n);
            let y = WEST_reg_aux(psi, n);
            WEST_until(&x, &y, *a, *b, n)
        },
        Mltl::Release(phi, a, b, psi) => {
            let x = WEST_reg_aux(phi, n);
            let y = WEST_reg_aux(psi, n);
            WEST_release(&x, &y, *a, *b, n)
        },
    }
}

/// `WEST_num_vars F` (needs every atom below `usize::MAX`).
pub fn WEST_num_vars(f: &Mltl<usize>) -> (r: usize)
    requires
        WEST_num_vars_spec(*f) <= usize::MAX,
    ensures
        r == WEST_num_vars_spec(*f),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False => 1,
        Mltl::Prop(p) => *p + 1,
        Mltl::Not(phi) => WEST_num_vars(phi),
        Mltl::Future(_, _, phi) => WEST_num_vars(phi),
        Mltl::Global(_, _, phi) => WEST_num_vars(phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            let x = WEST_num_vars(phi);
            let y = WEST_num_vars(psi);
            if x >= y { x } else { y }
        },
        Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            let x = WEST_num_vars(phi);
            let y = WEST_num_vars(psi);
            if x >= y { x } else { y }
        },
    }
}

/// Not in Isabelle: the sum of all upper bounds in `F`. `complen_mltl` of
/// every subformula is at most this plus one (`complen_le_bound_sum`), so
/// `bound_sum F < usize::MAX` lets `complen` run without overflow.
pub open spec fn bound_sum(f: Mltl<usize>) -> nat
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 0,
        Mltl::Not(phi) => bound_sum(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => bound_sum(*phi) + bound_sum(*psi),
        Mltl::Future(_, b, phi) | Mltl::Global(_, b, phi) => (b + bound_sum(*phi)) as nat,
        Mltl::Until(phi, _, b, psi) | Mltl::Release(phi, _, b, psi) => (b + bound_sum(*phi) + bound_sum(*psi)) as nat,
    }
}

pub proof fn complen_le_bound_sum(f: Mltl<usize>)
    ensures
        complen_mltl(f) <= bound_sum(f) + 1,
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(phi) => complen_le_bound_sum(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            complen_le_bound_sum(*phi);
            complen_le_bound_sum(*psi);
        },
        Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => complen_le_bound_sum(*phi),
        Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            complen_le_bound_sum(*phi);
            complen_le_bound_sum(*psi);
        },
    }
}

/// `bound_sum F`, or `None` if it does not fit in `usize`.
pub fn bound_sum_checked(f: &Mltl<usize>) -> (r: Option<usize>)
    ensures
        match r {
            Some(x) => x == bound_sum(*f),
            None => bound_sum(*f) > usize::MAX,
        },
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => Some(0),
        Mltl::Not(phi) => bound_sum_checked(phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            let x = bound_sum_checked(phi)?;
            let y = bound_sum_checked(psi)?;
            if x > usize::MAX - y { None } else { Some(x + y) }
        },
        Mltl::Future(_, b, phi) | Mltl::Global(_, b, phi) => {
            let x = bound_sum_checked(phi)?;
            if x > usize::MAX - *b { None } else { Some(*b + x) }
        },
        Mltl::Until(phi, _, b, psi) | Mltl::Release(phi, _, b, psi) => {
            let x = bound_sum_checked(phi)?;
            let y = bound_sum_checked(psi)?;
            if x > usize::MAX - y { return None; }
            let s = x + y;
            if s > usize::MAX - *b { None } else { Some(*b + s) }
        },
    }
}

/// `complen_mltl F`
pub fn complen(f: &Mltl<usize>) -> (r: usize)
    requires
        bound_sum(*f) < usize::MAX,
    ensures
        r == complen_mltl(*f),
    decreases f,
{
    proof { complen_le_bound_sum(*f); }
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(phi) => complen(phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            let x = complen(phi);
            let y = complen(psi);
            if x >= y { x } else { y }
        },
        Mltl::Future(_, b, phi) | Mltl::Global(_, b, phi) => {
            proof { complen_le_bound_sum(**phi); }
            *b + complen(phi)
        },
        Mltl::Until(phi, _, b, psi) | Mltl::Release(phi, _, b, psi) => {
            proof {
                complen_le_bound_sum(**phi);
                complen_le_bound_sum(**psi);
            }
            let x = complen(phi);
            let y = complen(psi);
            let x1 = if x >= 1 { x - 1 } else { 0 };
            *b + if x1 >= y { x1 } else { y }
        },
    }
}

/// The satisfying traces of `f` as a list of trace regexes: Isabelle's
/// `WEST_reg f`. A trace at least `complen_mltl f` long satisfies `f`
/// exactly when it matches one of the returned regexes.
pub fn WEST_reg(f: &Mltl<usize>) -> (r: ExecRegex)
    requires
        WEST_num_vars_spec(*f) <= usize::MAX,
    ensures
        // Computes exactly Isabelle's `WEST_reg f` ...
        rview(r) == WEST_reg_spec(*f),
        // ... with `WEST_num_vars f` entries per state ...
        WEST_regex_of_vars(rview(r), WEST_num_vars_spec(*f)),
        // ... and is correct (`WEST_correct_v2`).
        intervals_welldef(*f) ==> forall|pi: WestTrace| pi.len() >= complen_mltl(*f) ==>
            (#[trigger] west_match(pi, rview(r)) <==> semantics_mltl(pi, *f)),
{
    let g = convert_nnf(f);
    let n = WEST_num_vars(f);
    let r = WEST_reg_aux(&g, n);
    proof {
        if intervals_welldef(*f) {
            assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                (#[trigger] west_match(pi, rview(r)) <==> semantics_mltl(pi, *f)) by {
                WEST_correct_v2(pi, *f);
            }
        }
    }
    r
}

/// Isabelle's `simp_pad_WEST_reg f`: `WEST_reg f` with every regex padded to
/// `complen_mltl f`, then simplified (padding lets more regexes merge).
pub fn simp_pad_WEST_reg(f: &Mltl<usize>) -> (r: ExecRegex)
    requires
        WEST_num_vars_spec(*f) <= usize::MAX,
        bound_sum(*f) < usize::MAX,
    ensures
        rview(r) == simp_pad_WEST_reg_spec(*f),
        WEST_regex_of_vars(rview(r), WEST_num_vars_spec(*f)),
        // Correctness (`WEST_correct_pad`).
        intervals_welldef(*f) ==> forall|pi: WestTrace| pi.len() >= complen_mltl(*f) ==>
            (#[trigger] west_match(pi, rview(r)) <==> semantics_mltl(pi, *f)),
{
    let unpadded = WEST_reg(f);
    let c = complen(f);
    let n = WEST_num_vars(f);
    let ghost uv = rview(unpadded);
    let ghost padded_spec = pad_WEST_reg_spec(*f);
    let mut padded: ExecRegex = Vec::with_capacity(unpadded.len());
    let mut i: usize = 0;
    while i < unpadded.len()
        invariant
            i <= unpadded.len(),
            uv == rview(unpadded),
            uv == WEST_reg_spec(*f),
            c == complen_mltl(*f),
            n == WEST_num_vars_spec(*f),
            padded_spec == pad_WEST_reg_spec(*f),
            rview(padded) == padded_spec.subrange(0, i as int),
        decreases unpadded.len() - i,
    {
        let t = copy_trace(&unpadded[i]);
        assert(tview(t) == uv[i as int]);
        let p = if t.len() < c {
            let k = c - t.len();
            pad(t, n, k)
        } else {
            t
        };
        assert(tview(p) == padded_spec[i as int]);
        let ghost pv = tview(p);
        let ghost before = rview(padded);
        padded.push(p);
        assert(rview(padded) =~= before.push(pv));
        i += 1;
        assert(rview(padded) =~= padded_spec.subrange(0, i as int));
    }
    assert(rview(padded) =~= padded_spec);
    proof {
        pad_WEST_reg_of_vars(*f);
    }
    let r = WEST_simp(padded, n);
    proof {
        if intervals_welldef(*f) {
            assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                (#[trigger] west_match(pi, rview(r)) <==> semantics_mltl(pi, *f)) by {
                WEST_correct_pad(pi, *f);
            }
        }
        simp_correct(Seq::empty(), padded_spec, n as nat);
    }
    r
}

} // verus!
