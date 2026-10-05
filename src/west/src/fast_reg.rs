//! Fast WEST, part 2: temporal operators and the top-level `fast_reg`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithms::*;
use crate::matching::*;
use crate::temporal::*;
use crate::correct::*;
use crate::packed::*;
use crate::exec::*;
use crate::fast::*;

verus! {

proof fn fits_mono(n: nat, len: nat, len2: nat)
    requires
        len <= len2,
        fits(n, len2),
    ensures
        fits(n, len),
{
    assert(2 * n * len <= 2 * n * len2) by (nonlinear_arith) requires len <= len2;
}

/// `match π (shift L n k) ⟷ shifted π L k`, for a packed list.
proof fn p_shift_match(pi: WestTrace, l: Packed, s: Packed, k: usize)
    requires
        pwf(l),
        pview(s) == shift_spec(pview(l), l.n as nat, k as nat),
    ensures
        west_match(pi, pview(s)) <==> shifted(pi, pview(l), k as nat),
{
    shift_correct(pi, pview(l), l.n as nat, k as nat);
}

// ---------------------------------------------------------------------------
// G and F
// ---------------------------------------------------------------------------

/// `G[a,b]` on a packed list: length `b + len`.
pub fn p_global(l: &Packed, a: usize, b: usize) -> (out: Packed)
    requires
        pwf(*l),
        a <= b,
        fits(l.n as nat, (b + l.len) as nat),
    ensures
        pwf(out),
        out.n == l.n,
        out.len == b + l.len,
        forall|pi: WestTrace| pi.len() >= out.len ==>
            (#[trigger] west_match(pi, pview(out)) <==> all_shifted(pi, pview(*l), a as nat, b as nat)),
{
    let ghost lv = pview(*l);
    proof { fits_mono(l.n as nat, (a + l.len) as nat, (b + l.len) as nat); }
    let mut acc = p_shift(l, a);
    proof {
        assert forall|pi: WestTrace| pi.len() >= acc.len implies
            (#[trigger] west_match(pi, pview(acc)) <==> all_shifted(pi, lv, a as nat, a as nat)) by {
            p_shift_match(pi, *l, acc, a);
            if shifted(pi, lv, a as nat) {
                assert forall|i: nat| a <= i <= a implies #[trigger] shifted(pi, lv, i) by {}
            }
        }
    }
    let mut k = a;
    while k < b
        invariant
            pwf(*l),
            lv == pview(*l),
            a <= k <= b,
            fits(l.n as nat, (b + l.len) as nat),
            pwf(acc),
            acc.n == l.n,
            acc.len == k + l.len,
            forall|pi: WestTrace| pi.len() >= acc.len ==>
                (#[trigger] west_match(pi, pview(acc)) <==> all_shifted(pi, lv, a as nat, k as nat)),
        decreases b - k,
    {
        k += 1;
        proof { fits_mono(l.n as nat, (k + l.len) as nat, (b + l.len) as nat); }
        let s = p_shift(l, k);
        let prev = acc;
        acc = p_and(&s, &prev);
        proof {
            assert forall|pi: WestTrace| pi.len() >= acc.len implies
                (#[trigger] west_match(pi, pview(acc)) <==> all_shifted(pi, lv, a as nat, k as nat)) by {
                p_shift_match(pi, *l, s, k);
                assert(west_match(pi, pview(prev)) <==> all_shifted(pi, lv, a as nat, (k - 1) as nat));
                if all_shifted(pi, lv, a as nat, (k - 1) as nat) && shifted(pi, lv, k as nat) {
                    assert forall|i: nat| a <= i <= k implies #[trigger] shifted(pi, lv, i) by {
                        if i < k { assert(a <= i <= k - 1); }
                    }
                }
                if all_shifted(pi, lv, a as nat, k as nat) {
                    assert(shifted(pi, lv, k as nat));
                    assert forall|i: nat| a <= i <= (k - 1) as nat implies #[trigger] shifted(pi, lv, i) by {}
                }
            }
        }
    }
    acc
}

/// `F[a,b]` on a packed list: length `b + len`.
pub fn p_future(l: &Packed, a: usize, b: usize) -> (out: Packed)
    requires
        pwf(*l),
        a <= b,
        fits(l.n as nat, (b + l.len) as nat),
    ensures
        pwf(out),
        out.n == l.n,
        out.len == b + l.len,
        forall|pi: WestTrace| pi.len() >= out.len ==>
            (#[trigger] west_match(pi, pview(out)) <==> some_shifted(pi, pview(*l), a as nat, b as nat)),
{
    let ghost lv = pview(*l);
    proof { fits_mono(l.n as nat, (a + l.len) as nat, (b + l.len) as nat); }
    let mut acc = p_shift(l, a);
    proof {
        assert forall|pi: WestTrace| pi.len() >= acc.len implies
            (#[trigger] west_match(pi, pview(acc)) <==> some_shifted(pi, lv, a as nat, a as nat)) by {
            p_shift_match(pi, *l, acc, a);
            if some_shifted(pi, lv, a as nat, a as nat) {
                let i = choose|i: nat| a <= i <= a && #[trigger] shifted(pi, lv, i);
                assert(i == a);
            }
        }
    }
    let mut k = a;
    while k < b
        invariant
            pwf(*l),
            lv == pview(*l),
            a <= k <= b,
            fits(l.n as nat, (b + l.len) as nat),
            pwf(acc),
            acc.n == l.n,
            acc.len == k + l.len,
            forall|pi: WestTrace| pi.len() >= acc.len ==>
                (#[trigger] west_match(pi, pview(acc)) <==> some_shifted(pi, lv, a as nat, k as nat)),
        decreases b - k,
    {
        k += 1;
        proof { fits_mono(l.n as nat, (k + l.len) as nat, (b + l.len) as nat); }
        let s = p_shift(l, k);
        let ghost sv = s;
        let ghost prev = acc;
        acc = p_or(s, acc);
        proof {
            assert forall|pi: WestTrace| pi.len() >= acc.len implies
                (#[trigger] west_match(pi, pview(acc)) <==> some_shifted(pi, lv, a as nat, k as nat)) by {
                p_shift_match(pi, *l, sv, k);
                assert(west_match(pi, pview(prev)) <==> some_shifted(pi, lv, a as nat, (k - 1) as nat));
                if some_shifted(pi, lv, a as nat, k as nat) {
                    let i = choose|i: nat| a <= i <= k && #[trigger] shifted(pi, lv, i);
                    if i < k { assert(a <= i <= (k - 1) as nat); }
                }
                if some_shifted(pi, lv, a as nat, (k - 1) as nat) {
                    let i = choose|i: nat| a <= i <= (k - 1) as nat && #[trigger] shifted(pi, lv, i);
                    assert(a <= i <= k);
                }
                if shifted(pi, lv, k as nat) {
                    assert(a <= k <= k);
                }
            }
        }
    }
    acc
}

// ---------------------------------------------------------------------------
// U and R
// ---------------------------------------------------------------------------

pub open spec fn max_us(x: usize, y: usize) -> usize {
    if x >= y { x } else { y }
}

/// `Lφ U[a,b] Lψ` on packed lists: length at most `b + max(len φ - 1, len ψ)`.
pub fn p_until(lp: &Packed, lq: &Packed, a: usize, b: usize) -> (out: Packed)
    requires
        pwf(*lp),
        pwf(*lq),
        lp.n == lq.n,
        a <= b,
        fits(lp.n as nat, (b + lp.len) as nat),
        fits(lp.n as nat, (b + lq.len) as nat),
    ensures
        pwf(out),
        out.n == lp.n,
        out.len <= b + max_us((lp.len - 1) as usize, lq.len),
        forall|pi: WestTrace| pi.len() >= b + max_us((lp.len - 1) as usize, lq.len) ==>
            (#[trigger] west_match(pi, pview(out)) <==> until_shifted(pi, pview(*lp), pview(*lq), a as nat, b as nat)),
{
    let ghost vp = pview(*lp);
    let ghost vq = pview(*lq);
    let m = if lp.len - 1 >= lq.len { lp.len - 1 } else { lq.len };
    proof {
        fits_mono(lp.n as nat, (a + lp.len) as nat, (b + lp.len) as nat);
        fits_mono(lp.n as nat, (a + lq.len) as nat, (b + lq.len) as nat);
    }
    let mut acc = p_shift(lq, a);
    let mut g = p_shift(lp, a);
    proof {
        assert forall|pi: WestTrace| pi.len() >= a + m implies
            (#[trigger] west_match(pi, pview(acc)) <==> until_shifted(pi, vp, vq, a as nat, a as nat)) by {
            p_shift_match(pi, *lq, acc, a);
            if shifted(pi, vq, a as nat) {
                assert(forall|j: nat| a <= j < a ==> #[trigger] shifted(pi, vp, j));
            }
            if until_shifted(pi, vp, vq, a as nat, a as nat) {
                let i = choose|i: nat| a <= i <= a && #[trigger] shifted(pi, vq, i)
                    && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, vp, j);
                assert(i == a);
            }
        }
        assert forall|pi: WestTrace| pi.len() >= g.len implies
            (#[trigger] west_match(pi, pview(g)) <==> all_shifted(pi, vp, a as nat, a as nat)) by {
            p_shift_match(pi, *lp, g, a);
            if shifted(pi, vp, a as nat) {
                assert forall|i: nat| a <= i <= a implies #[trigger] shifted(pi, vp, i) by {}
            }
        }
    }
    let mut k = a;
    while k < b
        invariant
            pwf(*lp),
            pwf(*lq),
            lp.n == lq.n,
            vp == pview(*lp),
            vq == pview(*lq),
            m == max_us((lp.len - 1) as usize, lq.len),
            a <= k <= b,
            fits(lp.n as nat, (b + lp.len) as nat),
            fits(lp.n as nat, (b + lq.len) as nat),
            pwf(acc),
            acc.n == lp.n,
            acc.len <= k + m,
            forall|pi: WestTrace| pi.len() >= k + m ==>
                (#[trigger] west_match(pi, pview(acc)) <==> until_shifted(pi, vp, vq, a as nat, k as nat)),
            pwf(g),
            g.n == lp.n,
            k < b ==> g.len == k + lp.len,
            k < b ==> forall|pi: WestTrace| pi.len() >= g.len ==>
                (#[trigger] west_match(pi, pview(g)) <==> all_shifted(pi, vp, a as nat, k as nat)),
        decreases b - k,
    {
        k += 1;
        proof { fits_mono(lp.n as nat, (k + lq.len) as nat, (b + lq.len) as nat); }
        let s = p_shift(lq, k);
        let step = p_and(&g, &s);
        let ghost prev = acc;
        let ghost stepv = step;
        acc = p_or(acc, step);
        proof {
            assert forall|pi: WestTrace| pi.len() >= k + m implies
                (#[trigger] west_match(pi, pview(acc)) <==> until_shifted(pi, vp, vq, a as nat, k as nat)) by {
                p_shift_match(pi, *lq, s, k);
                assert(west_match(pi, pview(prev)) <==> until_shifted(pi, vp, vq, a as nat, (k - 1) as nat));
                assert(west_match(pi, pview(g)) <==> all_shifted(pi, vp, a as nat, (k - 1) as nat));
                assert(west_match(pi, pview(stepv)) <==> (all_shifted(pi, vp, a as nat, (k - 1) as nat) && shifted(pi, vq, k as nat)));
                if until_shifted(pi, vp, vq, a as nat, k as nat) {
                    let i = choose|i: nat| a <= i <= k && #[trigger] shifted(pi, vq, i)
                        && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, vp, j);
                    if i < k {
                        assert(a <= i <= (k - 1) as nat);
                    } else {
                        assert forall|j: nat| a <= j <= (k - 1) as nat implies #[trigger] shifted(pi, vp, j) by {
                            assert(a <= j < i);
                        }
                    }
                }
                if until_shifted(pi, vp, vq, a as nat, (k - 1) as nat) {
                    let i = choose|i: nat| a <= i <= (k - 1) as nat && #[trigger] shifted(pi, vq, i)
                        && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, vp, j);
                    assert(a <= i <= k);
                }
                if all_shifted(pi, vp, a as nat, (k - 1) as nat) && shifted(pi, vq, k as nat) {
                    assert forall|j: nat| a <= j < k implies #[trigger] shifted(pi, vp, j) by {
                        assert(a <= j <= (k - 1) as nat);
                    }
                    assert(a <= k <= k);
                }
            }
        }
        if k < b {
            proof { fits_mono(lp.n as nat, (k + lp.len) as nat, (b + lp.len) as nat); }
            let sp = p_shift(lp, k);
            let gprev = g;
            g = p_and(&sp, &gprev);
            proof {
                assert forall|pi: WestTrace| pi.len() >= g.len implies
                    (#[trigger] west_match(pi, pview(g)) <==> all_shifted(pi, vp, a as nat, k as nat)) by {
                    p_shift_match(pi, *lp, sp, k);
                    assert(west_match(pi, pview(gprev)) <==> all_shifted(pi, vp, a as nat, (k - 1) as nat));
                    if all_shifted(pi, vp, a as nat, (k - 1) as nat) && shifted(pi, vp, k as nat) {
                        assert forall|i: nat| a <= i <= k implies #[trigger] shifted(pi, vp, i) by {
                            if i < k { assert(a <= i <= (k - 1) as nat); }
                        }
                    }
                    if all_shifted(pi, vp, a as nat, k as nat) {
                        assert(shifted(pi, vp, k as nat));
                        assert forall|i: nat| a <= i <= (k - 1) as nat implies #[trigger] shifted(pi, vp, i) by {}
                    }
                }
            }
        }
    }
    acc
}

/// `Lφ` released-helper on `[a, ub]`: length at most `ub + max(len φ, len ψ)`.
fn p_release_helper(lp: &Packed, lq: &Packed, a: usize, ub: usize) -> (out: Packed)
    requires
        pwf(*lp),
        pwf(*lq),
        lp.n == lq.n,
        a <= ub,
        fits(lp.n as nat, (ub + lp.len) as nat),
        fits(lp.n as nat, (ub + lq.len) as nat),
    ensures
        pwf(out),
        out.n == lp.n,
        out.len <= ub + max_us(lp.len, lq.len),
        forall|pi: WestTrace| pi.len() >= ub + max_us(lp.len, lq.len) ==>
            (#[trigger] west_match(pi, pview(out)) <==> release_helper_shifted(pi, pview(*lp), pview(*lq), a as nat, ub as nat)),
{
    let ghost vp = pview(*lp);
    let ghost vq = pview(*lq);
    let m = if lp.len >= lq.len { lp.len } else { lq.len };
    proof {
        fits_mono(lp.n as nat, (a + lp.len) as nat, (ub + lp.len) as nat);
        fits_mono(lp.n as nat, (a + lq.len) as nat, (ub + lq.len) as nat);
    }
    let sp = p_shift(lp, a);
    let mut gq = p_shift(lq, a);
    let mut acc = p_and(&sp, &gq);
    proof {
        assert forall|pi: WestTrace| pi.len() >= a + m implies
            (#[trigger] west_match(pi, pview(acc)) <==> release_helper_shifted(pi, vp, vq, a as nat, a as nat)) by {
            p_shift_match(pi, *lp, sp, a);
            p_shift_match(pi, *lq, gq, a);
            if shifted(pi, vp, a as nat) && shifted(pi, vq, a as nat) {
                assert(forall|k: nat| a <= k <= a ==> #[trigger] shifted(pi, vq, k));
                assert(a <= a <= a);
            }
            if release_helper_shifted(pi, vp, vq, a as nat, a as nat) {
                let j = choose|j: nat| a <= j <= a && #[trigger] shifted(pi, vp, j)
                    && forall|k: nat| a <= k <= j ==> #[trigger] shifted(pi, vq, k);
                assert(j == a);
                assert(shifted(pi, vq, a as nat));
            }
        }
        assert forall|pi: WestTrace| pi.len() >= gq.len implies
            (#[trigger] west_match(pi, pview(gq)) <==> all_shifted(pi, vq, a as nat, a as nat)) by {
            p_shift_match(pi, *lq, gq, a);
            if shifted(pi, vq, a as nat) {
                assert forall|i: nat| a <= i <= a implies #[trigger] shifted(pi, vq, i) by {}
            }
        }
    }
    let mut k = a;
    while k < ub
        invariant
            pwf(*lp),
            pwf(*lq),
            lp.n == lq.n,
            vp == pview(*lp),
            vq == pview(*lq),
            m == max_us(lp.len, lq.len),
            a <= k <= ub,
            fits(lp.n as nat, (ub + lp.len) as nat),
            fits(lp.n as nat, (ub + lq.len) as nat),
            pwf(acc),
            acc.n == lp.n,
            acc.len <= k + m,
            forall|pi: WestTrace| pi.len() >= k + m ==>
                (#[trigger] west_match(pi, pview(acc)) <==> release_helper_shifted(pi, vp, vq, a as nat, k as nat)),
            pwf(gq),
            gq.n == lp.n,
            gq.len == k + lq.len,
            forall|pi: WestTrace| pi.len() >= gq.len ==>
                (#[trigger] west_match(pi, pview(gq)) <==> all_shifted(pi, vq, a as nat, k as nat)),
        decreases ub - k,
    {
        k += 1;
        proof {
            fits_mono(lp.n as nat, (k + lq.len) as nat, (ub + lq.len) as nat);
            fits_mono(lp.n as nat, (k + lp.len) as nat, (ub + lp.len) as nat);
        }
        let sq = p_shift(lq, k);
        let gprev = gq;
        gq = p_and(&sq, &gprev);
        proof {
            assert forall|pi: WestTrace| pi.len() >= gq.len implies
                (#[trigger] west_match(pi, pview(gq)) <==> all_shifted(pi, vq, a as nat, k as nat)) by {
                p_shift_match(pi, *lq, sq, k);
                assert(west_match(pi, pview(gprev)) <==> all_shifted(pi, vq, a as nat, (k - 1) as nat));
                if all_shifted(pi, vq, a as nat, (k - 1) as nat) && shifted(pi, vq, k as nat) {
                    assert forall|i: nat| a <= i <= k implies #[trigger] shifted(pi, vq, i) by {
                        if i < k { assert(a <= i <= (k - 1) as nat); }
                    }
                }
                if all_shifted(pi, vq, a as nat, k as nat) {
                    assert(shifted(pi, vq, k as nat));
                    assert forall|i: nat| a <= i <= (k - 1) as nat implies #[trigger] shifted(pi, vq, i) by {}
                }
            }
        }
        let spk = p_shift(lp, k);
        let step = p_and(&gq, &spk);
        let ghost prev = acc;
        acc = p_or(acc, step);
        proof {
            assert forall|pi: WestTrace| pi.len() >= k + m implies
                (#[trigger] west_match(pi, pview(acc)) <==> release_helper_shifted(pi, vp, vq, a as nat, k as nat)) by {
                p_shift_match(pi, *lp, spk, k);
                assert(west_match(pi, pview(prev)) <==> release_helper_shifted(pi, vp, vq, a as nat, (k - 1) as nat));
                assert(west_match(pi, pview(gq)) <==> all_shifted(pi, vq, a as nat, k as nat));
                if release_helper_shifted(pi, vp, vq, a as nat, k as nat) {
                    let j = choose|j: nat| a <= j <= k && #[trigger] shifted(pi, vp, j)
                        && forall|kk: nat| a <= kk <= j ==> #[trigger] shifted(pi, vq, kk);
                    if j < k {
                        assert(a <= j <= (k - 1) as nat);
                    } else {
                        assert forall|i: nat| a <= i <= k implies #[trigger] shifted(pi, vq, i) by {}
                    }
                }
                if release_helper_shifted(pi, vp, vq, a as nat, (k - 1) as nat) {
                    let j = choose|j: nat| a <= j <= (k - 1) as nat && #[trigger] shifted(pi, vp, j)
                        && forall|kk: nat| a <= kk <= j ==> #[trigger] shifted(pi, vq, kk);
                    assert(a <= j <= k);
                }
                if all_shifted(pi, vq, a as nat, k as nat) && shifted(pi, vp, k as nat) {
                    assert(forall|kk: nat| a <= kk <= k ==> #[trigger] shifted(pi, vq, kk));
                    assert(a <= k <= k);
                }
            }
        }
    }
    acc
}

/// `Lφ R[a,b] Lψ` on packed lists: length at most `b + max(len φ - 1, len ψ)`.
pub fn p_release(lp: &Packed, lq: &Packed, a: usize, b: usize) -> (out: Packed)
    requires
        pwf(*lp),
        pwf(*lq),
        lp.n == lq.n,
        a <= b,
        fits(lp.n as nat, (b + lp.len) as nat),
        fits(lp.n as nat, (b + lq.len) as nat),
    ensures
        pwf(out),
        out.n == lp.n,
        out.len <= b + max_us((lp.len - 1) as usize, lq.len),
        forall|pi: WestTrace| pi.len() >= b + max_us((lp.len - 1) as usize, lq.len) ==>
            (#[trigger] west_match(pi, pview(out)) <==> release_shifted(pi, pview(*lp), pview(*lq), a as nat, b as nat)),
{
    let g = p_global(lq, a, b);
    if b > a {
        proof {
            fits_mono(lp.n as nat, (b - 1 + lp.len) as nat, (b + lp.len) as nat);
            fits_mono(lp.n as nat, (b - 1 + lq.len) as nat, (b + lq.len) as nat);
        }
        let h = p_release_helper(lp, lq, a, b - 1);
        let ghost gv = g;
        let ghost hv = h;
        let out = p_or(g, h);
        proof {
            assert forall|pi: WestTrace| pi.len() >= b + max_us((lp.len - 1) as usize, lq.len) implies
                (#[trigger] west_match(pi, pview(out)) <==> release_shifted(pi, pview(*lp), pview(*lq), a as nat, b as nat)) by {
                assert(west_match(pi, pview(gv)) <==> all_shifted(pi, pview(*lq), a as nat, b as nat));
                assert(west_match(pi, pview(hv)) <==> release_helper_shifted(pi, pview(*lp), pview(*lq), a as nat, (b - 1) as nat));
            }
        }
        out
    } else {
        proof {
            assert forall|pi: WestTrace| pi.len() >= b + max_us((lp.len - 1) as usize, lq.len) implies
                (#[trigger] west_match(pi, pview(g)) <==> release_shifted(pi, pview(*lp), pview(*lq), a as nat, b as nat)) by {
                assert(west_match(pi, pview(g)) <==> all_shifted(pi, pview(*lq), a as nat, b as nat));
            }
        }
        g
    }
}

// ---------------------------------------------------------------------------
// The formula recursion
// ---------------------------------------------------------------------------

/// `bound_sum` of a subformula is at most that of the formula.
proof fn bound_sum_children(f: Mltl<usize>)
    ensures
        match f {
            Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => bound_sum(*g) <= bound_sum(f),
            Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) =>
                bound_sum(*g) <= bound_sum(f) && bound_sum(*h) <= bound_sum(f),
            _ => true,
        },
{
}

/// Fast `WEST_reg_aux` on an NNF formula. The result has length at most
/// `complen φ`, and on traces at least `complen φ` long matches exactly
/// the traces satisfying `φ`.
pub fn p_reg(f: &Mltl<usize>, n: usize) -> (out: Packed)
    requires
        is_nnf(*f),
        intervals_welldef(*f),
        WEST_num_vars_spec(*f) <= n,
        fits(n as nat, bound_sum(*f) + 1),
    ensures
        pwf(out),
        out.n == n,
        out.len <= complen_mltl(*f),
        forall|pi: WestTrace| pi.len() >= complen_mltl(*f) ==>
            (#[trigger] west_match(pi, pview(out)) <==> semantics_mltl(pi, *f)),
    decreases f,
{
    proof {
        complen_le_bound_sum(*f);
        complen_geq_one(*f);
        bound_sum_children(*f);
        WEST_num_vars_pos(*f);
        fits_mono(n as nat, 1, bound_sum(*f) + 1);
    }
    match f {
        Mltl::True => {
            let r = p_true(n);
            proof {
                assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                    (#[trigger] west_match(pi, pview(r)) <==> semantics_mltl(pi, *f)) by {
                    WEST_reg_aux_correct(pi, *f, n as nat);
                }
            }
            r
        },
        Mltl::False => {
            let r = p_false(n);
            proof {
                assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                    (#[trigger] west_match(pi, pview(r)) <==> semantics_mltl(pi, *f)) by {
                    WEST_reg_aux_correct(pi, *f, n as nat);
                }
            }
            r
        },
        Mltl::Prop(p) => {
            let r = p_literal(n, *p, true);
            proof {
                assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                    (#[trigger] west_match(pi, pview(r)) <==> semantics_mltl(pi, *f)) by {
                    WEST_reg_aux_correct(pi, *f, n as nat);
                }
            }
            r
        },
        Mltl::Not(g) => {
            match &**g {
                Mltl::Prop(p) => {
                    proof { reveal_with_fuel(WEST_num_vars_spec, 2); }
                    let r = p_literal(n, *p, false);
                    proof {
                        assert(*f == Mltl::Not(Box::new(Mltl::<usize>::Prop(*p))));
                        assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                            (#[trigger] west_match(pi, pview(r)) <==> semantics_mltl(pi, *f)) by {
                            WEST_reg_aux_correct(pi, *f, n as nat);
                        }
                    }
                    r
                },
                _ => {
                    assert(false);
                    p_false(n)
                },
            }
        },
        Mltl::And(phi, psi) => {
            proof {
                fits_mono(n as nat, bound_sum(**phi) + 1, bound_sum(*f) + 1);
                fits_mono(n as nat, bound_sum(**psi) + 1, bound_sum(*f) + 1);
            }
            let x = p_reg(phi, n);
            let y = p_reg(psi, n);
            let r = p_and(&x, &y);
            r
        },
        Mltl::Or(phi, psi) => {
            proof {
                fits_mono(n as nat, bound_sum(**phi) + 1, bound_sum(*f) + 1);
                fits_mono(n as nat, bound_sum(**psi) + 1, bound_sum(*f) + 1);
            }
            let x = p_reg(phi, n);
            let y = p_reg(psi, n);
            let r = p_or(x, y);
            r
        },
        Mltl::Future(a, b, phi) => {
            proof { fits_mono(n as nat, bound_sum(**phi) + 1, bound_sum(*f) + 1); }
            let x = p_reg(phi, n);
            proof { fits_mono(n as nat, (*b + x.len) as nat, bound_sum(*f) + 1); }
            let r = p_future(&x, *a, *b);
            proof {
                let xv = pview(x);
                assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                    (#[trigger] west_match(pi, pview(r)) <==> semantics_mltl(pi, *f)) by {
                    assert forall|i: nat| *a <= i <= *b implies
                        (#[trigger] shifted(pi, xv, i) <==> semantics_mltl(drop(pi, i), **phi)) by {
                        assert(drop(pi, i).len() >= complen_mltl(**phi));
                    }
                    future_sem(pi, xv, **phi, *a, *b);
                }
            }
            r
        },
        Mltl::Global(a, b, phi) => {
            proof { fits_mono(n as nat, bound_sum(**phi) + 1, bound_sum(*f) + 1); }
            let x = p_reg(phi, n);
            proof { fits_mono(n as nat, (*b + x.len) as nat, bound_sum(*f) + 1); }
            let r = p_global(&x, *a, *b);
            proof {
                let xv = pview(x);
                assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                    (#[trigger] west_match(pi, pview(r)) <==> semantics_mltl(pi, *f)) by {
                    assert forall|i: nat| *a <= i <= *b implies
                        (#[trigger] shifted(pi, xv, i) <==> semantics_mltl(drop(pi, i), **phi)) by {
                        assert(drop(pi, i).len() >= complen_mltl(**phi));
                    }
                    global_sem(pi, xv, **phi, *a, *b);
                }
            }
            r
        },
        Mltl::Until(phi, a, b, psi) => {
            proof {
                fits_mono(n as nat, bound_sum(**phi) + 1, bound_sum(*f) + 1);
                fits_mono(n as nat, bound_sum(**psi) + 1, bound_sum(*f) + 1);
            }
            let x = p_reg(phi, n);
            let y = p_reg(psi, n);
            proof {
                complen_geq_one(**phi);
                complen_le_bound_sum(**phi);
                complen_le_bound_sum(**psi);
                fits_mono(n as nat, (*b + x.len) as nat, bound_sum(*f) + 1);
                fits_mono(n as nat, (*b + y.len) as nat, bound_sum(*f) + 1);
            }
            let r = p_until(&x, &y, *a, *b);
            proof {
                let (xv, yv) = (pview(x), pview(y));
                assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                    (#[trigger] west_match(pi, pview(r)) <==> semantics_mltl(pi, *f)) by {
                    assert forall|i: nat| *a <= i <= *b implies
                        (#[trigger] shifted(pi, yv, i) <==> semantics_mltl(drop(pi, i), **psi)) by {
                        assert(drop(pi, i).len() >= complen_mltl(**psi));
                    }
                    assert forall|j: nat| *a <= j < *b implies
                        (#[trigger] shifted(pi, xv, j) <==> semantics_mltl(drop(pi, j), **phi)) by {
                        assert(drop(pi, j).len() >= complen_mltl(**phi));
                    }
                    until_sem(pi, xv, yv, **phi, **psi, *a, *b);
                }
            }
            r
        },
        Mltl::Release(phi, a, b, psi) => {
            proof {
                fits_mono(n as nat, bound_sum(**phi) + 1, bound_sum(*f) + 1);
                fits_mono(n as nat, bound_sum(**psi) + 1, bound_sum(*f) + 1);
            }
            let x = p_reg(phi, n);
            let y = p_reg(psi, n);
            proof {
                complen_geq_one(**phi);
                complen_le_bound_sum(**phi);
                complen_le_bound_sum(**psi);
                fits_mono(n as nat, (*b + x.len) as nat, bound_sum(*f) + 1);
                fits_mono(n as nat, (*b + y.len) as nat, bound_sum(*f) + 1);
            }
            let r = p_release(&x, &y, *a, *b);
            proof {
                let (xv, yv) = (pview(x), pview(y));
                assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                    (#[trigger] west_match(pi, pview(r)) <==> semantics_mltl(pi, *f)) by {
                    assert forall|i: nat| *a <= i <= *b implies
                        (#[trigger] shifted(pi, yv, i) <==> semantics_mltl(drop(pi, i), **psi)) by {
                        assert(drop(pi, i).len() >= complen_mltl(**psi));
                    }
                    assert forall|j: nat| *a <= j < *b implies
                        (#[trigger] shifted(pi, xv, j) <==> semantics_mltl(drop(pi, j), **phi)) by {
                        assert(drop(pi, j).len() >= complen_mltl(**phi));
                    }
                    release_sem(pi, xv, yv, **phi, **psi, *a, *b);
                }
            }
            r
        },
    }
}

/// `WEST_num_vars` is at least 1.
pub proof fn WEST_num_vars_pos(f: Mltl<usize>)
    ensures
        WEST_num_vars_spec(f) >= 1,
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => WEST_num_vars_pos(*g),
        Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) => {
            WEST_num_vars_pos(*g);
        },
    }
}

/// `convert_nnf` keeps the interval bounds.
pub proof fn convert_nnf_bound_sum(f: Mltl<usize>)
    ensures
        bound_sum(convert_nnf_spec(f)) == bound_sum(f),
    decreases depth_mltl(f),
{
    reveal_with_fuel(depth_mltl, 2);
    reveal_with_fuel(bound_sum, 3);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => match *g {
            Mltl::True | Mltl::False | Mltl::Prop(_) => {},
            Mltl::Not(phi) => convert_nnf_bound_sum(*phi),
            Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
            | Mltl::Release(phi, _, _, psi) => {
                convert_nnf_bound_sum(Mltl::Not(phi));
                convert_nnf_bound_sum(Mltl::Not(psi));
            },
            Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
                convert_nnf_bound_sum(Mltl::Not(phi));
            },
        },
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
        | Mltl::Release(phi, _, _, psi) => {
            convert_nnf_bound_sum(*phi);
            convert_nnf_bound_sum(*psi);
        },
        Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
            convert_nnf_bound_sum(*phi);
        },
    }
}

/// The satisfying traces of `f`, fast: every returned regex has
/// `complen f` states of `WEST_num_vars f` atoms, and a trace at least
/// `complen f` long satisfies `f` exactly when it matches one of them.
/// (Proved equivalent to `WEST_reg`, not equal: D43.)
pub fn fast_reg(f: &Mltl<usize>) -> (out: Packed)
    requires
        WEST_num_vars_spec(*f) <= usize::MAX,
        fits(WEST_num_vars_spec(*f), bound_sum(*f) + 1),
    ensures
        pwf(out),
        out.n == WEST_num_vars_spec(*f),
        out.len == complen_mltl(*f),
        intervals_welldef(*f) ==> forall|pi: WestTrace| pi.len() >= complen_mltl(*f) ==>
            (#[trigger] west_match(pi, pview(out)) <==> semantics_mltl(pi, *f)),
{
    let n = WEST_num_vars(f);
    let g = convert_nnf(f);
    proof {
        WEST_num_vars_pos(*f);
        let bs = bound_sum(*f);
        assert(bs + 1 <= 2 * n * (bs + 1)) by (nonlinear_arith) requires n >= 1;
        fits_mono(n as nat, 1, bound_sum(*f) + 1);
        convert_nnf_is_nnf(*f);
        convert_nnf_num_vars_complen(*f);
        convert_nnf_bound_sum(*f);
        complen_le_bound_sum(*f);
    }
    if !intervals_welldef_exec(f) {
        // Not covered by the theorem; still return a well-formed answer.
        proof { WEST_num_vars_pos(*f); fits_mono(n as nat, complen_mltl(*f), bound_sum(*f) + 1); }
        let c = complen(f);
        proof { complen_geq_one(*f); }
        let e = p_false(n);
        return p_pad(&e, c);
    }
    proof { convert_nnf_welldef(*f); }
    let r = p_reg(&g, n);
    let c = complen(f);
    proof { fits_mono(n as nat, c as nat, bound_sum(*f) + 1); }
    let padded = if r.len == c { r } else { p_pad(&r, c) };
    proof {
        pview_facts(r);
        if r.len != c {
            assert forall|pi: WestTrace| pi.len() >= c implies
                (#[trigger] west_match(pi, pview(padded)) <==> west_match(pi, pview(r))) by {
                pad_all_match(pi, pview(r), n as nat, r.len as nat, c as nat);
            }
        }
    }
    let out = p_simp(padded);
    proof {
        if intervals_welldef(*f) {
            assert forall|pi: WestTrace| pi.len() >= complen_mltl(*f) implies
                (#[trigger] west_match(pi, pview(out)) <==> semantics_mltl(pi, *f)) by {
                convert_nnf_preserves_semantics(pi, *f);
                assert(west_match(pi, pview(padded)) <==> west_match(pi, pview(r)));
            }
        }
    }
    out
}

/// `intervals_welldef`, executable.
pub fn intervals_welldef_exec(f: &Mltl<usize>) -> (r: bool)
    ensures
        r == intervals_welldef(*f),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => true,
        Mltl::Not(g) => intervals_welldef_exec(g),
        Mltl::And(g, h) | Mltl::Or(g, h) => intervals_welldef_exec(g) && intervals_welldef_exec(h),
        Mltl::Future(a, b, g) | Mltl::Global(a, b, g) => *a <= *b && intervals_welldef_exec(g),
        Mltl::Until(g, a, b, h) | Mltl::Release(g, a, b, h) =>
            *a <= *b && intervals_welldef_exec(g) && intervals_welldef_exec(h),
    }
}

} // verus!
