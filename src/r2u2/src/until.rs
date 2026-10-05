//! Soundness of UNTIL (Isabelle `R2U2_Operators.thy : UNTIL`).
//!
//! Notation: for `φ U[a,b] ψ`, `P` is the first output time the node has not
//! written yet (`next_after` of its history) and `τ` its `next_time`, the
//! first child time it has not read yet. The invariant ([`until_inv`]):
//! - `P + a ≤ τ ≤ P + b`;
//! - at every child time in `[P + a, τ)`, ψ is false and φ is true (the
//!   times UNTIL skipped without deciding anything);
//! - `prev_verdict` is the last verdict written.
//!
//! Every branch of [`until_op`] keeps it, and writes only correct verdicts.
//! A "true" verdict for output `i` is witnessed at `max(i + a, τ)`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use crate::verdict::*;
use crate::scq::*;
use crate::observer::*;
use crate::operators::*;
use crate::soundness::*;

verus! {

pub open spec fn until_f<A>(phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>) -> Mltl<A> {
    Mltl::Until(Box::new(phi), a, b, Box::new(psi))
}

// ---------------------------------------------------------------------------
// UNTIL semantics at absolute positions
// ---------------------------------------------------------------------------

/// A witness `k` for `φ U[a,b] ψ` at position `i`.
pub proof fn lemma_until_true<A>(pi: Seq<Set<A>>, i: nat, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>, k: nat)
    requires
        a <= b,
        i + a <= k <= i + b,
        k < pi.len(),
        semantics_mltl(drop(pi, k), psi),
        forall|m: nat| i + a <= m < k ==> semantics_mltl(#[trigger] drop(pi, m), phi),
    ensures
        semantics_mltl(drop(pi, i), until_f(phi, a, b, psi)),
{
    let d = drop(pi, i);
    let w = (k - i) as nat;
    lemma_drop_len(pi, i);
    lemma_drop_drop(pi, i, w);
    assert forall|j: nat| (j >= a && j < w) implies semantics_mltl(drop(d, j), phi) by {
        lemma_drop_drop(pi, i, j);
        assert(semantics_mltl(drop(pi, i + j), phi));
    }
    assert((a <= w && w <= b) && (semantics_mltl(drop(d, w), psi)
        && forall|j: nat| (j >= a && j < w) ==> semantics_mltl(drop(d, j), phi)));
}

/// `φ U[a,b] ψ` is false at `i` if every ψ-time in the window comes after a
/// φ-failure in the window.
pub proof fn lemma_until_false<A>(pi: Seq<Set<A>>, i: nat, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>)
    requires
        forall|k: nat| i + a <= k <= i + b && semantics_mltl(#[trigger] drop(pi, k), psi) ==>
            exists|m: nat| i + a <= m < k && !semantics_mltl(#[trigger] drop(pi, m), phi),
    ensures
        !semantics_mltl(drop(pi, i), until_f(phi, a, b, psi)),
{
    let d = drop(pi, i);
    if semantics_mltl(d, until_f(phi, a, b, psi)) {
        let w = choose|w: nat| (a <= w && w <= b) && (semantics_mltl(drop(d, w), psi)
            && forall|j: nat| (j >= a && j < w) ==> semantics_mltl(drop(d, j), phi));
        lemma_drop_drop(pi, i, w);
        let k = i + w;
        assert(semantics_mltl(drop(pi, k), psi));
        let m = choose|m: nat| i + a <= m < k && !semantics_mltl(#[trigger] drop(pi, m), phi);
        let j = (m - i) as nat;
        lemma_drop_drop(pi, i, j);
        assert(semantics_mltl(drop(d, j), phi));
    }
}

// ---------------------------------------------------------------------------
// Invariant
// ---------------------------------------------------------------------------

/// The UNTIL node invariant (see the module comment).
pub open spec fn until_inv<A>(q: Scq, obs: Observer, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>, pi: Seq<Set<A>>) -> bool {
    let p = next_after(q.all_values);
    &&& obs.lower_bound == a && obs.upper_bound == b && a <= b
    &&& obs.prev_verdict == (if q.all_values.len() == 0 { None } else { Some(q.all_values.last()) })
    &&& p + a <= q.next_time <= p + b
    &&& forall|m: nat| p + a <= m < q.next_time ==>
            !semantics_mltl(#[trigger] drop(pi, m), psi) && semantics_mltl(drop(pi, m), phi)
}

/// What a read tells about the child's formula: its value on `[next_time, e.time]`.
pub proof fn lemma_read_sem<A>(parent: Scq, child: Scq, f: Mltl<A>, pi: Seq<Set<A>>, bound: nat)
    requires
        hist_inv(child.all_values, f, pi, bound),
        scq_read(parent, child).is_some(),
    ensures
        ({
            let e = scq_read(parent, child).unwrap();
            &&& parent.next_time <= e.time < bound
            &&& forall|j: nat| parent.next_time <= j <= e.time ==> semantics_mltl(#[trigger] drop(pi, j), f) == e.val
        }),
{
    let e = scq_read(parent, child).unwrap();
    lemma_scq_read_sound(parent, child);
    assert forall|j: nat| parent.next_time <= j <= e.time implies semantics_mltl(#[trigger] drop(pi, j), f) == e.val by {
        assert(value_at(child.all_values, j) == Some(e.val));
    }
}

// ---------------------------------------------------------------------------
// The branches of until_op
// ---------------------------------------------------------------------------

/// ψ true on `[τ, t_r]`: write `<true, t_r - a>`.
pub proof fn lemma_until_branch_true<A>(parent: Scq, obs: Observer, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>,
    pi: Seq<Set<A>>, bound: nat, tr: nat)
    requires
        hist_inv(parent.all_values, until_f(phi, a, b, psi), pi, bound),
        until_inv(parent, obs, phi, a, b, psi, pi),
        bound <= pi.len(),
        parent.next_time <= tr < bound,
        forall|j: nat| parent.next_time <= j <= tr ==> semantics_mltl(#[trigger] drop(pi, j), psi),
    ensures
        ({
            let v = Verdict { val: true, time: (tr - a) as nat };
            &&& hist_inv(parent.all_values.push(v), until_f(phi, a, b, psi), pi, bound)
            &&& until_inv(Scq { all_values: parent.all_values.push(v), next_time: tr + 1 },
                    Observer { prev_verdict: Some(v), ..obs }, phi, a, b, psi, pi)
        }),
{
    let p = next_after(parent.all_values);
    let tau = parent.next_time;
    let v = Verdict { val: true, time: (tr - a) as nat };
    assert forall|j: nat| p <= j <= v.time implies v.val == semantics_mltl(#[trigger] drop(pi, j), until_f(phi, a, b, psi)) by {
        let k: nat = if j + a >= tau { (j + a) as nat } else { tau };
        assert(semantics_mltl(drop(pi, k), psi));
        assert forall|m: nat| j + a <= m < k implies semantics_mltl(#[trigger] drop(pi, m), phi) by {
            assert(p + a <= m < tau);
        }
        lemma_until_true(pi, j, phi, a, b, psi, k);
    }
    lemma_hist_push(parent.all_values, v, until_f(phi, a, b, psi), pi, bound);
}

/// ψ false on `[τ, t_r]`, φ false on `[τ, t_l]`: write `<false, t_min - a>`.
pub proof fn lemma_until_branch_left_false<A>(parent: Scq, obs: Observer, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>,
    pi: Seq<Set<A>>, bound: nat, tl: nat, tr: nat)
    requires
        hist_inv(parent.all_values, until_f(phi, a, b, psi), pi, bound),
        until_inv(parent, obs, phi, a, b, psi, pi),
        parent.next_time <= tr < bound,
        parent.next_time <= tl < bound,
        forall|j: nat| parent.next_time <= j <= tr ==> !semantics_mltl(#[trigger] drop(pi, j), psi),
        forall|j: nat| parent.next_time <= j <= tl ==> !semantics_mltl(#[trigger] drop(pi, j), phi),
    ensures
        ({
            let t_min = min_nat(tl, tr);
            let v = Verdict { val: false, time: (t_min - a) as nat };
            &&& hist_inv(parent.all_values.push(v), until_f(phi, a, b, psi), pi, bound)
            &&& until_inv(Scq { all_values: parent.all_values.push(v), next_time: t_min + 1 },
                    Observer { prev_verdict: Some(v), ..obs }, phi, a, b, psi, pi)
        }),
{
    let p = next_after(parent.all_values);
    let tau = parent.next_time;
    let t_min = min_nat(tl, tr);
    let v = Verdict { val: false, time: (t_min - a) as nat };
    assert forall|j: nat| p <= j <= v.time implies v.val == semantics_mltl(#[trigger] drop(pi, j), until_f(phi, a, b, psi)) by {
        let m: nat = if j + a >= tau { (j + a) as nat } else { tau };
        assert(!semantics_mltl(drop(pi, m), phi));
        assert forall|k: nat| j + a <= k <= j + b && semantics_mltl(#[trigger] drop(pi, k), psi) implies
            exists|m2: nat| j + a <= m2 < k && !semantics_mltl(#[trigger] drop(pi, m2), phi) by {
            if k < tau {
                assert(p + a <= k);
            }
            assert(m < k);
        }
        lemma_until_false(pi, j, phi, a, b, psi);
    }
    lemma_hist_push(parent.all_values, v, until_f(phi, a, b, psi), pi, bound);
}

/// ψ false on `[τ, t_r]` and `t_r ≥ P + b`: write `<false, t_r - b>`, and
/// read on from `max(x, t_r - b + a + 1)`, where everything in `[τ, x)` has
/// ψ false and φ true.
pub proof fn lemma_until_branch_elapsed<A>(parent: Scq, obs: Observer, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>,
    pi: Seq<Set<A>>, bound: nat, tr: nat, x: nat)
    requires
        hist_inv(parent.all_values, until_f(phi, a, b, psi), pi, bound),
        until_inv(parent, obs, phi, a, b, psi, pi),
        parent.next_time <= tr < bound,
        tr >= next_after(parent.all_values) + b,
        forall|j: nat| parent.next_time <= j <= tr ==> !semantics_mltl(#[trigger] drop(pi, j), psi),
        parent.next_time <= x <= tr + 1,
        forall|j: nat| parent.next_time <= j < x ==> #[trigger] semantics_mltl(drop(pi, j), phi),
    ensures
        ({
            let v = Verdict { val: false, time: (tr - b) as nat };
            &&& hist_inv(parent.all_values.push(v), until_f(phi, a, b, psi), pi, bound)
            &&& until_inv(Scq { all_values: parent.all_values.push(v), next_time: max_nat(x, (v.time + a + 1) as nat) },
                    Observer { prev_verdict: Some(v), ..obs }, phi, a, b, psi, pi)
        }),
{
    let p = next_after(parent.all_values);
    let tau = parent.next_time;
    let v = Verdict { val: false, time: (tr - b) as nat };
    assert forall|j: nat| p <= j <= v.time implies v.val == semantics_mltl(#[trigger] drop(pi, j), until_f(phi, a, b, psi)) by {
        assert forall|k: nat| j + a <= k <= j + b && semantics_mltl(#[trigger] drop(pi, k), psi) implies
            exists|m2: nat| j + a <= m2 < k && !semantics_mltl(#[trigger] drop(pi, m2), phi) by {
            if k < tau {
                assert(p + a <= k);
            }
        }
        lemma_until_false(pi, j, phi, a, b, psi);
    }
    lemma_hist_push(parent.all_values, v, until_f(phi, a, b, psi), pi, bound);
    let q2 = Scq { all_values: parent.all_values.push(v), next_time: max_nat(x, (v.time + a + 1) as nat) };
    let p2 = next_after(q2.all_values);
    assert forall|m: nat| p2 + a <= m < q2.next_time implies
        !semantics_mltl(#[trigger] drop(pi, m), psi) && semantics_mltl(drop(pi, m), phi) by {
        if m < tau {
            assert(p + a <= m);
        }
    }
}

/// ψ false on `[τ, t_r]`, φ true on `[τ, t_l]`, window not passed: skip to `t_min + 1`.
pub proof fn lemma_until_branch_wait<A>(parent: Scq, obs: Observer, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>,
    pi: Seq<Set<A>>, tl: nat, tr: nat)
    requires
        until_inv(parent, obs, phi, a, b, psi, pi),
        parent.next_time <= tr,
        parent.next_time <= tl,
        tr < next_after(parent.all_values) + b,
        forall|j: nat| parent.next_time <= j <= tr ==> !semantics_mltl(#[trigger] drop(pi, j), psi),
        forall|j: nat| parent.next_time <= j <= tl ==> #[trigger] semantics_mltl(drop(pi, j), phi),
    ensures
        until_inv(Scq { all_values: parent.all_values, next_time: min_nat(tl, tr) + 1 }, obs, phi, a, b, psi, pi),
{
    let p = next_after(parent.all_values);
    let tau = parent.next_time;
    let q2 = Scq { all_values: parent.all_values, next_time: min_nat(tl, tr) + 1 };
    assert forall|m: nat| p + a <= m < q2.next_time implies
        !semantics_mltl(#[trigger] drop(pi, m), psi) && semantics_mltl(drop(pi, m), phi) by {
        if m < tau {
            assert(p + a <= m < tau);
        }
    }
}

// ---------------------------------------------------------------------------
// The step
// ---------------------------------------------------------------------------

/// `UNTIL` keeps the parent's history sound for `φ U[a,b] ψ` and keeps
/// [`until_inv`], if the children's histories are sound for `φ` and `ψ`.
pub proof fn lemma_until_step<A>(parent: Scq, left: Scq, right: Scq, obs: Observer, phi: Mltl<A>, a: usize, b: usize,
    psi: Mltl<A>, pi: Seq<Set<A>>, bound: nat, progress: LoopProgress)
    requires
        hist_inv(parent.all_values, until_f(phi, a, b, psi), pi, bound),
        until_inv(parent, obs, phi, a, b, psi, pi),
        hist_inv(left.all_values, phi, pi, bound),
        hist_inv(right.all_values, psi, pi, bound),
        bound <= pi.len(),
    ensures
        ({
            let (q, o, p) = until_op(parent, left, right, obs, progress);
            &&& hist_inv(q.all_values, until_f(phi, a, b, psi), pi, bound)
            &&& until_inv(q, o, phi, a, b, psi, pi)
        }),
{
    let p = next_after(parent.all_values);
    let elapsed_from = match obs.prev_verdict {
        None => obs.upper_bound,
        Some(prev) => prev.time + obs.upper_bound + 1,
    };
    assert(elapsed_from == p + b);
    match scq_read(parent, right) {
        None => {},
        Some(r) => {
            lemma_read_sem(parent, right, psi, pi, bound);
            if r.val {
                lemma_until_branch_true(parent, obs, phi, a, b, psi, pi, bound, r.time);
            } else {
                match scq_read(parent, left) {
                    Some(l) => {
                        lemma_read_sem(parent, left, phi, pi, bound);
                        let t_min = min_nat(l.time, r.time);
                        if !l.val {
                            lemma_until_branch_left_false(parent, obs, phi, a, b, psi, pi, bound, l.time, r.time);
                        } else if r.time >= elapsed_from {
                            lemma_until_branch_elapsed(parent, obs, phi, a, b, psi, pi, bound, r.time, t_min + 1);
                        } else {
                            lemma_until_branch_wait(parent, obs, phi, a, b, psi, pi, l.time, r.time);
                        }
                    },
                    None => {
                        if r.time >= elapsed_from {
                            lemma_until_branch_elapsed(parent, obs, phi, a, b, psi, pi, bound, r.time, parent.next_time);
                        }
                    },
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Progress (used by promptness.rs)
// ---------------------------------------------------------------------------

/// What one operator call may do to its node's queue in a reloop pass
/// (`b` = steps read): written-up-to and `next_time` never go down and stay
/// within `b` when they move; no progress means nothing was written;
/// progress means something was.
pub open spec fn scq_step_ok(old: Scq, new: Scq, p: LoopProgress, b: nat) -> bool {
    &&& next_after(new.all_values) >= next_after(old.all_values)
    &&& next_after(new.all_values) <= b
    &&& new.next_time >= old.next_time
    &&& new.next_time > old.next_time ==> new.next_time <= b
    &&& p == LoopProgress::ReloopNoProgress ==> new.all_values == old.all_values
    &&& p != LoopProgress::ReloopNoProgress ==> next_after(new.all_values) > next_after(old.all_values)
}

/// UNTIL never moves `next_time` back.
pub proof fn lemma_until_next_time_mono(parent: Scq, left: Scq, right: Scq, obs: Observer, progress: LoopProgress)
    ensures
        until_op(parent, left, right, obs, progress).0.next_time >= parent.next_time,
{
    if scq_read(parent, right).is_some() {
        lemma_first_from_props(scq_entries(right), parent.next_time);
    }
    if scq_read(parent, left).is_some() {
        lemma_first_from_props(scq_entries(left), parent.next_time);
    }
}

pub proof fn lemma_until_progress<A>(parent: Scq, left: Scq, right: Scq, obs: Observer, phi: Mltl<A>, a: usize, b: usize,
    psi: Mltl<A>, pi: Seq<Set<A>>, bound: nat)
    requires
        hist_inv(parent.all_values, until_f(phi, a, b, psi), pi, bound),
        until_inv(parent, obs, phi, a, b, psi, pi),
        hist_inv(left.all_values, phi, pi, bound),
        hist_inv(right.all_values, psi, pi, bound),
        bound <= pi.len(),
    ensures
        ({
            let (q, o, p) = until_op(parent, left, right, obs, LoopProgress::ReloopNoProgress);
            scq_step_ok(parent, q, p, bound)
        }),
{
    lemma_propagate_progress_1(LoopProgress::ReloopNoProgress);
    lemma_until_step(parent, left, right, obs, phi, a, b, psi, pi, bound, LoopProgress::ReloopNoProgress);
    lemma_until_next_time_mono(parent, left, right, obs, LoopProgress::ReloopNoProgress);
    if scq_read(parent, right).is_some() {
        lemma_read_sem(parent, right, psi, pi, bound);
    }
    if scq_read(parent, left).is_some() {
        lemma_read_sem(parent, left, phi, pi, bound);
    }
}

/// In a reloop call that reports no progress, if both children have data
/// at `next_time`, UNTIL skipped ahead: `next_time` went up.
pub proof fn lemma_until_last(parent: Scq, left: Scq, right: Scq, obs: Observer)
    requires
        strictly_increasing(left.all_values),
        strictly_increasing(right.all_values),
        until_op(parent, left, right, obs, LoopProgress::ReloopNoProgress).2 == LoopProgress::ReloopNoProgress,
        parent.next_time < next_after(left.all_values),
        parent.next_time < next_after(right.all_values),
    ensures
        until_op(parent, left, right, obs, LoopProgress::ReloopNoProgress).0.next_time >= parent.next_time + 1,
{
    lemma_propagate_progress_1(LoopProgress::ReloopNoProgress);
    lemma_scq_read_some(parent, left);
    lemma_scq_read_some(parent, right);
    lemma_first_from_props(scq_entries(right), parent.next_time);
    lemma_first_from_props(scq_entries(left), parent.next_time);
}

} // verus!
