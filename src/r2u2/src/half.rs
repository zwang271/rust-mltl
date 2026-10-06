//! Half-size queues: why a slower child needs only half of the extra room.
//!
//! For a child `c` of a binary node, with `x = wpd(operands) − bpd(c)` and
//! `y = wpd(sibling) − bpd(c)` (both cut at 0), the ring of `c` gets
//! `⌈(x + y)/2⌉ + 1` slots ([`half_slack`]). When `c` is not the slower child
//! `x = y` and this is the time bound of `ring_sim.rs`. When it is (`x > y`),
//! the bound comes from a potential ([`psi`]) of the reader's backlog:
//!
//! - the reader's current entry counts the steps left in it, every later
//!   entry counts its length but at least 2, and the child's headroom up to
//!   its coverage bound `cap` counts 1 per step;
//! - a write of the child adds at most 1, and only when the reader already
//!   has data ([`lemma_psi_write`]); a new time step adds at most 1
//!   ([`lemma_psi_cap`]); every move of the reader takes at least 1 off
//!   ([`lemma_psi_move`]);
//! - so before every pass the potential is at most `x + y` (one more when the
//!   reader needs nothing stored), and every later entry costing 2 bounds the
//!   backlog by `⌈(x + y)/2⌉` ([`lemma_room_half`]).
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use crate::verdict::*;
use crate::scq::*;
use crate::operators::*;
use crate::engine::*;
use crate::soundness::*;
use crate::until::*;
use crate::promptness::*;
use crate::queue_size::*;
use crate::ring_engine::*;
use crate::ring_sim::*;
use crate::tight::*;

verus! {

// ---------------------------------------------------------------------------
// The potential
// ---------------------------------------------------------------------------

/// Weight of entry `j ≥ 1` when it comes after the reader's current entry:
/// its length, but at least 2.
pub open spec fn gapw(c: Seq<Verdict>, j: int) -> int {
    let g = c[j].time - c[j - 1].time;
    if g >= 2 { g } else { 2 }
}

/// Sum of `gapw` over the entries from index `i ≥ 1` to the end.
pub open spec fn tail_w(c: Seq<Verdict>, i: int) -> int
    decreases c.len(),
{
    if c.len() as int <= i || i < 1 { 0 } else { tail_w(c.drop_last(), i) + gapw(c, c.len() - 1) }
}

/// Weight of the stored entries a reader at `tau` still needs: the steps
/// left in its current entry, plus `tail_w` of the later ones.
pub open spec fn wsum(c: Seq<Verdict>, tau: nat) -> int {
    let k = first_idx(c, tau);
    if k < c.len() { (c[k as int].time + 1 - tau) + tail_w(c, k as int + 1) } else { 0 }
}

/// The potential: `wsum` plus the child's headroom up to `cap` beyond what
/// it covered and where the reader is.
pub open spec fn psi(c: Seq<Verdict>, tau: nat, cap: nat) -> int {
    wsum(c, tau) + nat_sub(cap, max_nat(next_after(c), tau)) as int
}

/// Entries at or after `tau`: what a reader at `tau` still needs.
pub open spec fn ent(c: Seq<Verdict>, tau: nat) -> int {
    c.len() - first_idx(c, tau)
}

/// The ring slack for child `c` with `x`, `y` as in the module comment.
pub open spec fn half_slack(x: nat, y: nat) -> nat {
    (x + y + 1) / 2
}

/// A pointer at the first needed entry leaves room for one more write.
pub open spec fn room(c: Seq<Verdict>, tau: nat, w: nat, cap: nat) -> bool {
    ent(c, tau) <= w || (ent(c, tau) == w + 1 && next_after(c) >= cap)
}

// ---------------------------------------------------------------------------
// tail_w
// ---------------------------------------------------------------------------

pub proof fn lemma_tail_w_split(c: Seq<Verdict>, i: int)
    requires
        1 <= i < c.len(),
    ensures
        tail_w(c, i) == gapw(c, i) + tail_w(c, i + 1),
    decreases c.len(),
{
    let d = c.drop_last();
    if i < c.len() - 1 {
        lemma_tail_w_split(d, i);
        assert(gapw(d, i) == gapw(c, i));
        assert(tail_w(c, i + 1) == tail_w(d, i + 1) + gapw(c, c.len() - 1));
    } else {
        assert(tail_w(d, i) == 0);
        assert(tail_w(c, i + 1) == 0);
    }
}

/// Every later entry weighs at least 2, and at most its length plus 1.
pub proof fn lemma_tail_w_bounds(c: Seq<Verdict>, i: int)
    requires
        strictly_increasing(c),
        1 <= i <= c.len(),
    ensures
        tail_w(c, i) >= 2 * (c.len() - i),
        i < c.len() ==> tail_w(c, i) <= c[c.len() - 1].time - c[i - 1].time + (c.len() - i),
        i < c.len() ==> tail_w(c, i) >= c[c.len() - 1].time - c[i - 1].time,
    decreases c.len() - i,
{
    if i < c.len() {
        lemma_tail_w_split(c, i);
        assert(c[i - 1].time < c[i].time);
        lemma_tail_w_bounds(c, i + 1);
        if i + 1 < c.len() {
            assert(c[i].time < c[c.len() - 1].time);
        }
    } else {
        assert(tail_w(c, i) == 0);
    }
}

/// `tail_w` gets smaller from later indices.
pub proof fn lemma_tail_w_mono(c: Seq<Verdict>, i: int, i2: int)
    requires
        strictly_increasing(c),
        1 <= i <= i2 <= c.len(),
    ensures
        tail_w(c, i) >= tail_w(c, i2),
    decreases i2 - i,
{
    if i < i2 {
        lemma_tail_w_split(c, i);
        lemma_tail_w_mono(c, i + 1, i2);
    }
}

pub proof fn lemma_tail_w_push(c: Seq<Verdict>, v: Verdict, i: int)
    requires
        1 <= i <= c.len(),
    ensures
        tail_w(c.push(v), i) == tail_w(c, i) + gapw(c.push(v), c.len() as int),
{
    assert(c.push(v).drop_last() =~= c);
}

pub proof fn lemma_tail_w_update_last(c: Seq<Verdict>, v: Verdict, i: int)
    requires
        1 <= i < c.len(),
    ensures
        tail_w(c.update(c.len() - 1, v), i) - gapw(c.update(c.len() - 1, v), c.len() - 1)
            == tail_w(c, i) - gapw(c, c.len() - 1),
{
    let c2 = c.update(c.len() - 1, v);
    assert(c2.drop_last() =~= c.drop_last());
}

// ---------------------------------------------------------------------------
// Bounds on the potential
// ---------------------------------------------------------------------------

/// With data, the backlog costs `2·ent − 1` and the potential is at most
/// `2·(cap − tau) − 1`; without, the potential is the headroom past `tau`.
pub proof fn lemma_psi_bounds(c: Seq<Verdict>, tau: nat, cap: nat)
    requires
        strictly_increasing(c),
        next_after(c) <= cap,
    ensures
        0 <= first_idx(c, tau) <= c.len(),
        ent(c, tau) > 0 ==> psi(c, tau, cap) >= 2 * ent(c, tau) - 1 + nat_sub(cap, next_after(c)),
        ent(c, tau) > 0 ==> psi(c, tau, cap) <= 2 * nat_sub(cap, tau) - 1,
        ent(c, tau) > 0 ==> next_after(c) > tau,
        ent(c, tau) <= 0 ==> next_after(c) <= tau && psi(c, tau, cap) == nat_sub(cap, tau),
        psi(c, tau, cap) >= 0,
{
    lemma_first_idx(c, tau);
    let k = first_idx(c, tau);
    if k < c.len() {
        let l = c.len() - 1;
        if k < l {
            assert(c[k as int].time < c[l].time);
        }
        lemma_tail_w_bounds(c, k as int + 1);
        if k + 1 < c.len() {
            lemma_time_gap(c, k as int + 1, l);
        }
    } else if c.len() > 0 {
        assert(c[c.len() - 1].time < tau);
    }
}

/// A new time step raises the potential by at most 1.
pub proof fn lemma_psi_cap(c: Seq<Verdict>, tau: nat, cap: nat)
    ensures
        psi(c, tau, cap + 1) <= psi(c, tau, cap) + 1,
{
}

/// A move of the reader lowers the potential by at least 1 (or it is 0).
pub proof fn lemma_psi_move(c: Seq<Verdict>, tau: nat, tau2: nat, cap: nat)
    requires
        strictly_increasing(c),
        next_after(c) <= cap,
        tau <= tau2,
    ensures
        psi(c, tau2, cap) <= psi(c, tau, cap),
        tau < tau2 ==> psi(c, tau2, cap) < psi(c, tau, cap) || psi(c, tau2, cap) == 0,
{
    lemma_first_idx(c, tau);
    lemma_first_idx(c, tau2);
    lemma_first_idx_mono(c, tau, tau2);
    lemma_psi_bounds(c, tau, cap);
    lemma_psi_bounds(c, tau2, cap);
    let k = first_idx(c, tau);
    let k2 = first_idx(c, tau2);
    if k < c.len() {
        let l = c.len() - 1;
        if k < l {
            assert(c[k as int].time < c[l].time);
        }
        if k2 >= c.len() {
            // the reader leaves the stored entries: wsum was at least what it skips
            lemma_tail_w_bounds(c, k as int + 1);
        } else if k < k2 {
            lemma_tail_w_mono(c, k as int + 1, k2 as int);
            lemma_tail_w_split(c, k2 as int);
            assert(c[k2 - 1].time < tau2);
        }
    }
}

/// A child write (at most one, after what it covered, within `cap`) raises
/// the potential by at most 1, and only if the reader had data.
pub proof fn lemma_psi_write(h: Seq<Verdict>, h2: Seq<Verdict>, tau: nat, cap: nat)
    requires
        strictly_increasing(h2),
        h2 == h || h2 == h.push(h2.last()),
        next_after(h2) <= cap,
    ensures
        psi(compact(h2), tau, cap) <= psi(compact(h), tau, cap) + (if ent(compact(h), tau) > 0 { 1int } else { 0 }),
{
    if h2 != h {
        let v = h2.last();
        assert(h2.drop_last() =~= h);
        assert(strictly_increasing(h)) by {
            assert forall|i: int, k: int| #![trigger h[i], h[k]] 0 <= i < k < h.len() implies h[i].time < h[k].time by {
                assert(h[i] == h2[i] && h[k] == h2[k]);
            }
        }
        lemma_compact(h);
        lemma_compact(h2);
        if h.len() > 0 {
            assert(h.last() == h2[h2.len() - 2]);
            assert(h2[h2.len() - 2].time < h2.last().time);
        }
        let c = compact(h);
        let c2 = compact(h2);
        assert(v.time >= next_after(c));
        lemma_first_idx(c, tau);
        let k = first_idx(c, tau);
        if k < c.len() && k + 1 < c.len() {
            assert(c[k as int].time < c[c.len() - 1].time);
        }
        if k >= c.len() && c.len() > 0 {
            assert(c[c.len() - 1].time < tau);
        }
        if c.len() > 0 && c.last().val == v.val {
            assert(c2 == c.update(c.len() - 1, v));
            lemma_first_idx_update_last(c, v, tau);
            let l = c.len() - 1;
            if k < l {
                lemma_tail_w_update_last(c, v, k as int + 1);
                assert(c2[k as int] == c[k as int]);
                lemma_tail_w_split(c, l);
                lemma_tail_w_split(c2, l);
                assert(tail_w(c, l + 1) == 0 && tail_w(c2, l + 1) == 0);
            } else if k == l {
                assert(tail_w(c2, l + 1) == 0 && tail_w(c, l + 1) == 0);
            } else if v.time >= tau {
                assert(tail_w(c2, l + 1) == 0);
            }
        } else {
            assert(c2 == c.push(v));
            lemma_first_idx_push(c, v, tau);
            if k < c.len() {
                lemma_tail_w_push(c, v, k as int + 1);
                assert(c2[k as int] == c[k as int]);
            } else if v.time >= tau {
                assert(tail_w(c2, c.len() as int + 1) == 0);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// From the potential to room in the ring
// ---------------------------------------------------------------------------

/// At a read: potential at most `x + y + 1` leaves room in `half_slack + 1` slots.
pub proof fn lemma_room_half(c: Seq<Verdict>, tau: nat, cap: nat, x: nat, y: nat)
    requires
        strictly_increasing(c),
        next_after(c) <= cap,
        psi(c, tau, cap) <= x + y + 1,
    ensures
        room(c, tau, half_slack(x, y), cap),
{
    lemma_psi_bounds(c, tau, cap);
}

/// In the last pass of a step: potential at most `x + y` (when the reader
/// has data) leaves room for the next step too.
pub proof fn lemma_room_half_last(c: Seq<Verdict>, tau: nat, cap: nat, x: nat, y: nat)
    requires
        strictly_increasing(c),
        next_after(c) <= cap,
        psi(c, tau, cap) <= x + y + (if ent(c, tau) > 0 { 0int } else { 1 }),
    ensures
        ent(c, tau) <= half_slack(x, y),
        room(c, tau, half_slack(x, y), cap + 1),
{
    lemma_psi_bounds(c, tau, cap);
}

/// A larger bound `cap` only adds headroom.
pub proof fn lemma_psi_cap_mono(c: Seq<Verdict>, tau: nat, cap: nat, cap2: nat)
    requires
        cap <= cap2,
    ensures
        psi(c, tau, cap) <= psi(c, tau, cap2),
{
}

// ---------------------------------------------------------------------------
// One edge in one pass
// ---------------------------------------------------------------------------

/// A history that gained at most one later entry covers at least as much.
pub proof fn lemma_next_after_grow(h: Seq<Verdict>, h2: Seq<Verdict>)
    requires
        strictly_increasing(h2),
        h2 == h || h2 == h.push(h2.last()),
    ensures
        next_after(h2) >= next_after(h),
{
    if h2 != h && h.len() > 0 {
        assert(h2[h.len() - 1] == h.last());
        assert(h2[h.len() - 1].time < h2[h2.len() - 1].time);
    }
}

/// A pass at one edge: the child wrote at most once; then the reader moved,
/// or had no data from the child, or none from the sibling (which covers at
/// least `s_lo`, at most `y + 1` behind the child's bound `cap`). The
/// potential is at most `x + y + 1` at the read and the invariant holds after.
pub proof fn lemma_edge_pass(hc: Seq<Verdict>, hc2: Seq<Verdict>, hs2: Seq<Verdict>, tau: nat, tau2: nat,
    x: nat, y: nat, cap: nat, s_lo: nat)
    requires
        strictly_increasing(hc2),
        hc2 == hc || hc2 == hc.push(hc2.last()),
        next_after(hc2) <= cap,
        tau <= tau2,
        tau2 == tau ==> (ent(compact(hc2), tau) <= 0 || tau >= next_after(hs2)),
        next_after(hs2) >= s_lo,
        nat_sub(cap, s_lo) <= y + 1,
        x > y,
        psi(compact(hc), tau, cap) <= x + y + (if ent(compact(hc), tau) > 0 { 0int } else { 1 }),
    ensures
        psi(compact(hc2), tau, cap) <= x + y + 1,
        psi(compact(hc2), tau2, cap) <= x + y + (if ent(compact(hc2), tau2) > 0 { 0int } else { 1 }),
{
    lemma_psi_write(hc, hc2, tau, cap);
    lemma_compact(hc2);
    let c2 = compact(hc2);
    lemma_psi_move(c2, tau, tau2, cap);
    lemma_psi_bounds(c2, tau, cap);
    lemma_psi_bounds(c2, tau2, cap);
}

/// The last pass of a step at one edge: nothing was written; the reader is at
/// least `r_lo` (at most `x` behind `cap`) and the sibling covers at least
/// `s_lo` (at most `y` behind). The invariant then holds for the next step.
pub proof fn lemma_edge_last(hc: Seq<Verdict>, hs: Seq<Verdict>, tau: nat, tau2: nat,
    x: nat, y: nat, cap: nat, cap2: nat, s_lo: nat, r_lo: nat)
    requires
        strictly_increasing(hc),
        next_after(hc) <= cap,
        cap2 <= cap + 1,
        tau <= tau2,
        tau2 == tau ==> (ent(compact(hc), tau) <= 0 || tau >= next_after(hs)),
        next_after(hs) >= s_lo,
        nat_sub(cap, s_lo) <= y,
        tau >= r_lo,
        nat_sub(cap, r_lo) <= x,
        x > y,
        psi(compact(hc), tau, cap) <= x + y + (if ent(compact(hc), tau) > 0 { 0int } else { 1 }),
    ensures
        psi(compact(hc), tau2, cap2) <= x + y + (if ent(compact(hc), tau2) > 0 { 0int } else { 1 }),
{
    lemma_compact(hc);
    let c = compact(hc);
    lemma_psi_move(c, tau, tau2, cap);
    lemma_psi_bounds(c, tau, cap);
    lemma_psi_bounds(c, tau2, cap);
    lemma_psi_cap(c, tau2, cap);
    lemma_psi_cap_mono(c, tau2, cap2, cap + 1);
    lemma_first_idx_mono(c, tau, tau2);
}

// ---------------------------------------------------------------------------
// The invariant over the tree
// ---------------------------------------------------------------------------

/// The potential bound for child history `h` (formula `fc`, sibling `fs`,
/// operands' `wpd` `w`) read at `tau`, after `b` steps (`cap = b − bpd`).
pub open spec fn edge_ok<A>(h: Seq<Verdict>, fc: Mltl<A>, fs: Mltl<A>, w: nat, tau: nat, b: nat) -> bool {
    let x = child_slack(w, fc);
    let y = sib_slack(fc, fs);
    x > y ==> psi(compact(h), tau, nat_sub(b, bpd(fc))) <= x + y + (if ent(compact(h), tau) > 0 { 0int } else { 1 })
}

/// `edge_ok` at every child of every binary node.
pub open spec fn half_inv<A>(t: Tree<A>, b: nat) -> bool
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => half_inv(*c, b),
        MltlParseTree::And(d, l, r) | MltlParseTree::Until(d, l, _, _, r) => {
            let w = operands_wpd(*l, *r);
            let (fl, fr) = (mltl_parse_tree_to_mltl_spec(*l), mltl_parse_tree_to_mltl_spec(*r));
            &&& edge_ok(get_execution_sequence(*l), fl, fr, w, d.scq.next_time, b)
            &&& edge_ok(get_execution_sequence(*r), fr, fl, w, d.scq.next_time, b)
            &&& half_inv(*l, b) && half_inv(*r, b)
        },
        _ => true,
    }
}

/// With data on both sides AND writes, so moves `next_time`.
pub proof fn lemma_and_moves(parent: Scq, left: Scq, right: Scq, progress: LoopProgress)
    ensures
        and_op(parent, left, right, progress).0.next_time >= parent.next_time,
        scq_read(parent, left).is_some() && scq_read(parent, right).is_some()
            ==> and_op(parent, left, right, progress).0.next_time > parent.next_time,
{
    if scq_read(parent, left).is_some() {
        lemma_first_from_props(scq_entries(left), parent.next_time);
    }
    if scq_read(parent, right).is_some() {
        lemma_first_from_props(scq_entries(right), parent.next_time);
    }
}

/// The reader stayed put: it lacked data from `c` or from `s`.
pub proof fn lemma_stay(parent: Scq, cq: Scq, sq: Scq, tau2: nat)
    requires
        strictly_increasing(sq.all_values),
        scq_read(parent, cq).is_some() && scq_read(parent, sq).is_some() ==> tau2 > parent.next_time,
    ensures
        tau2 == parent.next_time ==> (ent(compact(cq.all_values), parent.next_time) <= 0
            || parent.next_time >= next_after(sq.all_values)),
{
    lemma_scq_read_some(parent, sq);
    lemma_first_idx(compact(cq.all_values), parent.next_time);
}

/// The arithmetic of the bounds: the child's `cap` against the sibling's and
/// the reader's guaranteed progress.
pub proof fn lemma_edge_arith<A>(fc: Mltl<A>, fs: Mltl<A>, w: nat, k: nat)
    requires
        w >= wpd(fs),
    ensures
        nat_sub(nat_sub(k + 1, bpd(fc)), nat_sub(k, wpd(fs))) <= sib_slack(fc, fs) + 1,
        nat_sub(nat_sub(k, bpd(fc)), nat_sub(k, wpd(fs))) <= sib_slack(fc, fs),
        nat_sub(nat_sub(k, bpd(fc)), nat_sub(k, w)) <= child_slack(w, fc),
        nat_sub(k + 1, bpd(fc)) <= nat_sub(k, bpd(fc)) + 1,
{
}

/// Shape facts of a child after its update in the pass.
pub proof fn lemma_child_pass<A>(c: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        cov_pre(c, pi, n, progress),
        tree_prompt(c, n),
    ensures
        ({
            let c2 = mltl_update(c, pi[n as int], n, progress).0;
            let h = get_execution_sequence(c);
            let h2 = get_execution_sequence(c2);
            &&& mltl_parse_tree_to_mltl_spec(c2) == mltl_parse_tree_to_mltl_spec(c)
            &&& strictly_increasing(h2)
            &&& h2 == h || h2 == h.push(h2.last())
            &&& next_after(h2) <= nat_sub(n + 1, bpd(mltl_parse_tree_to_mltl_spec(c)))
            &&& next_after(h2) >= nat_sub(n, wpd(mltl_parse_tree_to_mltl_spec(c)))
            &&& tree_inv(c2, pi, n + 1)
        }),
{
    let s = pi[n as int];
    lemma_update_shape(c, s, n, progress);
    child_updated_inv(c, pi, n, progress);
    lemma_update_root(c, s, n, progress);
    lemma_update_cov_ub(c, pi, n, progress);
    let h = get_execution_sequence(c);
    let h2 = get_execution_sequence(mltl_update(c, s, n, progress).0);
    lemma_next_after_grow(h, h2);
}

/// Passes keep `half_inv` (at `n + 1` steps read).
pub proof fn lemma_update_half<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        cov_pre(t, pi, n, progress),
        tree_prompt(t, n),
        half_inv(t, n + 1),
    ensures
        half_inv(mltl_update(t, pi[n as int], n, progress).0, n + 1),
    decreases t,
{
    let s = pi[n as int];
    match t {
        MltlParseTree::Not(_, c) => lemma_update_half(*c, pi, n, progress),
        MltlParseTree::And(d, l, r) => {
            lemma_update_half(*l, pi, n, progress);
            lemma_update_half(*r, pi, n, progress);
            lemma_update_half_and(t, pi, n, progress);
        },
        MltlParseTree::Until(d, l, _, _, r) => {
            lemma_update_half(*l, pi, n, progress);
            lemma_update_half(*r, pi, n, progress);
            lemma_update_half_until(t, pi, n, progress);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_update_half_and<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        t is And,
        cov_pre(t, pi, n, progress),
        tree_prompt(t, n),
        half_inv(t, n + 1),
        half_inv(mltl_update(*t->And_1, pi[n as int], n, progress).0, n + 1),
        half_inv(mltl_update(*t->And_2, pi[n as int], n, progress).0, n + 1),
    ensures
        half_inv(mltl_update(t, pi[n as int], n, progress).0, n + 1),
{
    let s = pi[n as int];
    let d = t->And_0;
    let (l, r) = (*t->And_1, *t->And_2);
    let (fl, fr) = (mltl_parse_tree_to_mltl_spec(l), mltl_parse_tree_to_mltl_spec(r));
    let w = operands_wpd(l, r);
    lemma_child_pass(l, pi, n, progress);
    lemma_child_pass(r, pi, n, progress);
    let (l2, r2) = (mltl_update(l, s, n, progress).0, mltl_update(r, s, n, progress).0);
    let (lq, rq) = (get_scq_from_tree(l2), get_scq_from_tree(r2));
    let q = and_op(d.scq, lq, rq, progress).0;
    let tau = d.scq.next_time;
    lemma_and_moves(d.scq, lq, rq, progress);
    lemma_stay(d.scq, lq, rq, q.next_time);
    lemma_stay(d.scq, rq, lq, q.next_time);
    lemma_edge_arith(fl, fr, w, n);
    lemma_edge_arith(fr, fl, w, n);
    let (hl, hr) = (get_execution_sequence(l), get_execution_sequence(r));
    let (hl2, hr2) = (get_execution_sequence(l2), get_execution_sequence(r2));
    if child_slack(w, fl) > sib_slack(fl, fr) {
        lemma_edge_pass(hl, hl2, hr2, tau, q.next_time, child_slack(w, fl), sib_slack(fl, fr),
            nat_sub(n + 1, bpd(fl)), nat_sub(n, wpd(fr)));
    }
    if child_slack(w, fr) > sib_slack(fr, fl) {
        lemma_edge_pass(hr, hr2, hl2, tau, q.next_time, child_slack(w, fr), sib_slack(fr, fl),
            nat_sub(n + 1, bpd(fr)), nat_sub(n, wpd(fl)));
    }
    let t2 = mltl_update(t, s, n, progress).0;
    assert(t2 == MltlParseTree::And(with_scq(d, q), Box::new(l2), Box::new(r2)));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_update_half_until<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        t is Until,
        cov_pre(t, pi, n, progress),
        tree_prompt(t, n),
        half_inv(t, n + 1),
        half_inv(mltl_update(*t->Until_1, pi[n as int], n, progress).0, n + 1),
        half_inv(mltl_update(*t->Until_4, pi[n as int], n, progress).0, n + 1),
    ensures
        half_inv(mltl_update(t, pi[n as int], n, progress).0, n + 1),
{
    let s = pi[n as int];
    let d = t->Until_0;
    let (l, r) = (*t->Until_1, *t->Until_4);
    let (a, ub) = (t->Until_2, t->Until_3);
    let (fl, fr) = (mltl_parse_tree_to_mltl_spec(l), mltl_parse_tree_to_mltl_spec(r));
    let w = operands_wpd(l, r);
    lemma_child_pass(l, pi, n, progress);
    lemma_child_pass(r, pi, n, progress);
    let (l2, r2) = (mltl_update(l, s, n, progress).0, mltl_update(r, s, n, progress).0);
    let (lq, rq) = (get_scq_from_tree(l2), get_scq_from_tree(r2));
    let (q, o, p) = until_op(d.scq, lq, rq, d.obs, progress);
    let tau = d.scq.next_time;
    lemma_until_next_time_mono(d.scq, lq, rq, d.obs, progress);
    if scq_read(d.scq, lq).is_some() && scq_read(d.scq, rq).is_some() {
        lemma_until_moves(d.scq, lq, rq, d.obs, progress);
    }
    lemma_stay(d.scq, lq, rq, q.next_time);
    lemma_stay(d.scq, rq, lq, q.next_time);
    lemma_edge_arith(fl, fr, w, n);
    lemma_edge_arith(fr, fl, w, n);
    let (hl, hr) = (get_execution_sequence(l), get_execution_sequence(r));
    let (hl2, hr2) = (get_execution_sequence(l2), get_execution_sequence(r2));
    if child_slack(w, fl) > sib_slack(fl, fr) {
        lemma_edge_pass(hl, hl2, hr2, tau, q.next_time, child_slack(w, fl), sib_slack(fl, fr),
            nat_sub(n + 1, bpd(fl)), nat_sub(n, wpd(fr)));
    }
    if child_slack(w, fr) > sib_slack(fr, fl) {
        lemma_edge_pass(hr, hr2, hl2, tau, q.next_time, child_slack(w, fr), sib_slack(fr, fl),
            nat_sub(n + 1, bpd(fr)), nat_sub(n, wpd(fl)));
    }
    let t2 = mltl_update(t, s, n, progress).0;
    assert(t2 == MltlParseTree::Until(NodeData { scq: q, obs: o }, Box::new(l2), a, ub, Box::new(r2)));
}

/// The last pass of step `n` (no progress anywhere) leaves `half_inv` for
/// step `n + 1`.
pub proof fn lemma_last_half<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n + 1),
        cov_ub(t, n + 1),
        half_inv(t, n + 1),
        nodes_ready(t, n + 1),
        untils_ready(t, n),
        n < pi.len(),
        mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
    ensures
        half_inv(mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 2),
    decreases t,
{
    let no = LoopProgress::ReloopNoProgress;
    let s = pi[n as int];
    match t {
        MltlParseTree::Not(d, c) => {
            let (c2, cp) = mltl_update(*c, s, n, no);
            let (q, p) = not_op(d.scq, get_scq_from_tree(c2), no);
            lemma_propagate_progress_2(cp, p);
            lemma_last_half(*c, pi, n);
        },
        MltlParseTree::And(d, l, r) => {
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            let (q, p) = and_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), no);
            lemma_propagate_progress_3(lp, rp, p);
            lemma_last_half(*l, pi, n);
            lemma_last_half(*r, pi, n);
            lemma_last_half_and(t, pi, n);
        },
        MltlParseTree::Until(d, l, _, _, r) => {
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            let (q, o, p) = until_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, no);
            lemma_propagate_progress_3(lp, rp, p);
            lemma_last_half(*l, pi, n);
            lemma_last_half(*r, pi, n);
            lemma_last_half_until(t, pi, n);
        },
        _ => {},
    }
}

/// Facts about a child in the last pass: unchanged, within its bound.
pub proof fn lemma_child_last<A>(c: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(c, pi, n + 1),
        cov_ub(c, n + 1),
        n < pi.len(),
        mltl_update(c, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
    ensures
        ({
            let c2 = mltl_update(c, pi[n as int], n, LoopProgress::ReloopNoProgress).0;
            &&& get_execution_sequence(c2) == get_execution_sequence(c)
            &&& mltl_parse_tree_to_mltl_spec(c2) == mltl_parse_tree_to_mltl_spec(c)
            &&& strictly_increasing(get_execution_sequence(c))
            &&& next_after(get_execution_sequence(c)) <= nat_sub(n + 1, bpd(mltl_parse_tree_to_mltl_spec(c)))
        }),
{
    lemma_rlnp_root(c, pi, n);
    lemma_update_shape(c, pi[n as int], n, LoopProgress::ReloopNoProgress);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_last_half_and<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        t is And,
        tree_inv(t, pi, n + 1),
        cov_ub(t, n + 1),
        half_inv(t, n + 1),
        nodes_ready(t, n + 1),
        untils_ready(t, n),
        n < pi.len(),
        mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
        mltl_update(*t->And_1, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
        mltl_update(*t->And_2, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
        half_inv(mltl_update(*t->And_1, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 2),
        half_inv(mltl_update(*t->And_2, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 2),
    ensures
        half_inv(mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 2),
{
    let no = LoopProgress::ReloopNoProgress;
    let s = pi[n as int];
    let d = t->And_0;
    let (l, r) = (*t->And_1, *t->And_2);
    let (fl, fr) = (mltl_parse_tree_to_mltl_spec(l), mltl_parse_tree_to_mltl_spec(r));
    let w = operands_wpd(l, r);
    lemma_last_pass(t, pi, n);
    lemma_child_last(l, pi, n);
    lemma_child_last(r, pi, n);
    let (l2, r2) = (mltl_update(l, s, n, no).0, mltl_update(r, s, n, no).0);
    let (lq, rq) = (get_scq_from_tree(l2), get_scq_from_tree(r2));
    let q = and_op(d.scq, lq, rq, no).0;
    let tau = d.scq.next_time;
    let t2 = mltl_update(t, s, n, no).0;
    assert(t2 == MltlParseTree::And(with_scq(d, q), Box::new(l2), Box::new(r2)));
    assert(tree_prompt(l2, n + 1) && tree_prompt(r2, n + 1));
    lemma_and_moves(d.scq, lq, rq, no);
    lemma_stay(d.scq, lq, rq, q.next_time);
    lemma_stay(d.scq, rq, lq, q.next_time);
    lemma_edge_arith(fl, fr, w, n + 1);
    lemma_edge_arith(fr, fl, w, n + 1);
    let (hl, hr) = (get_execution_sequence(l), get_execution_sequence(r));
    if child_slack(w, fl) > sib_slack(fl, fr) {
        lemma_edge_last(hl, hr, tau, q.next_time, child_slack(w, fl), sib_slack(fl, fr),
            nat_sub(n + 1, bpd(fl)), nat_sub(n + 2, bpd(fl)), nat_sub(n + 1, wpd(fr)), nat_sub(n + 1, w));
    }
    if child_slack(w, fr) > sib_slack(fr, fl) {
        lemma_edge_last(hr, hl, tau, q.next_time, child_slack(w, fr), sib_slack(fr, fl),
            nat_sub(n + 1, bpd(fr)), nat_sub(n + 2, bpd(fr)), nat_sub(n + 1, wpd(fl)), nat_sub(n + 1, w));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
proof fn lemma_last_half_until<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        t is Until,
        tree_inv(t, pi, n + 1),
        cov_ub(t, n + 1),
        half_inv(t, n + 1),
        nodes_ready(t, n + 1),
        untils_ready(t, n),
        n < pi.len(),
        mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
        mltl_update(*t->Until_1, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
        mltl_update(*t->Until_4, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
        half_inv(mltl_update(*t->Until_1, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 2),
        half_inv(mltl_update(*t->Until_4, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 2),
    ensures
        half_inv(mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 2),
{
    let no = LoopProgress::ReloopNoProgress;
    let s = pi[n as int];
    let d = t->Until_0;
    let (l, r) = (*t->Until_1, *t->Until_4);
    let (a, ub) = (t->Until_2, t->Until_3);
    let (fl, fr) = (mltl_parse_tree_to_mltl_spec(l), mltl_parse_tree_to_mltl_spec(r));
    let w = operands_wpd(l, r);
    lemma_last_pass(t, pi, n);
    lemma_child_last(l, pi, n);
    lemma_child_last(r, pi, n);
    let (l2, r2) = (mltl_update(l, s, n, no).0, mltl_update(r, s, n, no).0);
    let (lq, rq) = (get_scq_from_tree(l2), get_scq_from_tree(r2));
    let (q, o, p) = until_op(d.scq, lq, rq, d.obs, no);
    let tau = d.scq.next_time;
    let t2 = mltl_update(t, s, n, no).0;
    assert(t2 == MltlParseTree::Until(NodeData { scq: q, obs: o }, Box::new(l2), a, ub, Box::new(r2)));
    assert(tree_prompt(l2, n + 1) && tree_prompt(r2, n + 1));
    lemma_until_next_time_mono(d.scq, lq, rq, d.obs, no);
    if scq_read(d.scq, lq).is_some() && scq_read(d.scq, rq).is_some() {
        lemma_until_moves(d.scq, lq, rq, d.obs, no);
    }
    lemma_stay(d.scq, lq, rq, q.next_time);
    lemma_stay(d.scq, rq, lq, q.next_time);
    lemma_edge_arith(fl, fr, w, n + 1);
    lemma_edge_arith(fr, fl, w, n + 1);
    let (hl, hr) = (get_execution_sequence(l), get_execution_sequence(r));
    if child_slack(w, fl) > sib_slack(fl, fr) {
        lemma_edge_last(hl, hr, tau, q.next_time, child_slack(w, fl), sib_slack(fl, fr),
            nat_sub(n + 1, bpd(fl)), nat_sub(n + 2, bpd(fl)), nat_sub(n + 1, wpd(fr)), nat_sub(n + 1, w));
    }
    if child_slack(w, fr) > sib_slack(fr, fl) {
        lemma_edge_last(hr, hl, tau, q.next_time, child_slack(w, fr), sib_slack(fr, fl),
            nat_sub(n + 1, bpd(fr)), nat_sub(n + 2, bpd(fr)), nat_sub(n + 1, wpd(fl)), nat_sub(n + 1, w));
    }
}

// ---------------------------------------------------------------------------
// Room for the ring reads
// ---------------------------------------------------------------------------

/// The time bound: a reader at most `w + 1` steps behind `cap` has room.
pub proof fn lemma_room_time(c: Seq<Verdict>, tau: nat, w: nat, cap: nat)
    requires
        strictly_increasing(c),
        next_after(c) <= cap,
        tau >= nat_sub(cap, w + 1),
    ensures
        room(c, tau, w, cap),
{
    lemma_first_idx(c, tau);
    let k = first_idx(c, tau);
    if k < c.len() {
        lemma_time_gap(c, k as int, c.len() - 1);
    }
}

/// A room bound for a larger `cap` holds for a smaller one too.
pub proof fn lemma_room_cap(c: Seq<Verdict>, tau: nat, w: nat, cap: nat, cap2: nat)
    requires
        room(c, tau, w, cap),
        cap2 <= cap,
    ensures
        room(c, tau, w, cap2),
{
}

/// Room for the read of child `c` (sibling formula `fs`, operands' `wpd`
/// `w`) by a reader at `tau` in a pass of step `n`, after the child's
/// update; and, in the last pass of the step, room for the next step.
pub proof fn lemma_child_rooms<A>(c: Tree<A>, fs: Mltl<A>, w: nat, tau: nat, pi: Seq<Set<A>>, n: nat,
    progress: LoopProgress)
    requires
        cov_pre(c, pi, n, progress),
        tree_prompt(c, n),
        w >= wpd(mltl_parse_tree_to_mltl_spec(c)),
        w >= wpd(fs),
        tau >= nat_sub(n, w),
        edge_ok(get_execution_sequence(c), mltl_parse_tree_to_mltl_spec(c), fs, w, tau, n + 1),
    ensures
        ({
            let fc = mltl_parse_tree_to_mltl_spec(c);
            let cc = compact(get_execution_sequence(mltl_update(c, pi[n as int], n, progress).0));
            let sl = ring_slack(w, fc, fs);
            &&& room(cc, tau, sl, nat_sub(n + 1, bpd(fc)))
            &&& (progress == LoopProgress::ReloopNoProgress
                && mltl_update(c, pi[n as int], n, progress).1 == LoopProgress::ReloopNoProgress
                && tau >= nat_sub(n + 1, w)) ==> room(cc, tau, sl, nat_sub(n + 2, bpd(fc)))
        }),
{
    let s = pi[n as int];
    let fc = mltl_parse_tree_to_mltl_spec(c);
    let h = get_execution_sequence(c);
    let h2 = get_execution_sequence(mltl_update(c, s, n, progress).0);
    let cc = compact(h2);
    let x = child_slack(w, fc);
    let y = sib_slack(fc, fs);
    let cap = nat_sub(n + 1, bpd(fc));
    let cap2 = nat_sub(n + 2, bpd(fc));
    lemma_child_pass(c, pi, n, progress);
    lemma_compact(h2);
    assert(cap2 <= cap + 1);
    if x > y {
        lemma_psi_write(h, h2, tau, cap);
        lemma_room_half(cc, tau, cap, x, y);
        if progress == LoopProgress::ReloopNoProgress && mltl_update(c, s, n, progress).1 == LoopProgress::ReloopNoProgress {
            lemma_rlnp_root(c, pi, n);
            lemma_room_half_last(cc, tau, cap, x, y);
        }
    } else {
        assert(x == y);
        assert(ring_slack(w, fc, fs) == x);
        lemma_cap_slack(n + 1, w, bpd(fc));
        lemma_room_time(cc, tau, x, cap);
        if tau >= nat_sub(n + 1, w) {
            lemma_cap_slack(n + 2, w, bpd(fc));
            lemma_room_time(cc, tau, x, cap2);
        }
    }
}

/// The initial tree (nothing written) satisfies `half_inv` for step 0.
pub proof fn lemma_initial_half<A>(f: Mltl<A>)
    ensures
        half_inv(parse_tree_with_scq(f), 1),
    decreases f,
{
    lemma_initial_shape(f);
    assert(compact(Seq::<Verdict>::empty()) =~= Seq::<Verdict>::empty());
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => lemma_initial_half(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            lemma_initial_half(*phi);
            lemma_initial_half(*psi);
            lemma_initial_shape(*phi);
            lemma_initial_shape(*psi);
            lemma_first_idx(Seq::<Verdict>::empty(), 0);
        },
        _ => {},
    }
}

} // verus!
