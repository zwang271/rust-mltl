//! The ring monitor computes exactly what the history monitor computes
//! ([`r2u2_ring_eq`]), so soundness and promptness hold for it
//! ([`r2u2_ring_correct`]) with [`child_slots`] slots per child queue: 1 for
//! the child of a NOT, `w − bpd(c) + 1` for a child `c` of a binary node
//! (`w = wpd(operands)` of the reader). Write `w_c = w − bpd(c)` for the
//! child's slack, so its ring has `w_c + 1` slots.
//!
//! Pointer invariant ([`ptr_inv`]) before each pass of step `n`, with the
//! child's coverage bound `cap = (n + 1) − bpd(c)` as `m` (`tight.rs`:
//! [`cov_ub`] — a node cannot have covered more): the pointer is at an entry
//! `j` at or before the reader's first needed entry, and either at most `w_c`
//! entries from `j` to the end, or `w_c + 1` and the child has covered all of
//! `cap` (so it cannot add an entry before the next read), or the reader needs
//! nothing stored and `j` is the last entry.
//!
//! Each read leaves the pointer at the first needed entry or the last one.
//! For a child of a binary node the backlog is at most `cap − tau ≤ w_c + 1`
//! (`queue_size.rs`), using `tau ≥ n − w` (promptness). In the last pass of a
//! step every reader already reads at `(n + 1) − w`
//! (`queue_size.rs : lemma_last_ready`), which is what the next step's bound
//! `cap + 1` needs. For the child of a NOT the reader is always at or past
//! everything the child wrote (`tight.rs`: [`not_caught`]), so only the
//! child's newest entry can still be needed and one slot is enough
//! ([`lemma_child_read_caught`]).
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use mltl_core::properties::*;
use crate::verdict::*;
use crate::scq::*;
use crate::operators::*;
use crate::engine::*;
use crate::soundness::*;
use crate::until::*;
use crate::promptness::*;
use crate::queue_size::*;
use crate::ring::*;
use crate::ring_engine::*;
use crate::tight::*;

verus! {

// ---------------------------------------------------------------------------
// first_idx under appends
// ---------------------------------------------------------------------------

pub proof fn lemma_first_idx_mono(c: Seq<Verdict>, t1: nat, t2: nat)
    requires
        t1 <= t2,
    ensures
        first_idx(c, t1) <= first_idx(c, t2),
{
    lemma_first_idx(c, t1);
    lemma_first_idx(c, t2);
    let f2 = first_idx(c, t2);
    if f2 < first_idx(c, t1) {
        assert(c[f2 as int].time < t1);
    }
}

pub proof fn lemma_first_idx_push(c: Seq<Verdict>, v: Verdict, t: nat)
    ensures
        first_idx(c.push(v), t) == (if first_idx(c, t) < c.len() { first_idx(c, t) }
            else if v.time >= t { c.len() } else { c.len() + 1 }),
{
    let c2 = c.push(v);
    lemma_first_idx(c, t);
    let f = first_idx(c, t);
    assert forall|i: int| 0 <= i < c.len() implies c2[i] == c[i] by {}
    if f < c.len() {
        assert forall|i: int| 0 <= i < f implies #[trigger] c2[i].time < t by { assert(c2[i] == c[i]); }
        assert(c2[f as int] == c[f as int]);
        lemma_first_idx_unique(c2, t, f);
    } else if v.time >= t {
        assert forall|i: int| 0 <= i < c.len() implies #[trigger] c2[i].time < t by { assert(c2[i] == c[i]); }
        lemma_first_idx_unique(c2, t, c.len());
    } else {
        assert forall|i: int| 0 <= i < c2.len() implies #[trigger] c2[i].time < t by {
            if i < c.len() { assert(c2[i] == c[i]); }
        }
        lemma_first_idx_unique(c2, t, c2.len());
    }
}

pub proof fn lemma_first_idx_update_last(c: Seq<Verdict>, v: Verdict, t: nat)
    requires
        c.len() > 0,
        v.time >= c.last().time,
    ensures
        first_idx(c.update(c.len() - 1, v), t) == (if first_idx(c, t) < c.len() - 1 { first_idx(c, t) }
            else if v.time >= t { (c.len() - 1) as nat } else { c.len() }),
{
    let l = c.len() - 1;
    let c2 = c.update(l, v);
    lemma_first_idx(c, t);
    let f = first_idx(c, t);
    if f < l {
        assert forall|i: int| 0 <= i < f implies #[trigger] c2[i].time < t by { assert(c2[i] == c[i]); }
        assert(c2[f as int] == c[f as int]);
        lemma_first_idx_unique(c2, t, f);
    } else if v.time >= t {
        assert forall|i: int| 0 <= i < l implies #[trigger] c2[i].time < t by { assert(c2[i] == c[i]); }
        lemma_first_idx_unique(c2, t, l as nat);
    } else {
        assert forall|i: int| 0 <= i < c2.len() implies #[trigger] c2[i].time < t by {
            if i < l { assert(c2[i] == c[i]); }
        }
        lemma_first_idx_unique(c2, t, c2.len());
    }
}

/// A reader at or past everything the child had written can still need only
/// the child's one new entry, so the child's last stored entry.
pub proof fn lemma_caught_first_idx(h: Seq<Verdict>, h2: Seq<Verdict>, tau: nat)
    requires
        strictly_increasing(h2),
        h2 == h || h2 == h.push(h2.last()),
        tau >= next_after(h),
    ensures
        first_idx(compact(h2), tau) + 1 >= compact(h2).len(),
{
    let c2 = compact(h2);
    lemma_compact(h2);
    lemma_first_idx(c2, tau);
    if h2 == h {
        assert forall|i: int| 0 <= i < c2.len() implies #[trigger] c2[i].time < tau by {
            if i < c2.len() - 1 { assert(c2[i].time < c2[c2.len() - 1].time); }
        }
        lemma_first_idx_unique(c2, tau, c2.len());
    } else {
        let v = h2.last();
        assert(h2.drop_last() =~= h);
        assert(strictly_increasing(h)) by {
            assert forall|i: int, k: int| #![trigger h[i], h[k]] 0 <= i < k < h.len() implies h[i].time < h[k].time by {
                assert(h[i] == h2[i] && h[k] == h2[k]);
            }
        }
        lemma_compact(h);
        let c = compact(h);
        if c.len() > 0 {
            if c.last().val == v.val {
                assert(c2 == c.update(c.len() - 1, v));
            } else {
                assert(c2 == c.push(v));
            }
            assert forall|i: int| 0 <= i < c2.len() - 1 implies #[trigger] c2[i].time < tau by {
                assert(c2[i] == c[i]);
                if i < c.len() - 1 { assert(c[i].time < c[c.len() - 1].time); }
            }
            if first_idx(c2, tau) + 1 < c2.len() {
                assert(c2[first_idx(c2, tau) as int].time < tau);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Read pointers
// ---------------------------------------------------------------------------

/// How many entries from the pointer to the end are allowed (see the module
/// comment); `cov` is what the child has covered, `m` the steps read.
pub open spec fn ptr_room(j: nat, c: Seq<Verdict>, tau: nat, w: nat, m: nat, cov: nat) -> bool {
    ||| c.len() - j <= w
    ||| (c.len() - j == w + 1 && cov >= m)
    ||| (first_idx(c, tau) >= c.len() && c.len() - j <= 1)
}

pub open spec fn ptr_at(j: nat, rd: nat, c: Seq<Verdict>, size: nat, tau: nat, w: nat, m: nat, cov: nat) -> bool {
    &&& j < c.len()
    &&& rd == j as int % (size as int)
    &&& j <= first_idx(c, tau)
    &&& ptr_room(j, c, tau, w, m, cov)
}

/// The pointer `rd` into `child` is usable by a reader at `tau` (module comment).
pub open spec fn ptr_inv(rd: nat, child: RNode, tau: nat, w: nat, m: nat) -> bool {
    let c = compact(child.all_values);
    (c.len() == 0 && rd == 0)
        || exists|j: nat| #[trigger] ptr_at(j, rd, c, child.ring.slots.len(), tau, w, m, next_after(child.all_values))
}

/// At a read, after the child wrote at most once and stayed within its
/// coverage bound `cap`: an entry `j2` at the pointer's slot, at or before
/// the first needed entry, with at most `w + 1` entries to the end (so
/// `lemma_ring_read` applies).
pub proof fn lemma_ptr_read_pos(h: Seq<Verdict>, h2: Seq<Verdict>, rd: nat, size: nat, tau: nat, w: nat, cap: nat) -> (j2: nat)
    requires
        size == w + 1,
        strictly_increasing(h2),
        next_after(h2) <= cap,
        h2 == h || h2 == h.push(h2.last()),
        (compact(h).len() == 0 && rd == 0)
            || exists|j: nat| #[trigger] ptr_at(j, rd, compact(h), size, tau, w, cap, next_after(h)),
    ensures
        (compact(h2).len() == 0 && rd == 0) || (j2 < compact(h2).len() && rd == j2 as int % (size as int)
            && j2 <= first_idx(compact(h2), tau) && compact(h2).len() - j2 <= size),
{
    let c = compact(h);
    let c2 = compact(h2);
    lemma_compact(h2);
    if h2 == h {
        if c.len() == 0 && rd == 0 {
            0
        } else {
            let j = choose|j: nat| #[trigger] ptr_at(j, rd, c, size, tau, w, cap, next_after(h));
            j
        }
    } else {
        let v = h2.last();
        assert(h2.drop_last() =~= h);
        assert(strictly_increasing(h)) by {
            assert forall|i: int, k: int| #![trigger h[i], h[k]] 0 <= i < k < h.len() implies h[i].time < h[k].time by {
                assert(h[i] == h2[i] && h[k] == h2[k]);
            }
        }
        lemma_compact(h);
        if h.len() > 0 {
            assert(h.last() == h2[h2.len() - 2]);
            assert(h2[h2.len() - 2].time < h2.last().time);
        }
        assert(v.time >= next_after(h));
        if c.len() == 0 && rd == 0 {
            assert(c2 == c.push(v));
            lemma_small_mod_0(size);
            0
        } else {
            let j = choose|j: nat| #[trigger] ptr_at(j, rd, c, size, tau, w, cap, next_after(h));
            if c.last().val == v.val {
                assert(c2 == c.update(c.len() - 1, v));
                lemma_first_idx_update_last(c, v, tau);
                j
            } else {
                assert(c2 == c.push(v));
                lemma_first_idx_push(c, v, tau);
                if c.len() - j <= w {
                    j
                } else if c.len() - j == w + 1 && next_after(h) >= cap {
                    // the child covered the whole step: it cannot have added an entry
                    assert(false);
                    j
                } else if w >= 1 {
                    j
                } else {
                    // one slot: the slot now holds the new entry, the only one needed
                    vstd::arithmetic::div_mod::lemma_mod_self_0(1);
                    vstd::arithmetic::div_mod::lemma_small_mod(0, 1);
                    let j2 = (c2.len() - 1) as nat;
                    assert(j as int % 1 == 0 && j2 as int % 1 == 0) by {
                        vstd::arithmetic::div_mod::lemma_mod_pos_bound(j as int, 1);
                        vstd::arithmetic::div_mod::lemma_mod_pos_bound(j2 as int, 1);
                    }
                    j2
                }
            }
        }
    }
}

proof fn lemma_small_mod_0(size: nat)
    requires
        size > 0,
    ensures
        0int % (size as int) == 0,
{
    vstd::arithmetic::div_mod::lemma_small_mod(0, size);
}

/// After a read by a reader at `tau ≥ cap − (w + 1)` of a child that covers
/// at most `cap`: the pointer (at the first needed entry, or the last)
/// satisfies the invariant for `m = cap`.
pub proof fn lemma_ptr_after_read(c: Seq<Verdict>, size: nat, tau: nat, tau2: nat, w: nat, cap: nat, cov: nat)
    requires
        strictly_increasing(c),
        tau <= tau2,
        c.len() > 0,
        size > 0,
        next_after(c) == cov,
        cov <= cap,
        tau >= nat_sub(cap, w + 1),
    ensures
        ({
            let j2: nat = if first_idx(c, tau) < c.len() { first_idx(c, tau) } else { (c.len() - 1) as nat };
            ptr_at(j2, (j2 as int % (size as int)) as nat, c, size, tau2, w, cap, cov)
        }),
{
    lemma_first_idx(c, tau);
    lemma_first_idx_mono(c, tau, tau2);
    let j2: nat = if first_idx(c, tau) < c.len() { first_idx(c, tau) } else { (c.len() - 1) as nat };
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j2 as int, size as int);
    if first_idx(c, tau) < c.len() {
        lemma_time_gap(c, j2 as int, c.len() - 1);
    }
}

/// After a read by a reader that was, and stays, at or past everything the
/// child wrote: the pointer is at the child's last entry, which is all the
/// reader can still need. Good for every `m`, however far behind the child is.
pub proof fn lemma_ptr_after_read_caught(c: Seq<Verdict>, size: nat, tau: nat, tau2: nat, w: nat, m: nat, cov: nat)
    requires
        strictly_increasing(c),
        c.len() > 0,
        size > 0,
        next_after(c) == cov,
        tau2 >= cov,
        first_idx(c, tau) + 1 >= c.len(),
    ensures
        ({
            let j2: nat = if first_idx(c, tau) < c.len() { first_idx(c, tau) } else { (c.len() - 1) as nat };
            ptr_at(j2, (j2 as int % (size as int)) as nat, c, size, tau2, w, m, cov)
        }),
{
    lemma_first_idx(c, tau);
    let j2: nat = if first_idx(c, tau) < c.len() { first_idx(c, tau) } else { (c.len() - 1) as nat };
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j2 as int, size as int);
    assert forall|i: int| 0 <= i < c.len() implies #[trigger] c[i].time < tau2 by {
        if i < c.len() - 1 { assert(c[i].time < c[c.len() - 1].time); }
    }
    lemma_first_idx_unique(c, tau2, c.len());
}

/// `nat_sub` composes, so a child's own bound is never later than the
/// uniform one: `(k − b) − (w − b + 1) ≤ k − (w + 1)`.
pub proof fn lemma_cap_slack(k: nat, w: nat, b: nat)
    ensures
        nat_sub(nat_sub(k, b), nat_sub(w, b) + 1) <= nat_sub(k, w + 1),
{
}

// ---------------------------------------------------------------------------
// The ring tree invariant
// ---------------------------------------------------------------------------

pub open spec fn rnode_ok(d: RNode, size: nat) -> bool {
    ring_abs(d.ring, compact(d.all_values)) && d.ring.slots.len() == size
}

/// Every ring abstracts its history; every pointer is usable (`ptr_inv`,
/// `m` steps read, so child `c` covers at most `m − bpd(c)`); the child of a
/// NOT has 1 slot, a child `c` of a binary node has `child_slots` slots.
pub open spec fn rtree_inv<A>(t: RTree<A>, size: nat, m: nat) -> bool
    decreases t,
{
    &&& rnode_ok(get_aux_data(t), size)
    &&& match t {
        MltlParseTree::Not(d, c) => {
            let f = mltl_parse_tree_to_mltl_spec(*c);
            ptr_inv(d.rd_left, get_aux_data(*c), d.next_time, 0, nat_sub(m, bpd(f))) && rtree_inv(*c, 1, m)
        },
        MltlParseTree::And(d, l, r) | MltlParseTree::Until(d, l, _, _, r) => {
            let w = operands_wpd(*l, *r);
            let fl = mltl_parse_tree_to_mltl_spec(*l);
            let fr = mltl_parse_tree_to_mltl_spec(*r);
            &&& ptr_inv(d.rd_left, get_aux_data(*l), d.next_time, child_slack(w, fl), nat_sub(m, bpd(fl)))
            &&& ptr_inv(d.rd_right, get_aux_data(*r), d.next_time, child_slack(w, fr), nat_sub(m, bpd(fr)))
            &&& rtree_inv(*l, child_slots(w, fl), m) && rtree_inv(*r, child_slots(w, fr), m)
        },
        _ => true,
    }
}

pub proof fn lemma_abs_shape<A>(t: RTree<A>)
    ensures
        mltl_parse_tree_to_mltl_spec(abs_tree(t)) == mltl_parse_tree_to_mltl_spec(t),
        get_aux_data(abs_tree(t)) == abs_node(get_aux_data(t)),
        size_parse_tree(abs_tree(t)) == size_parse_tree(t),
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) | MltlParseTree::Future(_, _, _, c) | MltlParseTree::Global(_, _, _, c) => lemma_abs_shape(*c),
        MltlParseTree::And(_, l, r) | MltlParseTree::Or(_, l, r) | MltlParseTree::Until(_, l, _, _, r)
        | MltlParseTree::Release(_, l, _, _, r) => {
            lemma_abs_shape(*l);
            lemma_abs_shape(*r);
        },
        _ => {},
    }
}

/// A pass writes at most one verdict at a node.
pub proof fn lemma_update_root<A>(t: Tree<A>, s: Set<A>, n: nat, progress: LoopProgress)
    ensures
        ({
            let h = get_execution_sequence(t);
            let h2 = get_execution_sequence(mltl_update(t, s, n, progress).0);
            h2 == h || h2 == h.push(h2.last())
        }),
{
    let h = get_execution_sequence(t);
    match t {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {
            let h2 = get_execution_sequence(mltl_update(t, s, n, progress).0);
            if h2 != h { assert(h2 == h.push(h2.last())); }
        },
        _ => {
            let h2 = get_execution_sequence(mltl_update(t, s, n, progress).0);
            if h2 != h { assert(h2 == h.push(h2.last())); }
        },
    }
}

/// Coverage never goes down, so passes keep `tree_prompt`.
pub proof fn lemma_update_prompt<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress, k: nat)
    requires
        (progress == LoopProgress::FirstLoop && tree_inv(t, pi, n))
            || (progress == LoopProgress::ReloopNoProgress && tree_inv(t, pi, n + 1)),
        n < pi.len(),
        tree_prompt(t, k),
    ensures
        tree_prompt(mltl_update(t, pi[n as int], n, progress).0, k),
    decreases t,
{
    let s = pi[n as int];
    lemma_update_shape(t, s, n, progress);
    lemma_update_root(t, s, n, progress);
    child_updated_inv(t, pi, n, progress);
    let h = get_execution_sequence(t);
    let h2 = get_execution_sequence(mltl_update(t, s, n, progress).0);
    if h2 != h {
        assert(h2[h2.len() - 1] == h2.last());
        if h.len() > 0 {
            assert(h2[h.len() - 1] == h.last());
            assert(h2[h.len() - 1].time < h2[h2.len() - 1].time);
        }
    }
    assert(next_after(h2) >= next_after(h));
    match t {
        MltlParseTree::Not(_, c) => lemma_update_prompt(*c, pi, n, progress, k),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => {
            lemma_update_prompt(*l, pi, n, progress, k);
            lemma_update_prompt(*r, pi, n, progress, k);
        },
        _ => {},
    }
}

pub proof fn lemma_prompt_zero<A>(t: Tree<A>)
    ensures
        tree_prompt(t, 0),
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => lemma_prompt_zero(*c),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => {
            lemma_prompt_zero(*l);
            lemma_prompt_zero(*r);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// One child read
// ---------------------------------------------------------------------------

/// The read of one (updated) child through the reader's pointer: same as
/// the history read, and the new pointer is usable again — for the next
/// step's bound `cap + 1` too if the reader is already that far along.
pub proof fn lemma_child_read<A>(c: RTree<A>, c2: RTree<A>, rd: nat, tau: nat, tau2: nat, w: nat, cap: nat, cap2: nat)
    requires
        cap <= cap2,
        ptr_inv(rd, get_aux_data(c), tau, w, cap),
        rnode_ok(get_aux_data(c2), w + 1),
        get_aux_data(c2).ring.slots.len() == get_aux_data(c).ring.slots.len(),
        strictly_increasing(get_aux_data(c2).all_values),
        next_after(get_aux_data(c2).all_values) <= cap,
        get_aux_data(c2).all_values == get_aux_data(c).all_values
            || get_aux_data(c2).all_values == get_aux_data(c).all_values.push(get_aux_data(c2).all_values.last()),
        tau <= tau2,
        tau >= nat_sub(cap, w + 1),
    ensures
        ring_read(get_ring(c2), rd, tau).0 == first_from(compact(get_aux_data(c2).all_values), tau),
        ptr_inv(ring_read(get_ring(c2), rd, tau).1, get_aux_data(c2), tau2, w, cap),
        tau >= nat_sub(cap2, w + 1) ==> ptr_inv(ring_read(get_ring(c2), rd, tau).1, get_aux_data(c2), tau2, w, cap2),
{
    let d2 = get_aux_data(c2);
    let size = w + 1;
    let h = get_aux_data(c).all_values;
    let h2 = d2.all_values;
    let j = lemma_ptr_read_pos(h, h2, rd, size, tau, w, cap);
    let c2c = compact(h2);
    lemma_compact(h2);
    lemma_ring_read(d2.ring, c2c, rd, j, tau);
    if c2c.len() > 0 {
        let j2: nat = if first_idx(c2c, tau) < c2c.len() { first_idx(c2c, tau) } else { (c2c.len() - 1) as nat };
        lemma_ptr_after_read(c2c, size, tau, tau2, w, cap, next_after(h2));
        assert(ptr_at(j2, ring_read(get_ring(c2), rd, tau).1, c2c, size, tau2, w, cap, next_after(h2)));
        if tau >= nat_sub(cap2, w + 1) {
            lemma_ptr_after_read(c2c, size, tau, tau2, w, cap2, next_after(h2));
            assert(ptr_at(j2, ring_read(get_ring(c2), rd, tau).1, c2c, size, tau2, w, cap2, next_after(h2)));
        }
    }
}

/// The read of one (updated) child by a reader that is, and stays, at or past
/// everything the child wrote (a NOT node): same as the history read, and one
/// slot is enough for any bound `m`.
pub proof fn lemma_child_read_caught<A>(c: RTree<A>, c2: RTree<A>, rd: nat, tau: nat, tau2: nat, cap: nat, m: nat)
    requires
        ptr_inv(rd, get_aux_data(c), tau, 0, cap),
        rnode_ok(get_aux_data(c2), 1),
        get_aux_data(c2).ring.slots.len() == get_aux_data(c).ring.slots.len(),
        strictly_increasing(get_aux_data(c2).all_values),
        next_after(get_aux_data(c2).all_values) <= cap,
        get_aux_data(c2).all_values == get_aux_data(c).all_values
            || get_aux_data(c2).all_values == get_aux_data(c).all_values.push(get_aux_data(c2).all_values.last()),
        tau >= next_after(get_aux_data(c).all_values),
        tau2 >= next_after(get_aux_data(c2).all_values),
    ensures
        ring_read(get_ring(c2), rd, tau).0 == first_from(compact(get_aux_data(c2).all_values), tau),
        ptr_inv(ring_read(get_ring(c2), rd, tau).1, get_aux_data(c2), tau2, 0, m),
{
    let d2 = get_aux_data(c2);
    let h = get_aux_data(c).all_values;
    let h2 = d2.all_values;
    let j = lemma_ptr_read_pos(h, h2, rd, 1, tau, 0, cap);
    let c2c = compact(h2);
    lemma_compact(h2);
    lemma_ring_read(d2.ring, c2c, rd, j, tau);
    if c2c.len() > 0 {
        let j2: nat = if first_idx(c2c, tau) < c2c.len() { first_idx(c2c, tau) } else { (c2c.len() - 1) as nat };
        lemma_caught_first_idx(h, h2, tau);
        lemma_ptr_after_read_caught(c2c, 1, tau, tau2, 0, m, next_after(h2));
        assert(ptr_at(j2, ring_read(get_ring(c2), rd, tau).1, c2c, 1, tau2, 0, m, next_after(h2)));
    }
}

// ---------------------------------------------------------------------------
// One pass
// ---------------------------------------------------------------------------

pub proof fn lemma_store_ok(d: RNode, q: Scq, size: nat)
    requires
        rnode_ok(d, size),
        strictly_increasing(q.all_values),
        q.all_values == d.all_values || q.all_values == d.all_values.push(q.all_values.last()),
    ensures
        rnode_ok(store(d, q), size),
        abs_node(store(d, q)) == with_scq(abs_node(d), q),
{
    if q.all_values != d.all_values {
        assert(q.all_values.len() > d.all_values.len());
        lemma_ring_write(d.ring, d.all_values, q.all_values.last());
    }
}

/// What the induction gives for a child: its pass is simulated.
pub open spec fn sim_ok<A>(c: RTree<A>, size: nat, s: Set<A>, n: nat, progress: LoopProgress) -> bool {
    &&& abs_tree(mltl_update_r(c, s, n, progress).0) == mltl_update(abs_tree(c), s, n, progress).0
    &&& mltl_update_r(c, s, n, progress).1 == mltl_update(abs_tree(c), s, n, progress).1
    &&& rtree_inv(mltl_update_r(c, s, n, progress).0, size, n + 1)
    &&& nodes_ready(abs_tree(c), n + 1) ==> rtree_inv(mltl_update_r(c, s, n, progress).0, size, n + 2)
}

/// The facts about the history side that the simulation of a pass needs.
pub open spec fn hist_pre<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress) -> bool {
    &&& (progress == LoopProgress::FirstLoop && tree_inv(t, pi, n) && cov_ub(t, n))
        || (progress == LoopProgress::ReloopNoProgress && tree_inv(t, pi, n + 1) && cov_ub(t, n + 1))
    &&& not_caught(t)
    &&& nodes_ready(t, n)
    &&& tree_prompt(t, n)
    &&& n < pi.len()
}

/// Facts about one updated child, for `lemma_child_read`.
pub proof fn lemma_child_facts<A>(c: RTree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress, size: nat)
    requires
        hist_pre(abs_tree(c), pi, n, progress),
        sim_ok(c, size, pi[n as int], n, progress),
        rnode_ok(get_aux_data(c), size),
    ensures
        ({
            let c2 = mltl_update_r(c, pi[n as int], n, progress).0;
            let ch2 = mltl_update(abs_tree(c), pi[n as int], n, progress).0;
            &&& rnode_ok(get_aux_data(c2), size)
            &&& get_aux_data(c2).ring.slots.len() == get_aux_data(c).ring.slots.len()
            &&& hist_inv(get_aux_data(c2).all_values, mltl_parse_tree_to_mltl_spec(c2), pi, n + 1)
            &&& get_aux_data(c2).all_values == get_aux_data(c).all_values
                || get_aux_data(c2).all_values == get_aux_data(c).all_values.push(get_aux_data(c2).all_values.last())
            &&& get_scq_from_tree(ch2) == rscq(get_aux_data(c2))
            &&& mltl_parse_tree_to_mltl_spec(ch2) == mltl_parse_tree_to_mltl_spec(c)
            &&& tree_inv(ch2, pi, n + 1)
            &&& cov_ub(ch2, n + 1)
            &&& not_caught(ch2)
            &&& next_after(get_aux_data(c2).all_values) <= nat_sub(n + 1, bpd(mltl_parse_tree_to_mltl_spec(c)))
        }),
{
    let s = pi[n as int];
    let ch = abs_tree(c);
    let c2 = mltl_update_r(c, s, n, progress).0;
    lemma_abs_shape(c);
    lemma_abs_shape(c2);
    child_updated_inv(ch, pi, n, progress);
    lemma_update_root(ch, s, n, progress);
    lemma_update_shape(ch, s, n, progress);
    lemma_update_cov_ub(ch, pi, n, progress);
    lemma_update_not_caught(ch, pi, n, progress);
}

/// A ring pass keeps the formula.
pub proof fn lemma_update_r_shape<A>(t: RTree<A>, s: Set<A>, n: nat, progress: LoopProgress)
    ensures
        mltl_parse_tree_to_mltl_spec(mltl_update_r(t, s, n, progress).0) == mltl_parse_tree_to_mltl_spec(t),
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => lemma_update_r_shape(*c, s, n, progress),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => {
            lemma_update_r_shape(*l, s, n, progress);
            lemma_update_r_shape(*r, s, n, progress);
        },
        _ => {},
    }
}

/// The history-side facts pass down to the children.
pub proof fn lemma_hist_pre_children<A>(t: RTree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        hist_pre(abs_tree(t), pi, n, progress),
    ensures
        match t {
            MltlParseTree::Not(_, c) => hist_pre(abs_tree(*c), pi, n, progress) && tree_prompt(abs_tree(*c), n),
            MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) =>
                hist_pre(abs_tree(*l), pi, n, progress) && hist_pre(abs_tree(*r), pi, n, progress)
                && tree_prompt(abs_tree(*l), n) && tree_prompt(abs_tree(*r), n),
            _ => true,
        },
{
}

#[verifier::spinoff_prover]
pub proof fn lemma_sim_leaf<A>(t: RTree<A>, size: nat, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        t is True || t is False || t is Prop,
        rtree_inv(t, size, n + 1),
        hist_pre(abs_tree(t), pi, n, progress),
    ensures
        sim_ok(t, size, pi[n as int], n, progress),
{
    let s = pi[n as int];
    let at = abs_tree(t);
    let d = get_aux_data(t);
    let v = match t {
        MltlParseTree::True(_) => Verdict { val: true, time: n },
        MltlParseTree::False(_) => Verdict { val: false, time: n },
        MltlParseTree::Prop(_, a) => Verdict { val: s.contains(a), time: n },
        _ => arbitrary(),
    };
    let (q, p) = load(rscq(d), v, progress);
    assert(mltl_update_r(t, s, n, progress).1 == p);
    assert(mltl_update(at, s, n, progress).1 == p);
    assert(get_aux_data(mltl_update_r(t, s, n, progress).0) == store(d, q));
    lemma_abs_shape(t);
    child_updated_inv(at, pi, n, progress);
    assert(get_execution_sequence(mltl_update(at, s, n, progress).0) == q.all_values);
    lemma_store_ok(d, q, size);
    match t {
        MltlParseTree::True(_) => {
            assert(abs_tree(mltl_update_r(t, s, n, progress).0) == MltlParseTree::<A, NodeData>::True(abs_node(store(d, q))));
        },
        MltlParseTree::False(_) => {
            assert(abs_tree(mltl_update_r(t, s, n, progress).0) == MltlParseTree::<A, NodeData>::False(abs_node(store(d, q))));
        },
        MltlParseTree::Prop(_, a) => {
            assert(abs_tree(mltl_update_r(t, s, n, progress).0) == MltlParseTree::<A, NodeData>::Prop(abs_node(store(d, q)), a));
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub proof fn lemma_sim_not<A>(t: RTree<A>, size: nat, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        t is Not,
        rtree_inv(t, size, n + 1),
        hist_pre(abs_tree(t), pi, n, progress),
        sim_ok(*t->Not_1, 1, pi[n as int], n, progress),
    ensures
        sim_ok(t, size, pi[n as int], n, progress),
{
    let s = pi[n as int];
    let d = t->Not_0;
    let c = *t->Not_1;
    let f = mltl_parse_tree_to_mltl_spec(c);
    let cap = nat_sub(n + 1, bpd(f));
    lemma_abs_shape(t);
    lemma_abs_shape(c);
    let at = abs_tree(t);
    child_updated_inv(at, pi, n, progress);
    lemma_update_root(at, s, n, progress);
    assert(rtree_inv(c, 1, n + 1));
    assert(rnode_ok(get_aux_data(c), 1));
    lemma_hist_pre_children(t, pi, n, progress);
    lemma_child_facts(c, pi, n, progress, 1);
    let c2 = mltl_update_r(c, s, n, progress).0;
    let c2h = mltl_update(abs_tree(c), s, n, progress).0;
    lemma_not_step(rscq(d), get_scq_from_tree(c2h), mltl_parse_tree_to_mltl_spec(c), pi, n + 1, progress);
    let (q, p) = not_op(rscq(d), get_scq_from_tree(c2h), progress);
    assert(d.next_time >= next_after(get_aux_data(c).all_values));
    lemma_not_catch_up(rscq(d), get_aux_data(c).all_values, get_scq_from_tree(c2h), progress);
    lemma_child_read_caught(c, c2, d.rd_left, d.next_time, q.next_time, cap, cap);
    lemma_child_read_caught(c, c2, d.rd_left, d.next_time, q.next_time, cap, nat_sub(n + 2, bpd(f)));
    lemma_store_ok(d, q, size);
    let cp = mltl_update_r(c, s, n, progress).1;
    let (data, rd) = ring_read(get_ring(c2), d.rd_left, d.next_time);
    assert(data == scq_read(rscq(d), get_scq_from_tree(c2h)));
    assert(not_core(rscq(d), data, progress) == (q, p));
    let nd = RNode { rd_left: rd, ..store(d, q) };
    assert(mltl_update_r(t, s, n, progress) == (MltlParseTree::Not(nd, Box::new(c2)), propagate_progress(seq![cp, p])));
    assert(abs_node(nd) == with_scq(abs_node(d), q));
    assert(abs_node(d).scq == rscq(d));
    assert(mltl_update(at, s, n, progress) == (MltlParseTree::Not(with_scq(abs_node(d), q), Box::new(c2h)),
        propagate_progress(seq![mltl_update(abs_tree(c), s, n, progress).1, p])));
    assert(abs_tree(MltlParseTree::Not(nd, Box::new(c2))) == MltlParseTree::Not(abs_node(nd), Box::new(abs_tree(c2))));
    assert(rnode_ok(nd, size));
    lemma_update_r_shape(c, s, n, progress);
    assert(rtree_inv(MltlParseTree::Not(nd, Box::new(c2)), size, n + 1));
    if nodes_ready(at, n + 1) {
        assert(rtree_inv(MltlParseTree::Not(nd, Box::new(c2)), size, n + 2));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub proof fn lemma_sim_and<A>(t: RTree<A>, size: nat, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        t is And,
        rtree_inv(t, size, n + 1),
        hist_pre(abs_tree(t), pi, n, progress),
        sim_ok(*t->And_1, child_slots(operands_wpd(*t->And_1, *t->And_2),
            mltl_parse_tree_to_mltl_spec(*t->And_1)), pi[n as int], n, progress),
        sim_ok(*t->And_2, child_slots(operands_wpd(*t->And_1, *t->And_2),
            mltl_parse_tree_to_mltl_spec(*t->And_2)), pi[n as int], n, progress),
    ensures
        sim_ok(t, size, pi[n as int], n, progress),
{
    let s = pi[n as int];
    let d = t->And_0;
    let (l, r) = (*t->And_1, *t->And_2);
    let w = operands_wpd(l, r);
    let (fl, fr) = (mltl_parse_tree_to_mltl_spec(l), mltl_parse_tree_to_mltl_spec(r));
    let (wl, wr) = (child_slack(w, fl), child_slack(w, fr));
    lemma_abs_shape(t);
    lemma_abs_shape(l);
    lemma_abs_shape(r);
    let at = abs_tree(t);
    child_updated_inv(at, pi, n, progress);
    lemma_update_root(at, s, n, progress);
    assert(rtree_inv(l, wl + 1, n + 1) && rtree_inv(r, wr + 1, n + 1));
    assert(rnode_ok(get_aux_data(l), wl + 1) && rnode_ok(get_aux_data(r), wr + 1));
    lemma_hist_pre_children(t, pi, n, progress);
    lemma_child_facts(l, pi, n, progress, wl + 1);
    lemma_child_facts(r, pi, n, progress, wr + 1);
    let (l2, r2) = (mltl_update_r(l, s, n, progress).0, mltl_update_r(r, s, n, progress).0);
    let l2h = mltl_update(abs_tree(l), s, n, progress).0;
    let r2h = mltl_update(abs_tree(r), s, n, progress).0;
    lemma_and_step(rscq(d), get_scq_from_tree(l2h), get_scq_from_tree(r2h), mltl_parse_tree_to_mltl_spec(l),
        mltl_parse_tree_to_mltl_spec(r), pi, n + 1, progress);
    let (q, p) = and_op(rscq(d), get_scq_from_tree(l2h), get_scq_from_tree(r2h), progress);
    lemma_cap_slack(n + 1, w, bpd(fl));
    lemma_cap_slack(n + 1, w, bpd(fr));
    lemma_cap_slack(n + 2, w, bpd(fl));
    lemma_cap_slack(n + 2, w, bpd(fr));
    lemma_child_read(l, l2, d.rd_left, d.next_time, q.next_time, wl, nat_sub(n + 1, bpd(fl)), nat_sub(n + 2, bpd(fl)));
    lemma_child_read(r, r2, d.rd_right, d.next_time, q.next_time, wr, nat_sub(n + 1, bpd(fr)), nat_sub(n + 2, bpd(fr)));
    lemma_store_ok(d, q, size);
    let (lp, rp) = (mltl_update_r(l, s, n, progress).1, mltl_update_r(r, s, n, progress).1);
    let (ld, lrd) = ring_read(get_ring(l2), d.rd_left, d.next_time);
    let (rdata, rrd) = ring_read(get_ring(r2), d.rd_right, d.next_time);
    assert(ld == scq_read(rscq(d), get_scq_from_tree(l2h)));
    assert(rdata == scq_read(rscq(d), get_scq_from_tree(r2h)));
    assert(and_core(rscq(d), ld, rdata, progress) == (q, p));
    let nd = RNode { rd_left: lrd, rd_right: rrd, ..store(d, q) };
    assert(mltl_update_r(t, s, n, progress)
        == (MltlParseTree::And(nd, Box::new(l2), Box::new(r2)), propagate_progress(seq![lp, rp, p])));
    assert(abs_node(nd) == with_scq(abs_node(d), q));
    assert(abs_node(d).scq == rscq(d));
    assert(mltl_update(at, s, n, progress) == (MltlParseTree::And(with_scq(abs_node(d), q), Box::new(l2h), Box::new(r2h)),
        propagate_progress(seq![mltl_update(abs_tree(l), s, n, progress).1, mltl_update(abs_tree(r), s, n, progress).1, p])));
    assert(rnode_ok(nd, size));
    lemma_update_r_shape(l, s, n, progress);
    lemma_update_r_shape(r, s, n, progress);
    assert(rtree_inv(MltlParseTree::And(nd, Box::new(l2), Box::new(r2)), size, n + 1));
    if nodes_ready(at, n + 1) {
        assert(rtree_inv(MltlParseTree::And(nd, Box::new(l2), Box::new(r2)), size, n + 2));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub proof fn lemma_sim_until<A>(t: RTree<A>, size: nat, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        t is Until,
        rtree_inv(t, size, n + 1),
        hist_pre(abs_tree(t), pi, n, progress),
        sim_ok(*t->Until_1, child_slots(operands_wpd(*t->Until_1, *t->Until_4),
            mltl_parse_tree_to_mltl_spec(*t->Until_1)), pi[n as int], n, progress),
        sim_ok(*t->Until_4, child_slots(operands_wpd(*t->Until_1, *t->Until_4),
            mltl_parse_tree_to_mltl_spec(*t->Until_4)), pi[n as int], n, progress),
    ensures
        sim_ok(t, size, pi[n as int], n, progress),
{
    let s = pi[n as int];
    let d = t->Until_0;
    let (l, r) = (*t->Until_1, *t->Until_4);
    let w = operands_wpd(l, r);
    let (fl, fr) = (mltl_parse_tree_to_mltl_spec(l), mltl_parse_tree_to_mltl_spec(r));
    let (wl, wr) = (child_slack(w, fl), child_slack(w, fr));
    lemma_abs_shape(t);
    lemma_abs_shape(l);
    lemma_abs_shape(r);
    let at = abs_tree(t);
    child_updated_inv(at, pi, n, progress);
    lemma_update_root(at, s, n, progress);
    assert(rtree_inv(l, wl + 1, n + 1) && rtree_inv(r, wr + 1, n + 1));
    assert(rnode_ok(get_aux_data(l), wl + 1) && rnode_ok(get_aux_data(r), wr + 1));
    lemma_hist_pre_children(t, pi, n, progress);
    lemma_child_facts(l, pi, n, progress, wl + 1);
    lemma_child_facts(r, pi, n, progress, wr + 1);
    let (l2, r2) = (mltl_update_r(l, s, n, progress).0, mltl_update_r(r, s, n, progress).0);
    let l2h = mltl_update(abs_tree(l), s, n, progress).0;
    let r2h = mltl_update(abs_tree(r), s, n, progress).0;
    let (q, o, p) = until_op(rscq(d), get_scq_from_tree(l2h), get_scq_from_tree(r2h), d.obs, progress);
    lemma_until_next_time_mono(rscq(d), get_scq_from_tree(l2h), get_scq_from_tree(r2h), d.obs, progress);
    lemma_cap_slack(n + 1, w, bpd(fl));
    lemma_cap_slack(n + 1, w, bpd(fr));
    lemma_cap_slack(n + 2, w, bpd(fl));
    lemma_cap_slack(n + 2, w, bpd(fr));
    lemma_child_read(l, l2, d.rd_left, d.next_time, q.next_time, wl, nat_sub(n + 1, bpd(fl)), nat_sub(n + 2, bpd(fl)));
    lemma_child_read(r, r2, d.rd_right, d.next_time, q.next_time, wr, nat_sub(n + 1, bpd(fr)), nat_sub(n + 2, bpd(fr)));
    lemma_store_ok(d, q, size);
    let (a, ub) = (t->Until_2, t->Until_3);
    let (lp, rp) = (mltl_update_r(l, s, n, progress).1, mltl_update_r(r, s, n, progress).1);
    let (ld, lrd) = ring_read(get_ring(l2), d.rd_left, d.next_time);
    let (rdata, rrd) = ring_read(get_ring(r2), d.rd_right, d.next_time);
    assert(ld == scq_read(rscq(d), get_scq_from_tree(l2h)));
    assert(rdata == scq_read(rscq(d), get_scq_from_tree(r2h)));
    assert(until_core(rscq(d), ld, rdata, d.obs, progress) == (q, o, p));
    let nd = RNode { rd_left: lrd, rd_right: rrd, obs: o, ..store(d, q) };
    assert(mltl_update_r(t, s, n, progress)
        == (MltlParseTree::Until(nd, Box::new(l2), a, ub, Box::new(r2)), propagate_progress(seq![lp, rp, p])));
    assert(abs_node(nd) == NodeData { scq: q, obs: o });
    assert(abs_node(d).scq == rscq(d) && abs_node(d).obs == d.obs);
    assert(mltl_update(at, s, n, progress) == (MltlParseTree::Until(NodeData { scq: q, obs: o }, Box::new(l2h), a, ub,
        Box::new(r2h)), propagate_progress(seq![mltl_update(abs_tree(l), s, n, progress).1,
        mltl_update(abs_tree(r), s, n, progress).1, p])));
    assert(rnode_ok(nd, size));
    lemma_update_r_shape(l, s, n, progress);
    lemma_update_r_shape(r, s, n, progress);
    assert(rtree_inv(MltlParseTree::Until(nd, Box::new(l2), a, ub, Box::new(r2)), size, n + 1));
    if nodes_ready(at, n + 1) {
        assert(rtree_inv(MltlParseTree::Until(nd, Box::new(l2), a, ub, Box::new(r2)), size, n + 2));
    }
}

/// One pass of the ring monitor equals one pass of the history monitor
/// (after abstraction), reports the same progress, and keeps the invariant.
pub proof fn lemma_sim_update<A>(t: RTree<A>, size: nat, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        rtree_inv(t, size, n + 1),
        hist_pre(abs_tree(t), pi, n, progress),
    ensures
        sim_ok(t, size, pi[n as int], n, progress),
    decreases t,
{
    lemma_hist_pre_children(t, pi, n, progress);
    match t {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) =>
            lemma_sim_leaf(t, size, pi, n, progress),
        MltlParseTree::Not(_, c) => {
            lemma_sim_update(*c, 1, pi, n, progress);
            lemma_sim_not(t, size, pi, n, progress);
        },
        MltlParseTree::And(_, l, r) => {
            lemma_sim_update(*l, child_slots(operands_wpd(*l, *r), mltl_parse_tree_to_mltl_spec(*l)), pi, n, progress);
            lemma_sim_update(*r, child_slots(operands_wpd(*l, *r), mltl_parse_tree_to_mltl_spec(*r)), pi, n, progress);
            lemma_sim_and(t, size, pi, n, progress);
        },
        MltlParseTree::Until(_, l, _, _, r) => {
            lemma_sim_update(*l, child_slots(operands_wpd(*l, *r), mltl_parse_tree_to_mltl_spec(*l)), pi, n, progress);
            lemma_sim_update(*r, child_slots(operands_wpd(*l, *r), mltl_parse_tree_to_mltl_spec(*r)), pi, n, progress);
            lemma_sim_until(t, size, pi, n, progress);
        },
        _ => {
            assert(!hist_pre(abs_tree(t), pi, n, progress)) by { lemma_abs_shape(t); }
        },
    }
}

// ---------------------------------------------------------------------------
// Time steps, runs, and the main theorems
// ---------------------------------------------------------------------------

pub proof fn lemma_sim_repeat<A>(t: RTree<A>, size: nat, pi: Seq<Set<A>>, n: nat, fuel: nat)
    requires
        rtree_inv(t, size, n + 1),
        hist_pre(abs_tree(t), pi, n, LoopProgress::ReloopNoProgress),
        untils_ready(abs_tree(t), n),
        until_c(abs_tree(t), n + 1),
        fuel > tree_measure(abs_tree(t), n + 1),
    ensures
        abs_tree(repeat_mltl_update_r(t, pi[n as int], n, fuel)) == repeat_mltl_update(abs_tree(t), pi[n as int], n, fuel),
        rtree_inv(repeat_mltl_update_r(t, pi[n as int], n, fuel), size, n + 2),
        cov_ub(abs_tree(repeat_mltl_update_r(t, pi[n as int], n, fuel)), n + 1),
        not_caught(abs_tree(repeat_mltl_update_r(t, pi[n as int], n, fuel))),
    decreases fuel,
{
    let no = LoopProgress::ReloopNoProgress;
    let at = abs_tree(t);
    lemma_sim_update(t, size, pi, n, no);
    lemma_update_reloop(at, pi, n);
    lemma_update_measure(at, pi, n);
    lemma_update_cov_ub(at, pi, n, no);
    lemma_update_not_caught(at, pi, n, no);
    let (t2, p) = mltl_update_r(t, pi[n as int], n, no);
    if p == no {
        lemma_last_ready(at, pi, n);
    } else {
        lemma_update_nodes_ready(at, pi, n, no, n);
        lemma_update_prompt(at, pi, n, no, n);
        lemma_update_ready(at, pi, n, n + 1, no, n);
        lemma_update_c(at, pi, n, no);
        lemma_sim_repeat(t2, size, pi, n, (fuel - 1) as nat);
    }
}

pub proof fn lemma_sim_step<A>(t: RTree<A>, size: nat, pi: Seq<Set<A>>, n: nat)
    requires
        rtree_inv(t, size, n + 1),
        hist_pre(abs_tree(t), pi, n, LoopProgress::FirstLoop),
        untils_ready(abs_tree(t), n),
    ensures
        abs_tree(r2u2_engine_step_r(t, pi[n as int], n)) == r2u2_engine_step(abs_tree(t), pi[n as int], n),
        rtree_inv(r2u2_engine_step_r(t, pi[n as int], n), size, n + 2),
        cov_ub(abs_tree(r2u2_engine_step_r(t, pi[n as int], n)), n + 1),
        not_caught(abs_tree(r2u2_engine_step_r(t, pi[n as int], n))),
{
    let first = LoopProgress::FirstLoop;
    let at = abs_tree(t);
    lemma_sim_update(t, size, pi, n, first);
    lemma_update_first(at, pi, n);
    lemma_update_nodes_ready(at, pi, n, first, n);
    lemma_update_prompt(at, pi, n, first, n);
    lemma_update_ready(at, pi, n, n, first, n);
    lemma_update_c(at, pi, n, first);
    lemma_update_cov_ub(at, pi, n, first);
    lemma_update_not_caught(at, pi, n, first);
    lemma_update_size(at, pi[n as int], n, first);
    lemma_abs_shape(t);
    let t1 = mltl_update_r(t, pi[n as int], n, first).0;
    let at1 = mltl_update(at, pi[n as int], n, first).0;
    lemma_tree_measure_bound(at1, n + 1);
    let sz = size_parse_tree(t);
    assert(2 * (n + 1) * sz == 2 * sz * (n + 1)) by (nonlinear_arith);
    lemma_sim_repeat(t1, size, pi, n, 2 * size_parse_tree(t) * (n + 1) + 1);
}

pub proof fn lemma_sim_run<A>(t: RTree<A>, size: nat, pi: Seq<Set<A>>, k: nat)
    requires
        rtree_inv(t, size, 1),
        tree_inv(abs_tree(t), pi, 0),
        untils_ready(abs_tree(t), 0),
        nodes_ready(abs_tree(t), 0),
        cov_ub(abs_tree(t), 0),
        not_caught(abs_tree(t)),
        k <= pi.len(),
    ensures
        abs_tree(r2u2_run_r(t, pi, k)) == r2u2_run(abs_tree(t), pi, k),
        rtree_inv(r2u2_run_r(t, pi, k), size, k + 1),
        cov_ub(r2u2_run(abs_tree(t), pi, k), k),
        not_caught(r2u2_run(abs_tree(t), pi, k)),
    decreases k,
{
    if k > 0 {
        let n = (k - 1) as nat;
        lemma_sim_run(t, size, pi, n);
        let at = abs_tree(t);
        lemma_run(at, pi, n);
        lemma_run_prompt(at, pi, n);
        if n > 0 {
            lemma_prompt_nodes_ready(r2u2_run(at, pi, n), pi, n);
        } else {
            lemma_prompt_zero(at);
        }
        lemma_sim_step(r2u2_run_r(t, pi, n), size, pi, n);
    }
}

/// The initial ring tree: empty rings of the planned sizes, abstracting the
/// initial history tree.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub proof fn lemma_initial_ring<A>(f: Mltl<A>, size: nat)
    requires
        size >= 1,
        is_r2u2_form(f),
    ensures
        rtree_inv(parse_tree_with_ring(f, size), size, 1),
        abs_tree(parse_tree_with_ring(f, size)) == parse_tree_with_scq(f),
        mltl_parse_tree_to_mltl_spec(parse_tree_with_ring(f, size)) == f,
    decreases f,
{
    let t = parse_tree_with_ring(f, size);
    let d = get_aux_data(t);
    assert(compact(Seq::<Verdict>::empty()) == Seq::<Verdict>::empty());
    vstd::arithmetic::div_mod::lemma_small_mod(0, size);
    assert(rnode_ok(d, size));
    match f {
        Mltl::Not(phi) => lemma_initial_ring(*phi, 1),
        Mltl::And(phi, psi) | Mltl::Until(phi, _, _, psi) => {
            let w = operands_wpd_of(f);
            lemma_initial_ring(*phi, child_slots(w, *phi));
            lemma_initial_ring(*psi, child_slots(w, *psi));
        },
        _ => {},
    }
}

/// **The ring monitor equals the history monitor.** With [`child_slots`]
/// slots per child queue (1 for the child of a NOT and for the root,
/// `wpd(operands) − bpd(child) + 1` for a child of a binary node), monitoring
/// any `φ` (intervals `a ≤ b`) on any trace gives the same verdicts.
pub proof fn r2u2_ring_eq<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        r2u2_ring(phi, pi) == r2u2(phi, pi),
{
    let c = convert_r2u2_form(phi);
    convert_r2u2_form_is_r2u2_form(phi);
    convert_r2u2_form_welldef_intervals(phi);
    lemma_initial_ring(c, 1);
    lemma_initial_tree(c, pi);
    lemma_initial_ready(c);
    lemma_initial_nodes_ready(c);
    lemma_initial_tight(c);
    let rt = parse_tree_with_ring(c, 1);
    lemma_sim_run(rt, 1, pi, pi.len());
    lemma_abs_shape(r2u2_run_r(rt, pi, pi.len()));
}

/// Soundness and promptness of the ring monitor.
pub proof fn r2u2_ring_correct<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        forall|j: nat| j < next_after(r2u2_ring(phi, pi)) ==>
            #[trigger] value_at(r2u2_ring(phi, pi), j) == Some(semantics_mltl(drop(pi, j), phi)),
        next_after(r2u2_ring(phi, pi)) >= nat_sub(pi.len(), wpd(phi)),
{
    r2u2_ring_eq(phi, pi);
    r2u2_sound(phi, pi);
    r2u2_prompt(phi, pi);
}

} // verus!
