//! Facts behind the tighter queue sizes (`1 + max(wpd c, wpd s) − bpd c` for
//! a child of AND/UNTIL, 1 for a child of NOT):
//! - a node never covers more than `b − bpd(φ_node)` steps when `b` steps
//!   were read ([`cov_ub`]): every verdict an operator writes is at least
//!   its lower bound behind what it read;
//! - a NOT node has read everything its child wrote after every pass
//!   ([`not_caught`]): NOT reads after its child's at most one new entry.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use crate::verdict::*;
use crate::scq::*;
use crate::operators::*;
use crate::engine::*;
use crate::soundness::*;
use crate::queue_size::*;
use crate::ring_sim::*;

verus! {

pub proof fn lemma_bpd_le_wpd<A>(f: Mltl<A>)
    requires
        mltl_core::properties::intervals_welldef(f),
    ensures
        bpd(f) <= wpd(f),
    decreases f,
{
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => lemma_bpd_le_wpd(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            lemma_bpd_le_wpd(*phi);
            lemma_bpd_le_wpd(*psi);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// A node never runs ahead
// ---------------------------------------------------------------------------

/// Every node has covered at most `b − bpd` of its subformula.
pub open spec fn cov_ub<A>(t: Tree<A>, b: nat) -> bool
    decreases t,
{
    &&& next_after(get_execution_sequence(t)) <= nat_sub(b, bpd(mltl_parse_tree_to_mltl_spec(t)))
    &&& match t {
        MltlParseTree::Not(_, c) => cov_ub(*c, b),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => cov_ub(*l, b) && cov_ub(*r, b),
        _ => true,
    }
}

pub proof fn lemma_cov_ub_mono<A>(t: Tree<A>, b: nat, b2: nat)
    requires
        cov_ub(t, b),
        b <= b2,
    ensures
        cov_ub(t, b2),
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => lemma_cov_ub_mono(*c, b, b2),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => {
            lemma_cov_ub_mono(*l, b, b2);
            lemma_cov_ub_mono(*r, b, b2);
        },
        _ => {},
    }
}

/// What a read returns lies before what the child has covered.
proof fn lemma_read_lt(parent: Scq, child: Scq)
    requires
        strictly_increasing(child.all_values),
    ensures
        scq_read(parent, child).is_some() ==> scq_read(parent, child).unwrap().time < next_after(child.all_values),
        scq_read(parent, child).is_some() ==> scq_read(parent, child).unwrap().time >= parent.next_time,
{
    if scq_read(parent, child).is_some() {
        lemma_scq_read_sound(parent, child);
    }
}

pub proof fn lemma_not_write_ub(parent: Scq, child: Scq, progress: LoopProgress)
    requires
        strictly_increasing(child.all_values),
    ensures
        ({
            let q = not_op(parent, child, progress).0;
            q.all_values == parent.all_values || (q.all_values.len() > 0 && q.all_values.last().time < next_after(child.all_values)
                && q.all_values == parent.all_values.push(q.all_values.last()))
        }),
{
    lemma_read_lt(parent, child);
}

pub proof fn lemma_and_write_ub(parent: Scq, left: Scq, right: Scq, progress: LoopProgress)
    requires
        strictly_increasing(left.all_values),
        strictly_increasing(right.all_values),
    ensures
        ({
            let q = and_op(parent, left, right, progress).0;
            q.all_values == parent.all_values || (q.all_values.len() > 0
                && (q.all_values.last().time < next_after(left.all_values) || q.all_values.last().time < next_after(right.all_values))
                && q.all_values == parent.all_values.push(q.all_values.last()))
        }),
{
    lemma_read_lt(parent, left);
    lemma_read_lt(parent, right);
}

pub proof fn lemma_until_write_ub(parent: Scq, left: Scq, right: Scq, obs: crate::observer::Observer, progress: LoopProgress)
    requires
        strictly_increasing(left.all_values),
        strictly_increasing(right.all_values),
        parent.next_time >= obs.lower_bound,
        obs.lower_bound <= obs.upper_bound,
    ensures
        ({
            let q = until_op(parent, left, right, obs, progress).0;
            q.all_values == parent.all_values || (q.all_values.len() > 0
                && q.all_values.last().time + obs.lower_bound < next_after(right.all_values)
                && q.all_values == parent.all_values.push(q.all_values.last()))
        }),
{
    lemma_read_lt(parent, left);
    lemma_read_lt(parent, right);
}

/// The precondition of a pass at step `n`, for `cov_ub`.
pub open spec fn cov_pre<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress) -> bool {
    &&& (progress == LoopProgress::FirstLoop && tree_inv(t, pi, n) && cov_ub(t, n))
        || (progress == LoopProgress::ReloopNoProgress && tree_inv(t, pi, n + 1) && cov_ub(t, n + 1))
    &&& n < pi.len()
}

/// The root's part: its new verdict (if any) is behind its children by its `bpd`.
#[verifier::spinoff_prover]
proof fn lemma_cov_ub_root<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        cov_pre(t, pi, n, progress),
        t is Not ==> cov_ub(mltl_update(*t->Not_1, pi[n as int], n, progress).0, n + 1),
        t is And ==> cov_ub(mltl_update(*t->And_1, pi[n as int], n, progress).0, n + 1)
            && cov_ub(mltl_update(*t->And_2, pi[n as int], n, progress).0, n + 1),
        t is Until ==> cov_ub(mltl_update(*t->Until_1, pi[n as int], n, progress).0, n + 1)
            && cov_ub(mltl_update(*t->Until_4, pi[n as int], n, progress).0, n + 1),
    ensures
        next_after(get_execution_sequence(mltl_update(t, pi[n as int], n, progress).0))
            <= nat_sub(n + 1, bpd(mltl_parse_tree_to_mltl_spec(t))),
{
    let s = pi[n as int];
    if progress == LoopProgress::FirstLoop {
        lemma_cov_ub_mono(t, n, n + 1);
    }
    child_updated_inv(t, pi, n, progress);
    match t {
        MltlParseTree::Not(d, c) => {
            child_updated_inv(*c, pi, n, progress);
            lemma_update_shape(*c, s, n, progress);
            let c2 = mltl_update(*c, s, n, progress).0;
            lemma_not_write_ub(d.scq, get_scq_from_tree(c2), progress);
        },
        MltlParseTree::And(d, l, r) => {
            child_updated_inv(*l, pi, n, progress);
            child_updated_inv(*r, pi, n, progress);
            lemma_update_shape(*l, s, n, progress);
            lemma_update_shape(*r, s, n, progress);
            let l2 = mltl_update(*l, s, n, progress).0;
            let r2 = mltl_update(*r, s, n, progress).0;
            lemma_and_write_ub(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), progress);
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            child_updated_inv(*l, pi, n, progress);
            child_updated_inv(*r, pi, n, progress);
            lemma_update_shape(*l, s, n, progress);
            lemma_update_shape(*r, s, n, progress);
            let l2 = mltl_update(*l, s, n, progress).0;
            let r2 = mltl_update(*r, s, n, progress).0;
            lemma_until_write_ub(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, progress);
        },
        _ => {},
    }
}

/// Passes keep `cov_ub` (at `n + 1` steps read).
pub proof fn lemma_update_cov_ub<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        cov_pre(t, pi, n, progress),
    ensures
        cov_ub(mltl_update(t, pi[n as int], n, progress).0, n + 1),
    decreases t,
{
    let s = pi[n as int];
    lemma_update_shape(t, s, n, progress);
    match t {
        MltlParseTree::Not(_, c) => lemma_update_cov_ub(*c, pi, n, progress),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => {
            lemma_update_cov_ub(*l, pi, n, progress);
            lemma_update_cov_ub(*r, pi, n, progress);
        },
        _ => {},
    }
    lemma_cov_ub_root(t, pi, n, progress);
}

// ---------------------------------------------------------------------------
// NOT keeps up with its child
// ---------------------------------------------------------------------------

/// Every NOT node has read up to what its child covers.
pub open spec fn not_caught<A>(t: Tree<A>) -> bool
    decreases t,
{
    match t {
        MltlParseTree::Not(d, c) => d.scq.next_time >= next_after(get_execution_sequence(*c)) && not_caught(*c),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => not_caught(*l) && not_caught(*r),
        _ => true,
    }
}

/// NOT, caught up before its child wrote at most once, is caught up after.
pub proof fn lemma_not_catch_up(parent: Scq, h: Seq<Verdict>, child2: Scq, progress: LoopProgress)
    requires
        strictly_increasing(child2.all_values),
        child2.all_values == h || child2.all_values == h.push(child2.all_values.last()),
        parent.next_time >= next_after(h),
    ensures
        not_op(parent, child2, progress).0.next_time >= next_after(child2.all_values),
{
    let h2 = child2.all_values;
    let tau = parent.next_time;
    lemma_scq_read_some(parent, child2);
    if h2 != h && scq_read(parent, child2).is_some() {
        let v = h2.last();
        assert(h2.drop_last() =~= h);
        assert(strictly_increasing(h)) by {
            assert forall|i: int, k: int| #![trigger h[i], h[k]] 0 <= i < k < h.len() implies h[i].time < h[k].time by {
                assert(h[i] == h2[i] && h[k] == h2[k]);
            }
        }
        lemma_compact(h);
        lemma_compact(h2);
        let c = compact(h);
        let c2 = compact(h2);
        // every stored entry before the last is before tau
        if c.len() > 0 {
            assert(c.last().time < next_after(h));
            assert forall|i: int| 0 <= i < c.len() implies #[trigger] c[i].time < tau by {
                if i < c.len() - 1 { assert(c[i].time < c[c.len() - 1].time); }
            }
        }
        if c.len() > 0 && c.last().val == v.val {
            assert(c2 == c.update(c.len() - 1, v));
            lemma_first_idx_update_last(c, v, tau);
        } else {
            assert(c2 == c.push(v));
            lemma_first_idx_push(c, v, tau);
        }
        lemma_first_idx(c, tau);
        if c.len() > 0 {
            lemma_first_idx_unique(c, tau, c.len());
        } else {
            lemma_first_idx_unique(c, tau, 0);
        }
    }
}

/// Passes keep `not_caught`.
pub proof fn lemma_update_not_caught<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        (progress == LoopProgress::FirstLoop && tree_inv(t, pi, n))
            || (progress == LoopProgress::ReloopNoProgress && tree_inv(t, pi, n + 1)),
        not_caught(t),
        n < pi.len(),
    ensures
        not_caught(mltl_update(t, pi[n as int], n, progress).0),
    decreases t,
{
    let s = pi[n as int];
    match t {
        MltlParseTree::Not(d, c) => {
            lemma_update_not_caught(*c, pi, n, progress);
            child_updated_inv(*c, pi, n, progress);
            lemma_update_root(*c, s, n, progress);
            let c2 = mltl_update(*c, s, n, progress).0;
            lemma_not_catch_up(d.scq, get_execution_sequence(*c), get_scq_from_tree(c2), progress);
        },
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => {
            lemma_update_not_caught(*l, pi, n, progress);
            lemma_update_not_caught(*r, pi, n, progress);
        },
        _ => {},
    }
}

pub proof fn lemma_initial_tight<A>(f: Mltl<A>)
    ensures
        cov_ub(parse_tree_with_scq(f), 0),
        not_caught(parse_tree_with_scq(f)),
    decreases f,
{
    lemma_initial_shape(f);
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => lemma_initial_tight(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            lemma_initial_tight(*phi);
            lemma_initial_tight(*psi);
        },
        _ => {},
    }
}

pub proof fn lemma_initial_shape<A>(f: Mltl<A>)
    ensures
        mltl_parse_tree_to_mltl_spec(parse_tree_with_scq(f)) == f,
        get_execution_sequence(parse_tree_with_scq(f)) == Seq::<Verdict>::empty(),
    decreases f,
{
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => lemma_initial_shape(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            lemma_initial_shape(*phi);
            lemma_initial_shape(*psi);
        },
        _ => {},
    }
}

} // verus!
