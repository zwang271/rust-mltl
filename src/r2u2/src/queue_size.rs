//! Queue sizes, at the history level: in every pass of every time step,
//! when a node reads a child, the child's stored (compacted) entries at or
//! after the reader's `next_time` are at most `wpd(operands) + 1`
//! ([`r2u2_queue_sizes`]). Those are the entries a ring buffer must still
//! hold for the read to see what the unbounded queue would show; so a ring
//! of [`child_queue_size`] slots per child is enough (the ring layer will
//! use this).
//!
//! Why: the entries have distinct time steps, all in `[next_time, n + 1)`
//! ([`lemma_backlog_bound`]), and the reader is at most `wpd(operands)`
//! steps behind (promptness: [`nodes_ready`]).
//!
//! Isabelle sizes a child's queue `max(wpd ψ − bpd φ, 0) + 1`
//! (`queue_size_sibling_nodes`) without proof; for the counterexample in
//! `R2U2_Bugs.thy` that gives 1 slot where 2 are needed.
//!
//! This bound is uniform over a node's children. `tight.rs` sharpens it per
//! child (a child `c` cannot have covered more than `(n + 1) − bpd(c)`, and a
//! NOT always reads everything its child wrote); `half.rs` halves the part a
//! slower child adds over its sibling. The ring layer uses both
//! (`ring_engine.rs : child_slots`).
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
use crate::observer::*;

verus! {

// ---------------------------------------------------------------------------
// Backlog of a queue
// ---------------------------------------------------------------------------

/// Stored entries of `child` at or after time `tau`: what a reader whose
/// `next_time` is `tau` may still read.
pub open spec fn backlog(child: Scq, tau: nat) -> nat {
    (scq_entries(child).len() - first_idx(scq_entries(child), tau)) as nat
}

/// Strictly increasing timestamps grow by at least one per entry.
pub proof fn lemma_time_gap(c: Seq<Verdict>, i: int, j: int)
    requires
        strictly_increasing(c),
        0 <= i <= j < c.len(),
    ensures
        c[j].time >= c[i].time + (j - i),
    decreases j - i,
{
    if i < j {
        lemma_time_gap(c, i, j - 1);
        assert(c[j - 1].time < c[j].time);
    }
}

/// The backlog is at most the number of time steps from `tau` to what the
/// child has covered.
pub proof fn lemma_backlog_bound(child: Scq, tau: nat)
    requires
        strictly_increasing(child.all_values),
    ensures
        backlog(child, tau) <= nat_sub(next_after(child.all_values), tau),
{
    let c = scq_entries(child);
    lemma_compact(child.all_values);
    lemma_first_idx(c, tau);
    let k = first_idx(c, tau);
    if k < c.len() {
        lemma_time_gap(c, k as int, c.len() - 1);
    }
}

// ---------------------------------------------------------------------------
// Readers are at most wpd(operands) behind
// ---------------------------------------------------------------------------

/// The `wpd` of a node's operands (its largest, for two operands).
pub open spec fn node_operands_wpd<A>(t: Tree<A>) -> nat {
    match t {
        MltlParseTree::Not(_, c) => wpd(mltl_parse_tree_to_mltl_spec(*c)),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => operands_wpd(*l, *r),
        _ => 0,
    }
}

/// Size of each child queue of node `t`.
pub open spec fn child_queue_size<A>(t: Tree<A>) -> nat {
    node_operands_wpd(t) + 1
}

/// Every reading node's `next_time` is at least `k − wpd(operands)`.
pub open spec fn nodes_ready<A>(t: Tree<A>, k: nat) -> bool
    decreases t,
{
    match t {
        MltlParseTree::Not(d, c) => d.scq.next_time >= nat_sub(k, node_operands_wpd(t)) && nodes_ready(*c, k),
        MltlParseTree::And(d, l, r) =>
            d.scq.next_time >= nat_sub(k, node_operands_wpd(t)) && nodes_ready(*l, k) && nodes_ready(*r, k),
        MltlParseTree::Until(d, l, _, _, r) =>
            d.scq.next_time >= nat_sub(k, node_operands_wpd(t)) && nodes_ready(*l, k) && nodes_ready(*r, k),
        _ => true,
    }
}

pub proof fn lemma_initial_nodes_ready<A>(f: Mltl<A>)
    ensures
        nodes_ready(parse_tree_with_scq(f), 0),
    decreases f,
{
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => lemma_initial_nodes_ready(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            lemma_initial_nodes_ready(*phi);
            lemma_initial_nodes_ready(*psi);
        },
        _ => {},
    }
}

/// After a time step: NOT and AND nodes are ready by promptness (their
/// `next_time` is their written-up-to point), UNTIL nodes by `untils_ready`.
pub proof fn lemma_prompt_nodes_ready<A>(t: Tree<A>, pi: Seq<Set<A>>, b: nat)
    requires
        tree_inv(t, pi, b),
        tree_prompt(t, b),
        untils_ready(t, b),
    ensures
        nodes_ready(t, b),
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => lemma_prompt_nodes_ready(*c, pi, b),
        MltlParseTree::And(_, l, r) => {
            lemma_prompt_nodes_ready(*l, pi, b);
            lemma_prompt_nodes_ready(*r, pi, b);
        },
        MltlParseTree::Until(_, l, _, _, r) => {
            lemma_prompt_nodes_ready(*l, pi, b);
            lemma_prompt_nodes_ready(*r, pi, b);
        },
        _ => {},
    }
}

/// `next_time` never goes down, so passes keep `nodes_ready`.
pub proof fn lemma_update_nodes_ready<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress, k: nat)
    requires
        (progress == LoopProgress::FirstLoop && tree_inv(t, pi, n))
            || (progress == LoopProgress::ReloopNoProgress && tree_inv(t, pi, n + 1)),
        n < pi.len(),
        nodes_ready(t, k),
    ensures
        nodes_ready(mltl_update(t, pi[n as int], n, progress).0, k),
    decreases t,
{
    let s = pi[n as int];
    lemma_update_shape(t, s, n, progress);
    match t {
        MltlParseTree::Not(d, c) => {
            lemma_update_nodes_ready(*c, pi, n, progress, k);
            lemma_update_shape(*c, s, n, progress);
            child_updated_inv(*c, pi, n, progress);
            let c2 = mltl_update(*c, s, n, progress).0;
            lemma_not_step(d.scq, get_scq_from_tree(c2), mltl_parse_tree_to_mltl_spec(*c), pi, n + 1, progress);
        },
        MltlParseTree::And(d, l, r) => {
            lemma_update_nodes_ready(*l, pi, n, progress, k);
            lemma_update_nodes_ready(*r, pi, n, progress, k);
            lemma_update_shape(*l, s, n, progress);
            lemma_update_shape(*r, s, n, progress);
            child_updated_inv(*l, pi, n, progress);
            child_updated_inv(*r, pi, n, progress);
            let l2 = mltl_update(*l, s, n, progress).0;
            let r2 = mltl_update(*r, s, n, progress).0;
            lemma_and_step(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), mltl_parse_tree_to_mltl_spec(*l),
                mltl_parse_tree_to_mltl_spec(*r), pi, n + 1, progress);
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            lemma_update_nodes_ready(*l, pi, n, progress, k);
            lemma_update_nodes_ready(*r, pi, n, progress, k);
            lemma_update_shape(*l, s, n, progress);
            lemma_update_shape(*r, s, n, progress);
            let l2 = mltl_update(*l, s, n, progress).0;
            let r2 = mltl_update(*r, s, n, progress).0;
            lemma_until_next_time_mono(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, progress);
        },
        _ => {},
    }
}

/// A child after its update in the pass satisfies the invariant for the
/// steps read so far (`n + 1`).
pub proof fn child_updated_inv<A>(c: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        (progress == LoopProgress::FirstLoop && tree_inv(c, pi, n))
            || (progress == LoopProgress::ReloopNoProgress && tree_inv(c, pi, n + 1)),
        n < pi.len(),
    ensures
        tree_inv(mltl_update(c, pi[n as int], n, progress).0, pi, n + 1),
{
    if progress == LoopProgress::FirstLoop {
        lemma_update_first(c, pi, n);
    } else {
        lemma_update_reloop(c, pi, n);
    }
}

// ---------------------------------------------------------------------------
// Every read fits
// ---------------------------------------------------------------------------

/// In this pass, every read finds at most `child_queue_size` stored entries
/// at or after the reader's `next_time` (children are read after their own
/// update, as in `mltl_update`).
pub open spec fn reads_fit<A>(t: Tree<A>, s: Set<A>, n: nat, progress: LoopProgress) -> bool
    decreases t,
{
    match t {
        MltlParseTree::Not(d, c) =>
            backlog(get_scq_from_tree(mltl_update(*c, s, n, progress).0), d.scq.next_time) <= child_queue_size(t)
            && reads_fit(*c, s, n, progress),
        MltlParseTree::And(d, l, r) | MltlParseTree::Until(d, l, _, _, r) =>
            backlog(get_scq_from_tree(mltl_update(*l, s, n, progress).0), d.scq.next_time) <= child_queue_size(t)
            && backlog(get_scq_from_tree(mltl_update(*r, s, n, progress).0), d.scq.next_time) <= child_queue_size(t)
            && reads_fit(*l, s, n, progress) && reads_fit(*r, s, n, progress),
        _ => true,
    }
}

pub proof fn lemma_child_backlog<A>(c: Tree<A>, tau: nat, w: nat, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        (progress == LoopProgress::FirstLoop && tree_inv(c, pi, n))
            || (progress == LoopProgress::ReloopNoProgress && tree_inv(c, pi, n + 1)),
        n < pi.len(),
        tau >= nat_sub(n, w),
    ensures
        backlog(get_scq_from_tree(mltl_update(c, pi[n as int], n, progress).0), tau) <= w + 1,
{
    child_updated_inv(c, pi, n, progress);
    let c2 = mltl_update(c, pi[n as int], n, progress).0;
    lemma_backlog_bound(get_scq_from_tree(c2), tau);
}

/// The queue-size theorem for one pass of time step `n`.
pub proof fn lemma_reads_fit<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        (progress == LoopProgress::FirstLoop && tree_inv(t, pi, n))
            || (progress == LoopProgress::ReloopNoProgress && tree_inv(t, pi, n + 1)),
        n < pi.len(),
        nodes_ready(t, n),
    ensures
        reads_fit(t, pi[n as int], n, progress),
    decreases t,
{
    match t {
        MltlParseTree::Not(d, c) => {
            lemma_child_backlog(*c, d.scq.next_time, node_operands_wpd(t), pi, n, progress);
            lemma_reads_fit(*c, pi, n, progress);
        },
        MltlParseTree::And(d, l, r) | MltlParseTree::Until(d, l, _, _, r) => {
            lemma_child_backlog(*l, d.scq.next_time, node_operands_wpd(t), pi, n, progress);
            lemma_child_backlog(*r, d.scq.next_time, node_operands_wpd(t), pi, n, progress);
            lemma_reads_fit(*l, pi, n, progress);
            lemma_reads_fit(*r, pi, n, progress);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Every read of a whole run fits
// ---------------------------------------------------------------------------

/// The reloop passes of `repeat_mltl_update`, pass by pass.
pub open spec fn repeat_reads_fit<A>(t: Tree<A>, s: Set<A>, n: nat, fuel: nat) -> bool
    decreases fuel,
{
    fuel == 0 || (reads_fit(t, s, n, LoopProgress::ReloopNoProgress) && {
        let (t2, p) = mltl_update(t, s, n, LoopProgress::ReloopNoProgress);
        p == LoopProgress::ReloopNoProgress || repeat_reads_fit(t2, s, n, (fuel - 1) as nat)
    })
}

/// All passes of `r2u2_engine_step`.
pub open spec fn step_reads_fit<A>(t: Tree<A>, s: Set<A>, n: nat) -> bool {
    &&& reads_fit(t, s, n, LoopProgress::FirstLoop)
    &&& repeat_reads_fit(mltl_update(t, s, n, LoopProgress::FirstLoop).0, s, n, step_fuel(t, n))
}

/// All passes of the first `k` time steps of `r2u2_run`.
pub open spec fn run_reads_fit<A>(t: Tree<A>, pi: Seq<Set<A>>, k: nat) -> bool
    decreases k,
{
    k == 0 || (run_reads_fit(t, pi, (k - 1) as nat)
        && step_reads_fit(r2u2_run(t, pi, (k - 1) as nat), pi[k - 1], (k - 1) as nat))
}

pub proof fn lemma_repeat_reads_fit<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, fuel: nat)
    requires
        tree_inv(t, pi, n + 1),
        nodes_ready(t, n),
        n < pi.len(),
    ensures
        repeat_reads_fit(t, pi[n as int], n, fuel),
    decreases fuel,
{
    if fuel > 0 {
        let no = LoopProgress::ReloopNoProgress;
        lemma_reads_fit(t, pi, n, no);
        lemma_update_reloop(t, pi, n);
        lemma_update_nodes_ready(t, pi, n, no, n);
        let (t2, p) = mltl_update(t, pi[n as int], n, no);
        if p != no {
            lemma_repeat_reads_fit(t2, pi, n, (fuel - 1) as nat);
        }
    }
}

pub proof fn lemma_step_reads_fit<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n),
        nodes_ready(t, n),
        n < pi.len(),
    ensures
        step_reads_fit(t, pi[n as int], n),
{
    lemma_reads_fit(t, pi, n, LoopProgress::FirstLoop);
    lemma_update_first(t, pi, n);
    lemma_update_nodes_ready(t, pi, n, LoopProgress::FirstLoop, n);
    let t1 = mltl_update(t, pi[n as int], n, LoopProgress::FirstLoop).0;
    lemma_repeat_reads_fit(t1, pi, n, step_fuel(t, n));
}

pub proof fn lemma_run_reads_fit<A>(t: Tree<A>, pi: Seq<Set<A>>, k: nat)
    requires
        tree_inv(t, pi, 0),
        untils_ready(t, 0),
        nodes_ready(t, 0),
        k <= pi.len(),
    ensures
        run_reads_fit(t, pi, k),
    decreases k,
{
    if k > 0 {
        lemma_run_reads_fit(t, pi, (k - 1) as nat);
        let m = (k - 1) as nat;
        lemma_run(t, pi, m);
        if m > 0 {
            lemma_run_prompt(t, pi, m);
            lemma_prompt_nodes_ready(r2u2_run(t, pi, m), pi, m);
        }
        lemma_step_reads_fit(r2u2_run(t, pi, m), pi, m);
    }
}

/// **Queue-size theorem.** Monitoring `φ` (with `a ≤ b` intervals) on any
/// trace, every read of every pass finds at most `wpd(operands) + 1` stored
/// child entries that it may still need.
pub proof fn r2u2_queue_sizes<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        run_reads_fit(parse_tree_with_scq(convert_r2u2_form(phi)), pi, pi.len()),
{
    let c = convert_r2u2_form(phi);
    convert_r2u2_form_is_r2u2_form(phi);
    convert_r2u2_form_welldef_intervals(phi);
    lemma_initial_tree(c, pi);
    lemma_initial_ready(c);
    lemma_initial_nodes_ready(c);
    lemma_run_reads_fit(parse_tree_with_scq(c), pi, pi.len());
}

// ---------------------------------------------------------------------------
// The last pass of a step reads at the next step's level (for tight sizes)
// ---------------------------------------------------------------------------

/// After a pass of step `n` (`k = n + 1`): an UNTIL node that has data on
/// both sides at its `next_time` is already at `k − wpd(operands)`.
pub open spec fn until_c<A>(t: Tree<A>, k: nat) -> bool
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => until_c(*c, k),
        MltlParseTree::And(_, l, r) => until_c(*l, k) && until_c(*r, k),
        MltlParseTree::Until(d, l, _, _, r) =>
            ((d.scq.next_time < next_after(get_execution_sequence(*l))
                && d.scq.next_time < next_after(get_execution_sequence(*r)))
                ==> d.scq.next_time >= nat_sub(k, operands_wpd(*l, *r)))
            && until_c(*l, k) && until_c(*r, k),
        _ => true,
    }
}

/// With data on both sides, UNTIL moves `next_time` by at least one.
pub proof fn lemma_until_moves(parent: Scq, left: Scq, right: Scq, obs: Observer, progress: LoopProgress)
    requires
        scq_read(parent, left).is_some(),
        scq_read(parent, right).is_some(),
    ensures
        until_op(parent, left, right, obs, progress).0.next_time >= parent.next_time + 1,
{
    lemma_first_from_props(scq_entries(right), parent.next_time);
    lemma_first_from_props(scq_entries(left), parent.next_time);
}

/// If UNTIL moved `next_time` without writing, it had data on both sides.
pub proof fn lemma_until_skip_both(parent: Scq, left: Scq, right: Scq, obs: Observer, progress: LoopProgress)
    requires
        until_op(parent, left, right, obs, progress).0.all_values == parent.all_values,
        until_op(parent, left, right, obs, progress).0.next_time != parent.next_time,
    ensures
        scq_read(parent, left).is_some(),
        scq_read(parent, right).is_some(),
{
    let q = until_op(parent, left, right, obs, progress).0;
    match scq_read(parent, right) {
        None => {},
        Some(r) => {
            if r.val {
                assert(q.all_values.len() == parent.all_values.len() + 1);
            } else if scq_read(parent, left).is_none() {
                let elapsed_from = match obs.prev_verdict {
                    None => obs.upper_bound,
                    Some(prev) => prev.time + obs.upper_bound + 1,
                };
                if r.time >= elapsed_from {
                    assert(q.all_values.len() == parent.all_values.len() + 1);
                }
            }
        },
    }
}

pub proof fn lemma_update_c<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        (progress == LoopProgress::FirstLoop && tree_inv(t, pi, n))
            || (progress == LoopProgress::ReloopNoProgress && tree_inv(t, pi, n + 1)),
        untils_ready(t, n),
        n < pi.len(),
    ensures
        until_c(mltl_update(t, pi[n as int], n, progress).0, n + 1),
    decreases t,
{
    let s = pi[n as int];
    match t {
        MltlParseTree::Not(_, c) => lemma_update_c(*c, pi, n, progress),
        MltlParseTree::And(_, l, r) => {
            lemma_update_c(*l, pi, n, progress);
            lemma_update_c(*r, pi, n, progress);
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            lemma_update_c(*l, pi, n, progress);
            lemma_update_c(*r, pi, n, progress);
            lemma_update_c_until(t, pi, n, progress);
        },
        _ => {},
    }
}

#[verifier::spinoff_prover]
proof fn lemma_update_c_until<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        t is Until,
        (progress == LoopProgress::FirstLoop && tree_inv(t, pi, n))
            || (progress == LoopProgress::ReloopNoProgress && tree_inv(t, pi, n + 1)),
        untils_ready(t, n),
        n < pi.len(),
        until_c(mltl_update(*t->Until_1, pi[n as int], n, progress).0, n + 1),
        until_c(mltl_update(*t->Until_4, pi[n as int], n, progress).0, n + 1),
    ensures
        until_c(mltl_update(t, pi[n as int], n, progress).0, n + 1),
{
    let s = pi[n as int];
    match t {
        MltlParseTree::Until(d, l, a, ub, r) => {
            lemma_update_shape(*l, s, n, progress);
            lemma_update_shape(*r, s, n, progress);
            child_updated_inv(*l, pi, n, progress);
            child_updated_inv(*r, pi, n, progress);
            let l2 = mltl_update(*l, s, n, progress).0;
            let r2 = mltl_update(*r, s, n, progress).0;
            let (lq, rq) = (get_scq_from_tree(l2), get_scq_from_tree(r2));
            lemma_until_next_time_mono(d.scq, lq, rq, d.obs, progress);
            lemma_scq_read_some(d.scq, lq);
            lemma_scq_read_some(d.scq, rq);
            if scq_read(d.scq, lq).is_some() && scq_read(d.scq, rq).is_some() {
                lemma_until_moves(d.scq, lq, rq, d.obs, progress);
            }
        },
        _ => {},
    }
}

/// A reloop pass reporting no progress writes nothing at the root.
pub proof fn lemma_rlnp_root<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n + 1),
        n < pi.len(),
        mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
    ensures
        get_execution_sequence(mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).0) == get_execution_sequence(t),
{
    let no = LoopProgress::ReloopNoProgress;
    let s = pi[n as int];
    let b = n + 1;
    match t {
        MltlParseTree::Not(d, c) => {
            lemma_update_reloop(*c, pi, n);
            lemma_update_shape(*c, s, n, no);
            let (c2, cp) = mltl_update(*c, s, n, no);
            lemma_not_progress(d.scq, get_scq_from_tree(c2), mltl_parse_tree_to_mltl_spec(*c), pi, b);
            let (q, p) = not_op(d.scq, get_scq_from_tree(c2), no);
            lemma_propagate_progress_2(cp, p);
        },
        MltlParseTree::And(d, l, r) => {
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_update_shape(*l, s, n, no);
            lemma_update_shape(*r, s, n, no);
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            lemma_and_progress(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), mltl_parse_tree_to_mltl_spec(*l),
                mltl_parse_tree_to_mltl_spec(*r), pi, b);
            let (q, p) = and_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), no);
            lemma_propagate_progress_3(lp, rp, p);
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_update_shape(*l, s, n, no);
            lemma_update_shape(*r, s, n, no);
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            lemma_until_progress(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, mltl_parse_tree_to_mltl_spec(*l),
                a, ub, mltl_parse_tree_to_mltl_spec(*r), pi, b);
            let (q, o, p) = until_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, no);
            lemma_propagate_progress_3(lp, rp, p);
        },
        _ => {},
    }
}

/// Before the last pass of step `n` (the one reporting no progress), every
/// reading node is already ready for step `n + 1`: its reads in that pass
/// are at `(n + 1) − wpd(operands)` or later.
pub proof fn lemma_last_ready<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n + 1),
        untils_ready(t, n),
        until_c(t, n + 1),
        n < pi.len(),
        mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
    ensures
        nodes_ready(t, n + 1),
    decreases t,
{
    let no = LoopProgress::ReloopNoProgress;
    let s = pi[n as int];
    let b = n + 1;
    lemma_last_pass(t, pi, n);
    lemma_update_shape(t, s, n, no);
    match t {
        MltlParseTree::Not(d, c) => {
            let (c2, cp) = mltl_update(*c, s, n, no);
            let (q, p) = not_op(d.scq, get_scq_from_tree(c2), no);
            lemma_propagate_progress_2(cp, p);
            lemma_last_ready(*c, pi, n);
            lemma_update_reloop(*c, pi, n);
            lemma_not_last(d.scq, get_scq_from_tree(c2));
        },
        MltlParseTree::And(d, l, r) => {
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            let (q, p) = and_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), no);
            lemma_propagate_progress_3(lp, rp, p);
            lemma_last_ready(*l, pi, n);
            lemma_last_ready(*r, pi, n);
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_and_last(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2));
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            let (lq, rq) = (get_scq_from_tree(l2), get_scq_from_tree(r2));
            let (q, o, p) = until_op(d.scq, lq, rq, d.obs, no);
            lemma_propagate_progress_3(lp, rp, p);
            lemma_last_ready(*l, pi, n);
            lemma_last_ready(*r, pi, n);
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_rlnp_root(*l, pi, n);
            lemma_rlnp_root(*r, pi, n);
            lemma_update_reloop(t, pi, n);
            lemma_until_progress(d.scq, lq, rq, d.obs, mltl_parse_tree_to_mltl_spec(*l), a, ub,
                mltl_parse_tree_to_mltl_spec(*r), pi, b);
            if q.next_time != d.scq.next_time {
                lemma_until_skip_both(d.scq, lq, rq, d.obs, no);
                lemma_scq_read_some(d.scq, lq);
                lemma_scq_read_some(d.scq, rq);
            }
        },
        _ => {},
    }
}

} // verus!
