//! Promptness: by the end of time step `n`, every node has written verdicts
//! for all steps before `n + 1 − wpd(φ_node)` ([`r2u2_prompt`],
//! [`r2u2_correct`]). This holds for the algorithm as Isabelle and Rust
//! define it, including UNTIL's "skip ahead" that reports no progress.
//! Isabelle states promptness through formula progression
//! (`r2u2_promptness`, sorried); that eager notion is stronger than what R2U2
//! does, see `agent-docs/modules/r2u2.md`.
//!
//! Proof: (1) a time step ends with a pass that writes nothing, since every
//! pass reporting progress lowers [`tree_measure`] ([`lemma_update_measure`],
//! [`lemma_repeat_prompt`]). (2) In that last pass ([`lemma_last_pass`]),
//! NOT and AND have read up to (one of) their children's coverage, else they
//! would have written. An UNTIL node whose `next_time` was below what both
//! children are guaranteed to cover had data on both sides, so it skipped
//! ahead by at least one step; and it was at most one step behind after the
//! previous time step ([`untils_ready`]).
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

verus! {

// ---------------------------------------------------------------------------
// Termination measure of the reloop
// ---------------------------------------------------------------------------

/// How much a queue can still advance within the steps read (`b`).
pub open spec fn scq_measure(q: Scq, b: nat) -> nat {
    nat_sub(b, next_after(q.all_values)) + nat_sub(b, q.next_time)
}

pub open spec fn tree_measure<A>(t: Tree<A>, b: nat) -> nat
    decreases t,
{
    scq_measure(get_scq_from_tree(t), b) + match t {
        MltlParseTree::Not(_, c) | MltlParseTree::Future(_, _, _, c) | MltlParseTree::Global(_, _, _, c) =>
            tree_measure(*c, b),
        MltlParseTree::And(_, l, r) | MltlParseTree::Or(_, l, r) | MltlParseTree::Until(_, l, _, _, r)
        | MltlParseTree::Release(_, l, _, _, r) => tree_measure(*l, b) + tree_measure(*r, b),
        _ => 0,
    }
}

pub proof fn lemma_scq_measure(old: Scq, new: Scq, p: LoopProgress, b: nat)
    requires
        scq_step_ok(old, new, p, b),
    ensures
        scq_measure(new, b) <= scq_measure(old, b),
        p != LoopProgress::ReloopNoProgress ==> scq_measure(new, b) < scq_measure(old, b),
{
}

pub proof fn lemma_tree_measure_bound<A>(t: Tree<A>, b: nat)
    ensures
        tree_measure(t, b) <= 2 * b * size_parse_tree(t),
    decreases t,
{
    let s = size_parse_tree(t);
    match t {
        MltlParseTree::Not(_, c) | MltlParseTree::Future(_, _, _, c) | MltlParseTree::Global(_, _, _, c) => {
            lemma_tree_measure_bound(*c, b);
            let sc = size_parse_tree(*c);
            assert(2 * b * (1 + sc) == 2 * b + 2 * b * sc) by (nonlinear_arith);
        },
        MltlParseTree::And(_, l, r) | MltlParseTree::Or(_, l, r) | MltlParseTree::Until(_, l, _, _, r)
        | MltlParseTree::Release(_, l, _, _, r) => {
            lemma_tree_measure_bound(*l, b);
            lemma_tree_measure_bound(*r, b);
            let (sl, sr) = (size_parse_tree(*l), size_parse_tree(*r));
            assert(2 * b * (1 + sl + sr) == 2 * b + 2 * b * sl + 2 * b * sr) by (nonlinear_arith);
        },
        _ => {
            assert(2 * b * 1 == 2 * b) by (nonlinear_arith);
        },
    }
}

pub proof fn lemma_update_size<A>(t: Tree<A>, state: Set<A>, n: nat, progress: LoopProgress)
    ensures
        size_parse_tree(mltl_update(t, state, n, progress).0) == size_parse_tree(t),
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => lemma_update_size(*c, state, n, progress),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => {
            lemma_update_size(*l, state, n, progress);
            lemma_update_size(*r, state, n, progress);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Per-operator progress (reloop passes)
// ---------------------------------------------------------------------------

pub proof fn lemma_not_progress<A>(parent: Scq, child: Scq, phi: Mltl<A>, pi: Seq<Set<A>>, b: nat)
    requires
        hist_inv(parent.all_values, Mltl::Not(Box::new(phi)), pi, b),
        parent.next_time == next_after(parent.all_values),
        hist_inv(child.all_values, phi, pi, b),
    ensures
        ({
            let (q, p) = not_op(parent, child, LoopProgress::ReloopNoProgress);
            scq_step_ok(parent, q, p, b)
        }),
{
    lemma_not_step(parent, child, phi, pi, b, LoopProgress::ReloopNoProgress);
    lemma_propagate_progress_1(LoopProgress::ReloopNoProgress);
    if scq_read(parent, child).is_some() {
        lemma_scq_read_sound(parent, child);
    }
}

pub proof fn lemma_and_progress<A>(parent: Scq, left: Scq, right: Scq, phi: Mltl<A>, psi: Mltl<A>, pi: Seq<Set<A>>, b: nat)
    requires
        hist_inv(parent.all_values, Mltl::And(Box::new(phi), Box::new(psi)), pi, b),
        parent.next_time == next_after(parent.all_values),
        hist_inv(left.all_values, phi, pi, b),
        hist_inv(right.all_values, psi, pi, b),
    ensures
        ({
            let (q, p) = and_op(parent, left, right, LoopProgress::ReloopNoProgress);
            scq_step_ok(parent, q, p, b)
        }),
{
    lemma_and_step(parent, left, right, phi, psi, pi, b, LoopProgress::ReloopNoProgress);
    lemma_propagate_progress_1(LoopProgress::ReloopNoProgress);
    if scq_read(parent, left).is_some() {
        lemma_scq_read_sound(parent, left);
    }
    if scq_read(parent, right).is_some() {
        lemma_scq_read_sound(parent, right);
    }
}

pub proof fn lemma_not_last(parent: Scq, child: Scq)
    requires
        strictly_increasing(child.all_values),
        not_op(parent, child, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
    ensures
        parent.next_time >= next_after(child.all_values),
        not_op(parent, child, LoopProgress::ReloopNoProgress).0 == parent,
{
    lemma_propagate_progress_1(LoopProgress::ReloopNoProgress);
    lemma_scq_read_some(parent, child);
}

pub proof fn lemma_and_last(parent: Scq, left: Scq, right: Scq)
    requires
        strictly_increasing(left.all_values),
        strictly_increasing(right.all_values),
        and_op(parent, left, right, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
    ensures
        parent.next_time >= next_after(left.all_values) || parent.next_time >= next_after(right.all_values),
        and_op(parent, left, right, LoopProgress::ReloopNoProgress).0 == parent,
{
    lemma_propagate_progress_1(LoopProgress::ReloopNoProgress);
    lemma_scq_read_some(parent, left);
    lemma_scq_read_some(parent, right);
}

// ---------------------------------------------------------------------------
// A reloop pass: progress means something was written; the measure drops
// ---------------------------------------------------------------------------

pub proof fn lemma_update_measure<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n + 1),
        n < pi.len(),
    ensures
        ({
            let (t2, p) = mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress);
            &&& tree_measure(t2, n + 1) <= tree_measure(t, n + 1)
            &&& p != LoopProgress::ReloopNoProgress ==> tree_measure(t2, n + 1) < tree_measure(t, n + 1)
        }),
    decreases t,
{
    let no = LoopProgress::ReloopNoProgress;
    let s = pi[n as int];
    let b = n + 1;
    match t {
        MltlParseTree::Not(d, c) => {
            lemma_update_measure(*c, pi, n);
            lemma_update_reloop(*c, pi, n);
            lemma_update_shape(*c, s, n, no);
            let (c2, cp) = mltl_update(*c, s, n, no);
            lemma_not_progress(d.scq, get_scq_from_tree(c2), mltl_parse_tree_to_mltl_spec(*c), pi, b);
            let (q, p) = not_op(d.scq, get_scq_from_tree(c2), no);
            lemma_scq_measure(d.scq, q, p, b);
            lemma_propagate_progress_2(cp, p);
        },
        MltlParseTree::And(d, l, r) => {
            lemma_update_measure(*l, pi, n);
            lemma_update_measure(*r, pi, n);
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_update_shape(*l, s, n, no);
            lemma_update_shape(*r, s, n, no);
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            lemma_and_progress(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), mltl_parse_tree_to_mltl_spec(*l),
                mltl_parse_tree_to_mltl_spec(*r), pi, b);
            let (q, p) = and_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), no);
            lemma_scq_measure(d.scq, q, p, b);
            lemma_propagate_progress_3(lp, rp, p);
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            lemma_update_measure(*l, pi, n);
            lemma_update_measure(*r, pi, n);
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_update_shape(*l, s, n, no);
            lemma_update_shape(*r, s, n, no);
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            lemma_until_progress(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, mltl_parse_tree_to_mltl_spec(*l),
                a, ub, mltl_parse_tree_to_mltl_spec(*r), pi, b);
            let (q, o, p) = until_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, no);
            lemma_scq_measure(d.scq, q, p, b);
            lemma_propagate_progress_3(lp, rp, p);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// The last pass of a time step
// ---------------------------------------------------------------------------

/// The largest `wpd` of an UNTIL node's two operands.
pub open spec fn operands_wpd<A, B>(l: MltlParseTree<A, B>, r: MltlParseTree<A, B>) -> nat {
    crate::operators::max_nat(wpd(mltl_parse_tree_to_mltl_spec(l)), wpd(mltl_parse_tree_to_mltl_spec(r)))
}

/// Every UNTIL node's `next_time` has reached `k − wpd` of its operands:
/// what both operands are guaranteed to cover after `k` time steps.
pub open spec fn untils_ready<A>(t: Tree<A>, k: nat) -> bool
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => untils_ready(*c, k),
        MltlParseTree::And(_, l, r) => untils_ready(*l, k) && untils_ready(*r, k),
        MltlParseTree::Until(d, l, _, _, r) =>
            d.scq.next_time >= nat_sub(k, operands_wpd(*l, *r)) && untils_ready(*l, k) && untils_ready(*r, k),
        _ => true,
    }
}

/// `next_time` never goes down, so passes keep `untils_ready`.
pub proof fn lemma_update_ready<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, b: nat, progress: LoopProgress, k: nat)
    requires
        tree_inv(t, pi, b),
        untils_ready(t, k),
    ensures
        untils_ready(mltl_update(t, pi[n as int], n, progress).0, k),
    decreases t,
{
    let s = pi[n as int];
    match t {
        MltlParseTree::Not(_, c) => lemma_update_ready(*c, pi, n, b, progress, k),
        MltlParseTree::And(_, l, r) => {
            lemma_update_ready(*l, pi, n, b, progress, k);
            lemma_update_ready(*r, pi, n, b, progress, k);
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            lemma_update_ready(*l, pi, n, b, progress, k);
            lemma_update_ready(*r, pi, n, b, progress, k);
            lemma_update_shape(*l, s, n, progress);
            lemma_update_shape(*r, s, n, progress);
            let l2 = mltl_update(*l, s, n, progress).0;
            let r2 = mltl_update(*r, s, n, progress).0;
            lemma_until_next_time_mono(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, progress);
        },
        _ => {},
    }
}

/// Every node has covered all steps before `b − wpd` of its subformula.
pub open spec fn tree_prompt<A>(t: Tree<A>, b: nat) -> bool
    decreases t,
{
    &&& next_after(get_execution_sequence(t)) >= nat_sub(b, wpd(mltl_parse_tree_to_mltl_spec(t)))
    &&& match t {
        MltlParseTree::Not(_, c) => tree_prompt(*c, b),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => tree_prompt(*l, b) && tree_prompt(*r, b),
        _ => true,
    }
}

/// A reloop pass of time step `n` that reports no progress leaves every node
/// within `wpd` of the steps read, and every UNTIL node ready for step `n + 1`.
pub proof fn lemma_last_pass<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n + 1),
        untils_ready(t, n),
        n < pi.len(),
        mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).1 == LoopProgress::ReloopNoProgress,
    ensures
        tree_prompt(mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 1),
        untils_ready(mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).0, n + 1),
    decreases t,
{
    let no = LoopProgress::ReloopNoProgress;
    let s = pi[n as int];
    let b = n + 1;
    lemma_update_reloop(t, pi, n);
    lemma_update_shape(t, s, n, no);
    match t {
        MltlParseTree::Not(d, c) => {
            let (c2, cp) = mltl_update(*c, s, n, no);
            let (q, p) = not_op(d.scq, get_scq_from_tree(c2), no);
            lemma_propagate_progress_2(cp, p);
            lemma_last_pass(*c, pi, n);
            lemma_update_reloop(*c, pi, n);
            lemma_update_shape(*c, s, n, no);
            assert(tree_inv(c2, pi, b));
            lemma_not_last(d.scq, get_scq_from_tree(c2));
            assert(tree_prompt(c2, b));
        },
        MltlParseTree::And(d, l, r) => {
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            let (q, p) = and_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), no);
            lemma_propagate_progress_3(lp, rp, p);
            lemma_last_pass(*l, pi, n);
            lemma_last_pass(*r, pi, n);
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_update_shape(*l, s, n, no);
            lemma_update_shape(*r, s, n, no);
            assert(tree_inv(l2, pi, b) && tree_inv(r2, pi, b));
            lemma_and_last(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2));
            assert(tree_prompt(l2, b) && tree_prompt(r2, b));
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            let (l2, lp) = mltl_update(*l, s, n, no);
            let (r2, rp) = mltl_update(*r, s, n, no);
            let (q, o, p) = until_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, no);
            lemma_propagate_progress_3(lp, rp, p);
            lemma_last_pass(*l, pi, n);
            lemma_last_pass(*r, pi, n);
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_update_shape(*l, s, n, no);
            lemma_update_shape(*r, s, n, no);
            assert(tree_inv(l2, pi, b) && tree_inv(r2, pi, b));
            assert(tree_prompt(l2, b) && tree_prompt(r2, b));
            lemma_until_next_time_mono(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, no);
            let g = nat_sub(b, operands_wpd(*l, *r));
            if d.scq.next_time < g {
                lemma_until_last(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs);
            }
            let t2 = mltl_update(t, s, n, no).0;
            assert(t2 == MltlParseTree::Until(NodeData { scq: q, obs: o }, Box::new(l2), a, ub, Box::new(r2)));
            assert(q.next_time >= g);
            assert(tree_inv(t2, pi, b));
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Time steps and runs
// ---------------------------------------------------------------------------

/// With enough fuel, the reloop ends with a pass that reports no progress.
pub proof fn lemma_repeat_prompt<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, fuel: nat)
    requires
        tree_inv(t, pi, n + 1),
        untils_ready(t, n),
        n < pi.len(),
        fuel > tree_measure(t, n + 1),
    ensures
        tree_prompt(repeat_mltl_update(t, pi[n as int], n, fuel), n + 1),
        untils_ready(repeat_mltl_update(t, pi[n as int], n, fuel), n + 1),
    decreases fuel,
{
    let no = LoopProgress::ReloopNoProgress;
    lemma_update_measure(t, pi, n);
    lemma_update_reloop(t, pi, n);
    lemma_update_ready(t, pi, n, n + 1, no, n);
    let (t2, p) = mltl_update(t, pi[n as int], n, no);
    if p == no {
        lemma_last_pass(t, pi, n);
    } else {
        lemma_repeat_prompt(t2, pi, n, (fuel - 1) as nat);
    }
}

pub proof fn lemma_engine_step_prompt<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n),
        untils_ready(t, n),
        n < pi.len(),
    ensures
        tree_prompt(r2u2_engine_step(t, pi[n as int], n), n + 1),
        untils_ready(r2u2_engine_step(t, pi[n as int], n), n + 1),
{
    lemma_update_first(t, pi, n);
    lemma_update_size(t, pi[n as int], n, LoopProgress::FirstLoop);
    lemma_update_ready(t, pi, n, n, LoopProgress::FirstLoop, n);
    let t1 = mltl_update(t, pi[n as int], n, LoopProgress::FirstLoop).0;
    lemma_tree_measure_bound(t1, n + 1);
    let sz = size_parse_tree(t);
    assert(2 * (n + 1) * sz == 2 * sz * (n + 1)) by (nonlinear_arith);
    lemma_repeat_prompt(t1, pi, n, step_fuel(t, n));
}

pub proof fn lemma_initial_ready<A>(f: Mltl<A>)
    ensures
        untils_ready(parse_tree_with_scq(f), 0),
    decreases f,
{
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => lemma_initial_ready(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            lemma_initial_ready(*phi);
            lemma_initial_ready(*psi);
        },
        _ => {},
    }
}

/// After `k` steps every UNTIL node is ready, and for `k ≥ 1` every node is
/// within `wpd` of the steps read.
pub proof fn lemma_run_prompt<A>(t: Tree<A>, pi: Seq<Set<A>>, k: nat)
    requires
        tree_inv(t, pi, 0),
        untils_ready(t, 0),
        k <= pi.len(),
    ensures
        untils_ready(r2u2_run(t, pi, k), k),
        k >= 1 ==> tree_prompt(r2u2_run(t, pi, k), k),
    decreases k,
{
    if k > 0 {
        lemma_run_prompt(t, pi, (k - 1) as nat);
        lemma_run(t, pi, (k - 1) as nat);
        lemma_engine_step_prompt(r2u2_run(t, pi, (k - 1) as nat), pi, (k - 1) as nat);
    }
}

/// `convert_r2u2_form` keeps `wpd`.
pub proof fn lemma_wpd_convert<A>(f: Mltl<A>)
    ensures
        wpd(convert_r2u2_form(f)) == wpd(f),
    decreases f,
{
    reveal_with_fuel(wpd, 4);
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => lemma_wpd_convert(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            lemma_wpd_convert(*phi);
            lemma_wpd_convert(*psi);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Main theorems
// ---------------------------------------------------------------------------

/// Promptness: after monitoring all of `π`, the monitor has written verdicts
/// for every step `t` with `t + wpd(φ) < |π|` (and, by `r2u2_run_correct`,
/// after each prefix of length `k`, for every `t + wpd(φ) < k`).
pub proof fn r2u2_prompt<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        next_after(r2u2(phi, pi)) >= nat_sub(pi.len(), wpd(phi)),
{
    let c = convert_r2u2_form(phi);
    if pi.len() > 0 {
        convert_r2u2_form_is_r2u2_form(phi);
        convert_r2u2_form_welldef_intervals(phi);
        lemma_initial_tree(c, pi);
        lemma_initial_ready(c);
        lemma_run_prompt(parse_tree_with_scq(c), pi, pi.len());
        lemma_run(parse_tree_with_scq(c), pi, pi.len());
        lemma_wpd_convert(phi);
    }
}

/// Soundness and promptness together: every step `t` with `t + wpd(φ) < |π|`
/// has a verdict, and it is `drop t π ⊨ φ`.
pub proof fn r2u2_correct<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        forall|j: nat| j + wpd(phi) < pi.len() ==>
            #[trigger] value_at(r2u2(phi, pi), j) == 
            Some(semantics_mltl(drop(pi, j), phi)),
{
    r2u2_sound(phi, pi);
    r2u2_prompt(phi, pi);
}

} // verus!
