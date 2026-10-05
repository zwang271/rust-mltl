//! The monitor with bounded ring-buffer queues (Isabelle's SCQ model with
//! read pointers). Same operators as the history model ([`not_core`],
//! [`and_core`], [`until_core`] take what was read); the queues are rings,
//! reads go through [`ring_read`] from the reader's pointers, writes through
//! [`ring_write`]. Each node also keeps `all_values`, the ghost record of
//! everything it wrote (Isabelle's field of the same name); for the root
//! that is the monitor's output.
//!
//! Queue sizes ([`child_slots`]): the child of a NOT gets 1 slot, a child `c`
//! of a binary node gets `wpd(operands) − bpd(c) + 1`, the root gets 1.
//! `ring_sim.rs` proves this monitor's output equals the history model's.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use mltl_core::properties::*;
use crate::verdict::*;
use crate::scq::*;
use crate::observer::*;
use crate::operators::*;
use crate::engine::*;
use crate::ring::*;

verus! {

/// Node state: the ring, `next_time`, read pointers into the two children
/// (Isabelle `read_ptr_left`/`read_ptr_right`), the observer, and the
/// ghost history of writes.
pub struct RNode {
    pub ring: Ring,
    pub all_values: Seq<Verdict>,
    pub next_time: nat,
    pub rd_left: nat,
    pub rd_right: nat,
    pub obs: Observer,
}

pub type RTree<A> = MltlParseTree<A, RNode>;

/// The history-model view of a node (forget the ring and pointers).
pub open spec fn rscq(d: RNode) -> Scq {
    Scq { all_values: d.all_values, next_time: d.next_time }
}

pub open spec fn abs_node(d: RNode) -> NodeData {
    NodeData { scq: rscq(d), obs: d.obs }
}

pub open spec fn abs_tree<A>(t: RTree<A>) -> Tree<A>
    decreases t,
{
    match t {
        MltlParseTree::True(d) => MltlParseTree::True(abs_node(d)),
        MltlParseTree::False(d) => MltlParseTree::False(abs_node(d)),
        MltlParseTree::Prop(d, p) => MltlParseTree::Prop(abs_node(d), p),
        MltlParseTree::Not(d, c) => MltlParseTree::Not(abs_node(d), Box::new(abs_tree(*c))),
        MltlParseTree::And(d, l, r) => MltlParseTree::And(abs_node(d), Box::new(abs_tree(*l)), Box::new(abs_tree(*r))),
        MltlParseTree::Or(d, l, r) => MltlParseTree::Or(abs_node(d), Box::new(abs_tree(*l)), Box::new(abs_tree(*r))),
        MltlParseTree::Future(d, a, b, c) => MltlParseTree::Future(abs_node(d), a, b, Box::new(abs_tree(*c))),
        MltlParseTree::Global(d, a, b, c) => MltlParseTree::Global(abs_node(d), a, b, Box::new(abs_tree(*c))),
        MltlParseTree::Until(d, l, a, b, r) =>
            MltlParseTree::Until(abs_node(d), Box::new(abs_tree(*l)), a, b, Box::new(abs_tree(*r))),
        MltlParseTree::Release(d, l, a, b, r) =>
            MltlParseTree::Release(abs_node(d), Box::new(abs_tree(*l)), a, b, Box::new(abs_tree(*r))),
    }
}

pub open spec fn get_ring<A>(t: RTree<A>) -> Ring {
    get_aux_data(t).ring
}

/// Apply an operator's result to the node: if it wrote a verdict, write it
/// to the ring too.
pub open spec fn store(d: RNode, q: Scq) -> RNode {
    RNode {
        ring: if q.all_values.len() > d.all_values.len() { ring_write(d.ring, q.all_values.last()) } else { d.ring },
        all_values: q.all_values,
        next_time: q.next_time,
        ..d
    }
}

/// One pass (`mltl_update`) with ring queues.
pub open spec fn mltl_update_r<A>(t: RTree<A>, state: Set<A>, n: nat, progress: LoopProgress) -> (RTree<A>, LoopProgress)
    decreases t,
{
    match t {
        MltlParseTree::True(d) => {
            let (q, p) = load(rscq(d), Verdict { val: true, time: n }, progress);
            (MltlParseTree::True(store(d, q)), p)
        },
        MltlParseTree::False(d) => {
            let (q, p) = load(rscq(d), Verdict { val: false, time: n }, progress);
            (MltlParseTree::False(store(d, q)), p)
        },
        MltlParseTree::Prop(d, a) => {
            let (q, p) = load(rscq(d), Verdict { val: state.contains(a), time: n }, progress);
            (MltlParseTree::Prop(store(d, q), a), p)
        },
        MltlParseTree::Not(d, phi) => {
            let (phi2, phi_progress) = mltl_update_r(*phi, state, n, progress);
            let (data, rd) = ring_read(get_ring(phi2), d.rd_left, d.next_time);
            let (q, p) = not_core(rscq(d), data, progress);
            (MltlParseTree::Not(RNode { rd_left: rd, ..store(d, q) }, Box::new(phi2)),
                propagate_progress(seq![phi_progress, p]))
        },
        MltlParseTree::And(d, phi, psi) => {
            let (phi2, phi_progress) = mltl_update_r(*phi, state, n, progress);
            let (psi2, psi_progress) = mltl_update_r(*psi, state, n, progress);
            let (ld, lrd) = ring_read(get_ring(phi2), d.rd_left, d.next_time);
            let (rdata, rrd) = ring_read(get_ring(psi2), d.rd_right, d.next_time);
            let (q, p) = and_core(rscq(d), ld, rdata, progress);
            (MltlParseTree::And(RNode { rd_left: lrd, rd_right: rrd, ..store(d, q) }, Box::new(phi2), Box::new(psi2)),
                propagate_progress(seq![phi_progress, psi_progress, p]))
        },
        MltlParseTree::Until(d, phi, a, b, psi) => {
            let (phi2, phi_progress) = mltl_update_r(*phi, state, n, progress);
            let (psi2, psi_progress) = mltl_update_r(*psi, state, n, progress);
            let (ld, lrd) = ring_read(get_ring(phi2), d.rd_left, d.next_time);
            let (rdata, rrd) = ring_read(get_ring(psi2), d.rd_right, d.next_time);
            let (q, o, p) = until_core(rscq(d), ld, rdata, d.obs, progress);
            (MltlParseTree::Until(RNode { rd_left: lrd, rd_right: rrd, obs: o, ..store(d, q) }, Box::new(phi2), a, b,
                Box::new(psi2)), propagate_progress(seq![phi_progress, psi_progress, p]))
        },
        _ => (t, LoopProgress::ReloopNoProgress),
    }
}

pub open spec fn repeat_mltl_update_r<A>(t: RTree<A>, state: Set<A>, n: nat, fuel: nat) -> RTree<A>
    decreases fuel,
{
    if fuel == 0 {
        t
    } else {
        let (t2, p) = mltl_update_r(t, state, n, LoopProgress::ReloopNoProgress);
        if p == LoopProgress::ReloopNoProgress { t2 } else { repeat_mltl_update_r(t2, state, n, (fuel - 1) as nat) }
    }
}

pub open spec fn r2u2_engine_step_r<A>(t: RTree<A>, state: Set<A>, n: nat) -> RTree<A> {
    let (t1, _p) = mltl_update_r(t, state, n, LoopProgress::FirstLoop);
    repeat_mltl_update_r(t1, state, n, 2 * size_parse_tree(t) * (n + 1) + 1)
}

pub open spec fn r2u2_run_r<A>(t: RTree<A>, pi: Seq<Set<A>>, k: nat) -> RTree<A>
    decreases k,
{
    if k == 0 { t } else { r2u2_engine_step_r(r2u2_run_r(t, pi, (k - 1) as nat), pi[k - 1], (k - 1) as nat) }
}

/// How far a reader whose operands have `wpd` at most `w` may be behind the
/// entries of child `c`: `w − bpd(c)`. The child writes the verdict for step
/// `t` no earlier than step `t + bpd(c)`, so it is at most that far ahead of
/// the reader.
pub open spec fn child_slack<A>(w: nat, c: Mltl<A>) -> nat {
    nat_sub(w, bpd(c))
}

/// Slots for the queue of child `c`: one more than the slack.
pub open spec fn child_slots<A>(w: nat, c: Mltl<A>) -> nat {
    child_slack(w, c) + 1
}

/// `wpd` of the operands of a node for `f` (the larger one, for two operands).
pub open spec fn operands_wpd_of<A>(f: Mltl<A>) -> nat {
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => wpd(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) =>
            crate::operators::max_nat(wpd(*phi), wpd(*psi)),
        _ => 0,
    }
}

pub open spec fn initial_rnode(size: nat, tau: nat, lb: nat, ub: nat) -> RNode {
    RNode { ring: empty_ring(size), all_values: Seq::empty(), next_time: tau, rd_left: 0, rd_right: 0,
        obs: initial_observer(lb, ub) }
}

/// `parse_tree_with_SCQ` with ring sizes: this node gets `size` slots; the
/// child of a NOT gets 1 slot (NOT always reads everything its child wrote),
/// each child `c` of a binary node gets `child_slots(wpd(operands), c)`.
pub open spec fn parse_tree_with_ring<A>(f: Mltl<A>, size: nat) -> RTree<A>
    decreases f,
{
    let w = operands_wpd_of(f);
    match f {
        Mltl::True => MltlParseTree::True(initial_rnode(size, 0, 0, 0)),
        Mltl::False => MltlParseTree::False(initial_rnode(size, 0, 0, 0)),
        Mltl::Prop(p) => MltlParseTree::Prop(initial_rnode(size, 0, 0, 0), p),
        Mltl::Not(phi) => MltlParseTree::Not(initial_rnode(size, 0, 0, 0), Box::new(parse_tree_with_ring(*phi, 1))),
        Mltl::And(phi, psi) => MltlParseTree::And(initial_rnode(size, 0, 0, 0),
            Box::new(parse_tree_with_ring(*phi, child_slots(w, *phi))),
            Box::new(parse_tree_with_ring(*psi, child_slots(w, *psi)))),
        Mltl::Or(phi, psi) => MltlParseTree::Or(initial_rnode(size, 0, 0, 0),
            Box::new(parse_tree_with_ring(*phi, child_slots(w, *phi))),
            Box::new(parse_tree_with_ring(*psi, child_slots(w, *psi)))),
        Mltl::Future(a, b, phi) => MltlParseTree::Future(initial_rnode(size, a as nat, a as nat, b as nat), a, b,
            Box::new(parse_tree_with_ring(*phi, 1))),
        Mltl::Global(a, b, phi) => MltlParseTree::Global(initial_rnode(size, a as nat, a as nat, b as nat), a, b,
            Box::new(parse_tree_with_ring(*phi, 1))),
        Mltl::Until(phi, a, b, psi) => MltlParseTree::Until(initial_rnode(size, a as nat, a as nat, b as nat),
            Box::new(parse_tree_with_ring(*phi, child_slots(w, *phi))), a, b,
            Box::new(parse_tree_with_ring(*psi, child_slots(w, *psi)))),
        Mltl::Release(phi, a, b, psi) => MltlParseTree::Release(initial_rnode(size, a as nat, a as nat, b as nat),
            Box::new(parse_tree_with_ring(*phi, child_slots(w, *phi))), a, b,
            Box::new(parse_tree_with_ring(*psi, child_slots(w, *psi)))),
    }
}

/// The ring monitor's output: every verdict the root wrote.
pub open spec fn r2u2_ring<A>(phi: Mltl<A>, pi: Seq<Set<A>>) -> Seq<Verdict> {
    get_aux_data(r2u2_run_r(parse_tree_with_ring(convert_r2u2_form(phi), 1), pi, pi.len())).all_values
}

} // verus!
