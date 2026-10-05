//! The engine (Isabelle `R2U2_Parse_Tree.thy`, `MLTL_Update_and_R2U2_Engine_Step.thy`,
//! `Rewrite_Rules_and_Proofs.thy` "Snoc Style", `R2U2_Function.thy`).
//!
//! The formula is a parse tree with a queue and an observer at every node.
//! One pass ([`mltl_update`]) runs every node, children first. Each time
//! step does a first pass and then repeats passes while some node made
//! progress ([`r2u2_engine_step`]). [`r2u2`] runs a whole trace and returns
//! the root's history.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use mltl_core::properties::*;
use crate::verdict::*;
use crate::scq::*;
use crate::operators::*;
use crate::observer::*;

verus! {

// ---------------------------------------------------------------------------
// Node data  (R2U2_Observer.thy, R2U2_Parse_Tree.thy)
// ---------------------------------------------------------------------------

/// `type_synonym node_data = SCQ × observer`
pub struct NodeData {
    pub scq: Scq,
    pub obs: Observer,
}

/// `initial_node_data` (no queue size, see `scq.rs`).
pub open spec fn initial_node_data() -> NodeData {
    NodeData { scq: initial_scq(0), obs: initial_observer(0, 0) }
}

/// `initial_node_data_temporal sz lb ub`: a temporal node first needs time `lb`.
pub open spec fn initial_node_data_temporal(lb: nat, ub: nat) -> NodeData {
    NodeData { scq: initial_scq(lb), obs: initial_observer(lb, ub) }
}

pub type Tree<A> = MltlParseTree<A, NodeData>;

/// `parse_tree_with_SCQ φ`, without queue sizes (`queue_size_sibling_nodes`
/// matters only for bounded queues).
pub open spec fn parse_tree_with_scq<A>(f: Mltl<A>) -> Tree<A>
    decreases f,
{
    match f {
        Mltl::True => MltlParseTree::True(initial_node_data()),
        Mltl::False => MltlParseTree::False(initial_node_data()),
        Mltl::Prop(p) => MltlParseTree::Prop(initial_node_data(), p),
        Mltl::Not(phi) => MltlParseTree::Not(initial_node_data(), Box::new(parse_tree_with_scq(*phi))),
        Mltl::And(phi, psi) => MltlParseTree::And(
            initial_node_data(), Box::new(parse_tree_with_scq(*phi)), Box::new(parse_tree_with_scq(*psi))),
        Mltl::Or(phi, psi) => MltlParseTree::Or(
            initial_node_data(), Box::new(parse_tree_with_scq(*phi)), Box::new(parse_tree_with_scq(*psi))),
        Mltl::Future(a, b, phi) => MltlParseTree::Future(
            initial_node_data_temporal(a as nat, b as nat), a, b, Box::new(parse_tree_with_scq(*phi))),
        Mltl::Global(a, b, phi) => MltlParseTree::Global(
            initial_node_data_temporal(a as nat, b as nat), a, b, Box::new(parse_tree_with_scq(*phi))),
        Mltl::Until(phi, a, b, psi) => MltlParseTree::Until(
            initial_node_data_temporal(a as nat, b as nat), Box::new(parse_tree_with_scq(*phi)), a, b,
            Box::new(parse_tree_with_scq(*psi))),
        Mltl::Release(phi, a, b, psi) => MltlParseTree::Release(
            initial_node_data_temporal(a as nat, b as nat), Box::new(parse_tree_with_scq(*phi)), a, b,
            Box::new(parse_tree_with_scq(*psi))),
    }
}

/// `get_scq_from_tree T`
pub open spec fn get_scq_from_tree<A>(t: Tree<A>) -> Scq {
    get_aux_data(t).scq
}

/// `get_execution_sequence T`: everything the root has written.
pub open spec fn get_execution_sequence<A>(t: Tree<A>) -> Seq<Verdict> {
    get_scq_from_tree(t).all_values
}

pub open spec fn with_scq(d: NodeData, q: Scq) -> NodeData {
    NodeData { scq: q, obs: d.obs }
}

// ---------------------------------------------------------------------------
// One pass  (mltl_update)
// ---------------------------------------------------------------------------

/// `mltl_update T π_h n progress`: run every node once at time step `n`,
/// where `state` (`π_h`) is the set of atoms true at `n`.
///
/// LOAD (True, False, Prop), NOT, AND and UNTIL: the r2u2 form. The
/// operators `convert_r2u2_form` removes (Or, Future, Global, Release)
/// leave the tree unchanged.
pub open spec fn mltl_update<A>(t: Tree<A>, state: Set<A>, n: nat, progress: LoopProgress) -> (Tree<A>, LoopProgress)
    decreases t,
{
    match t {
        MltlParseTree::True(d) => {
            let (q, p) = load(d.scq, Verdict { val: true, time: n }, progress);
            (MltlParseTree::True(with_scq(d, q)), p)
        },
        MltlParseTree::False(d) => {
            let (q, p) = load(d.scq, Verdict { val: false, time: n }, progress);
            (MltlParseTree::False(with_scq(d, q)), p)
        },
        MltlParseTree::Prop(d, a) => {
            let (q, p) = load(d.scq, Verdict { val: state.contains(a), time: n }, progress);
            (MltlParseTree::Prop(with_scq(d, q), a), p)
        },
        MltlParseTree::Not(d, phi) => {
            let (phi2, phi_progress) = mltl_update(*phi, state, n, progress);
            let (q, p) = not_op(d.scq, get_scq_from_tree(phi2), progress);
            (MltlParseTree::Not(with_scq(d, q), Box::new(phi2)), propagate_progress(seq![phi_progress, p]))
        },
        MltlParseTree::And(d, phi, psi) => {
            let (phi2, phi_progress) = mltl_update(*phi, state, n, progress);
            let (psi2, psi_progress) = mltl_update(*psi, state, n, progress);
            let (q, p) = and_op(d.scq, get_scq_from_tree(phi2), get_scq_from_tree(psi2), progress);
            (MltlParseTree::And(with_scq(d, q), Box::new(phi2), Box::new(psi2)),
                propagate_progress(seq![phi_progress, psi_progress, p]))
        },
        MltlParseTree::Until(d, phi, a, b, psi) => {
            let (phi2, phi_progress) = mltl_update(*phi, state, n, progress);
            let (psi2, psi_progress) = mltl_update(*psi, state, n, progress);
            let (q, o, p) = until_op(d.scq, get_scq_from_tree(phi2), get_scq_from_tree(psi2), d.obs, progress);
            (MltlParseTree::Until(NodeData { scq: q, obs: o }, Box::new(phi2), a, b, Box::new(psi2)),
                propagate_progress(seq![phi_progress, psi_progress, p]))
        },
        _ => (t, LoopProgress::ReloopNoProgress),
    }
}

// ---------------------------------------------------------------------------
// Time steps and whole runs  (repeat_mltl_update, r2u2_engine_step_alt, r2u2)
// ---------------------------------------------------------------------------

/// Passes allowed per time step after the first. Isabelle loops until no
/// progress and proves termination with `r2u2_measure`; here the loop is
/// bounded, and `promptness.rs : lemma_repeat_prompt` shows a pass with no
/// progress comes first (each progressing pass writes, raising some node's
/// written-up-to point, which is at most `n + 1`).
pub open spec fn step_fuel<A>(t: Tree<A>, n: nat) -> nat {
    2 * size_parse_tree(t) * (n + 1) + 1
}

/// `wpd φ` (`R2U2_Parse_Tree.thy`): worst-case propagation delay, how many
/// steps after time `t` the verdict for `t` may need.
pub open spec fn wpd<A>(f: Mltl<A>) -> nat
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 0,
        Mltl::Not(phi) => wpd(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => crate::operators::max_nat(wpd(*phi), wpd(*psi)),
        Mltl::Future(_, b, phi) | Mltl::Global(_, b, phi) => (b + wpd(*phi)) as nat,
        Mltl::Until(phi, _, b, psi) | Mltl::Release(phi, _, b, psi) => (b + crate::operators::max_nat(wpd(*phi), wpd(*psi))) as nat,
    }
}

/// `repeat_mltl_update T π_h n ReloopWithProgress`: repeat passes until one
/// makes no progress (at most `fuel` passes).
pub open spec fn repeat_mltl_update<A>(t: Tree<A>, state: Set<A>, n: nat, fuel: nat) -> Tree<A>
    decreases fuel,
{
    if fuel == 0 {
        t
    } else {
        let (t2, p) = mltl_update(t, state, n, LoopProgress::ReloopNoProgress);
        if p == LoopProgress::ReloopNoProgress {
            t2
        } else {
            repeat_mltl_update(t2, state, n, (fuel - 1) as nat)
        }
    }
}

/// One time step: a first pass, then passes until no progress.
pub open spec fn r2u2_engine_step<A>(t: Tree<A>, state: Set<A>, n: nat) -> Tree<A> {
    let (t1, _p) = mltl_update(t, state, n, LoopProgress::FirstLoop);
    repeat_mltl_update(t1, state, n, step_fuel(t, n))
}

/// `r2u2_engine_step_alt T π 0` on the first `k` states of `pi`.
pub open spec fn r2u2_run<A>(t: Tree<A>, pi: Seq<Set<A>>, k: nat) -> Tree<A>
    decreases k,
{
    if k == 0 {
        t
    } else {
        r2u2_engine_step(r2u2_run(t, pi, (k - 1) as nat), pi[k - 1], (k - 1) as nat)
    }
}

/// `r2u2 φ π`: the root's verdicts after monitoring all of `pi`.
pub open spec fn r2u2<A>(phi: Mltl<A>, pi: Seq<Set<A>>) -> Seq<Verdict> {
    get_execution_sequence(r2u2_run(parse_tree_with_scq(convert_r2u2_form(phi)), pi, pi.len()))
}

} // verus!
