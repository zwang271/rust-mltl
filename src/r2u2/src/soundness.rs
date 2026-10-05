//! Correctness of the engine (Isabelle
//! `R2U2_Function.thy`: `True_/False_/Prop_execution_sequence`,
//! `Not_execution_sequence`, `Not_child_correct`, `And_execution_sequence`, and the shape of
//! `r2u2_soundness_alt_style`).
//!
//! Main results: [`r2u2_run_correct`] (after every time step, every verdict
//! any node has written is right for every trace extending what was read;
//! without UNTIL, every time step so far is covered), [`r2u2_sound`] (the
//! whole-trace soundness statement for every MLTL formula, also in
//! Isabelle's deaggregated form) and [`r2u2_correct_boolean`] (soundness and
//! completeness without temporal operators).
//!
//! Proof structure: one invariant per node ([`node_inv`]: the history is
//! strictly increasing, within the time steps read, and *sound*: it gives
//! every covered time step the formula's truth value), preserved by each
//! operator ([`lemma_load_step`], [`lemma_not_step`], [`lemma_and_step`],
//! `until.rs : lemma_until_step`), then by a pass, a
//! time step and a run.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use mltl_core::properties::*;
use crate::verdict::*;
use crate::scq::*;
use crate::operators::*;
use crate::engine::*;
use crate::until::*;

verus! {

// ---------------------------------------------------------------------------
// Invariants
// ---------------------------------------------------------------------------

/// The history `h` gives every time step it covers the truth value of `phi`
/// on the suffix of `pi` from that step.
pub open spec fn hist_sound<A>(h: Seq<Verdict>, phi: Mltl<A>, pi: Seq<Set<A>>) -> bool {
    forall|j: nat| j < next_after(h) ==> #[trigger] value_at(h, j) == Some(semantics_mltl(drop(pi, j), phi))
}

/// A queue history is well-formed, covers only steps before `b`, and is sound.
pub open spec fn hist_inv<A>(h: Seq<Verdict>, phi: Mltl<A>, pi: Seq<Set<A>>, b: nat) -> bool {
    &&& strictly_increasing(h)
    &&& next_after(h) <= b
    &&& hist_sound(h, phi, pi)
}

/// Formulas handled so far: True, False, Prop, Not and And.
pub open spec fn is_boolean_form<A>(f: Mltl<A>) -> bool
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => true,
        Mltl::Not(phi) => is_boolean_form(*phi),
        Mltl::And(phi, psi) => is_boolean_form(*phi) && is_boolean_form(*psi),
        _ => false,
    }
}

/// Invariant of a tree after the time steps before `b` have been read.
/// Leaves have covered exactly those steps; a NOT or AND node next needs
/// the step after its last write.
pub open spec fn tree_inv<A>(t: Tree<A>, pi: Seq<Set<A>>, b: nat) -> bool
    decreases t,
{
    &&& hist_inv(get_execution_sequence(t), mltl_parse_tree_to_mltl_spec(t), pi, b)
    &&& match t {
        MltlParseTree::True(d) | MltlParseTree::False(d) | MltlParseTree::Prop(d, _) =>
            next_after(d.scq.all_values) == b,
        MltlParseTree::Not(d, c) => d.scq.next_time == next_after(d.scq.all_values) && tree_inv(*c, pi, b),
        MltlParseTree::And(d, l, r) => d.scq.next_time == next_after(d.scq.all_values) && tree_inv(*l, pi, b)
            && tree_inv(*r, pi, b),
        MltlParseTree::Until(d, l, a, ub, r) => until_inv(d.scq, d.obs, mltl_parse_tree_to_mltl_spec(*l), a, ub,
            mltl_parse_tree_to_mltl_spec(*r), pi) && tree_inv(*l, pi, b) && tree_inv(*r, pi, b),
        _ => false,
    }
}

/// Every node has covered every time step before `b`.
pub open spec fn tree_complete<A>(t: Tree<A>, b: nat) -> bool
    decreases t,
{
    &&& next_after(get_execution_sequence(t)) == b
    &&& match t {
        MltlParseTree::Not(_, c) => tree_complete(*c, b),
        MltlParseTree::And(_, l, r) => tree_complete(*l, b) && tree_complete(*r, b),
        MltlParseTree::Until(_, _, _, _, _) => false,
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// Operators preserve the invariant
// ---------------------------------------------------------------------------

/// Appending `<v, n>` right after the covered steps extends a sound history
/// by step `n`, if `v` is the formula's value there.
pub proof fn lemma_hist_push<A>(h: Seq<Verdict>, v: Verdict, phi: Mltl<A>, pi: Seq<Set<A>>, b: nat)
    requires
        hist_inv(h, phi, pi, b),
        next_after(h) <= v.time,
        v.time < b,
        forall|j: nat| next_after(h) <= j <= v.time ==> v.val == semantics_mltl(#[trigger] drop(pi, j), phi),
    ensures
        hist_inv(h.push(v), phi, pi, b),
        next_after(h.push(v)) == v.time + 1,
{
    let h2 = h.push(v);
    assert forall|i: int, k: int| #![trigger h2[i], h2[k]] 0 <= i < k < h2.len() implies h2[i].time < h2[k].time by {
        assert(h2[i] == h[i]);
        if k < h.len() {
            assert(h2[k] == h[k]);
        } else if i < h.len() - 1 {
            assert(h[i].time < h[h.len() - 1].time);
        }
    }
    assert forall|j: nat| j < next_after(h2) implies #[trigger] value_at(h2, j) == Some(semantics_mltl(drop(pi, j), phi)) by {
        lemma_first_from_some(h, j);
        lemma_value_at_push(h, v, j);
        if j < next_after(h) {
            assert(value_at(h, j) == Some(semantics_mltl(drop(pi, j), phi)));
        }
    }
}

/// `LOAD`: on the first pass a leaf writes its value for step `n`.
pub proof fn lemma_load_step<A>(q: Scq, v: Verdict, phi: Mltl<A>, pi: Seq<Set<A>>, n: nat, progress: LoopProgress)
    requires
        hist_inv(q.all_values, phi, pi, n),
        next_after(q.all_values) == n,
        v.time == n,
        v.val == semantics_mltl(drop(pi, n), phi),
    ensures
        ({
            let (q2, p) = load(q, v, progress);
            progress == LoopProgress::FirstLoop ==> hist_inv(q2.all_values, phi, pi, n + 1)
                && next_after(q2.all_values) == n + 1 && p == LoopProgress::ReloopWithProgress
        }),
        progress != LoopProgress::FirstLoop ==> load(q, v, progress) == (q, LoopProgress::ReloopNoProgress),
{
    if progress == LoopProgress::FirstLoop {
        lemma_hist_push(q.all_values, v, phi, pi, n + 1);
    }
}

/// `NOT`: if the parent's history is sound for `¬φ` and the child's for `φ`,
/// the parent's history after the NOT step is still sound.
/// Completeness: if the child covers all steps before `b` and the parent
/// all steps before `b - 1`, the parent covers all steps before `b` after it.
/// If both already cover all steps before `b`, nothing happens.
pub proof fn lemma_not_step<A>(parent: Scq, child: Scq, phi: Mltl<A>, pi: Seq<Set<A>>, b: nat, progress: LoopProgress)
    requires
        hist_inv(parent.all_values, Mltl::Not(Box::new(phi)), pi, b),
        parent.next_time == next_after(parent.all_values),
        hist_inv(child.all_values, phi, pi, b),
    ensures
        ({
            let (q, p) = not_op(parent, child, progress);
            &&& hist_inv(q.all_values, Mltl::Not(Box::new(phi)), pi, b)
            &&& q.next_time == next_after(q.all_values)
            &&& q.next_time >= parent.next_time
            &&& (next_after(child.all_values) == b && parent.next_time + 1 == b) ==> next_after(q.all_values) == b
            &&& (next_after(child.all_values) == b && parent.next_time == b) ==>
                    q == parent && p == propagate_progress(seq![progress])
        }),
{
    lemma_scq_read_some(parent, child);
    match scq_read(parent, child) {
        Some(e) => {
            lemma_scq_read_sound(parent, child);
            let v = Verdict { val: !e.val, time: e.time };
            assert forall|j: nat| next_after(parent.all_values) <= j <= v.time implies
                v.val == semantics_mltl(#[trigger] drop(pi, j), Mltl::Not(Box::new(phi))) by {
                assert(value_at(child.all_values, j) == Some(e.val));
            }
            lemma_hist_push(parent.all_values, v, Mltl::Not(Box::new(phi)), pi, b);
        },
        None => {},
    }
}

/// `AND`: if the parent's history is sound for `φ ∧ ψ` and the children's
/// for `φ` and `ψ`, so is the parent's after the AND step. Completeness and
/// "nothing happens" as in [`lemma_not_step`], with both children covering
/// all steps before `b`.
pub proof fn lemma_and_step<A>(parent: Scq, left: Scq, right: Scq, phi: Mltl<A>, psi: Mltl<A>,
    pi: Seq<Set<A>>, b: nat, progress: LoopProgress)
    requires
        hist_inv(parent.all_values, Mltl::And(Box::new(phi), Box::new(psi)), pi, b),
        parent.next_time == next_after(parent.all_values),
        hist_inv(left.all_values, phi, pi, b),
        hist_inv(right.all_values, psi, pi, b),
    ensures
        ({
            let (q, p) = and_op(parent, left, right, progress);
            &&& hist_inv(q.all_values, Mltl::And(Box::new(phi), Box::new(psi)), pi, b)
            &&& q.next_time == next_after(q.all_values)
            &&& q.next_time >= parent.next_time
            &&& (next_after(left.all_values) == b && next_after(right.all_values) == b && parent.next_time + 1 == b)
                    ==> next_after(q.all_values) == b
            &&& (next_after(left.all_values) == b && next_after(right.all_values) == b && parent.next_time == b) ==>
                    q == parent && p == propagate_progress(seq![progress])
        }),
{
    let f = Mltl::And(Box::new(phi), Box::new(psi));
    let tau = parent.next_time;
    lemma_scq_read_some(parent, left);
    lemma_scq_read_some(parent, right);
    let rl = scq_read(parent, left);
    let rr = scq_read(parent, right);
    if rl.is_some() {
        lemma_scq_read_sound(parent, left);
    }
    if rr.is_some() {
        lemma_scq_read_sound(parent, right);
    }
    // The verdict written, if any: its value holds on all of [tau, v.time].
    let (q, p) = and_op(parent, left, right, progress);
    if q != parent {
        let v = q.all_values.last();
        assert(q.all_values == parent.all_values.push(v));
        assert forall|j: nat| next_after(parent.all_values) <= j <= v.time implies
            v.val == semantics_mltl(#[trigger] drop(pi, j), f) by {
            if rl.is_some() && j <= rl.unwrap().time {
                assert(value_at(left.all_values, j) == Some(rl.unwrap().val));
            }
            if rr.is_some() && j <= rr.unwrap().time {
                assert(value_at(right.all_values, j) == Some(rr.unwrap().val));
            }
        }
        lemma_hist_push(parent.all_values, v, f, pi, b);
    }
}

// ---------------------------------------------------------------------------
// A pass preserves the invariant
// ---------------------------------------------------------------------------

/// `mltl_update` keeps the formula (`mltl_update_preserves_tree`).
pub proof fn lemma_update_shape<A>(t: Tree<A>, state: Set<A>, n: nat, progress: LoopProgress)
    ensures
        mltl_parse_tree_to_mltl_spec(mltl_update(t, state, n, progress).0) == mltl_parse_tree_to_mltl_spec(t),
    decreases t,
{
    match t {
        MltlParseTree::Not(_, c) => lemma_update_shape(*c, state, n, progress),
        MltlParseTree::And(_, l, r) | MltlParseTree::Until(_, l, _, _, r) => {
            lemma_update_shape(*l, state, n, progress);
            lemma_update_shape(*r, state, n, progress);
        },
        _ => {},
    }
}

/// The first pass of time step `n` reads step `n`.
pub proof fn lemma_update_first<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n),
        n < pi.len(),
    ensures
        tree_inv(mltl_update(t, pi[n as int], n, LoopProgress::FirstLoop).0, pi, n + 1),
        tree_complete(t, n) ==> tree_complete(mltl_update(t, pi[n as int], n, LoopProgress::FirstLoop).0, n + 1),
    decreases t,
{
    let first = LoopProgress::FirstLoop;
    lemma_drop_len(pi, n);
    assert(drop(pi, n)[0] == pi[n as int]);
    match t {
        MltlParseTree::True(d) => {
            lemma_load_step(d.scq, Verdict { val: true, time: n }, Mltl::True, pi, n, first);
        },
        MltlParseTree::False(d) => {
            lemma_load_step(d.scq, Verdict { val: false, time: n }, Mltl::False, pi, n, first);
        },
        MltlParseTree::Prop(d, a) => {
            lemma_load_step(d.scq, Verdict { val: pi[n as int].contains(a), time: n }, Mltl::Prop(a), pi, n, first);
        },
        MltlParseTree::Not(d, c) => {
            lemma_update_first(*c, pi, n);
            lemma_update_shape(*c, pi[n as int], n, first);
            let c2 = mltl_update(*c, pi[n as int], n, first).0;
            lemma_not_step(d.scq, get_scq_from_tree(c2), mltl_parse_tree_to_mltl_spec(*c), pi, n + 1, first);
        },
        MltlParseTree::And(d, l, r) => {
            lemma_update_first(*l, pi, n);
            lemma_update_first(*r, pi, n);
            lemma_update_shape(*l, pi[n as int], n, first);
            lemma_update_shape(*r, pi[n as int], n, first);
            let l2 = mltl_update(*l, pi[n as int], n, first).0;
            let r2 = mltl_update(*r, pi[n as int], n, first).0;
            lemma_and_step(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), mltl_parse_tree_to_mltl_spec(*l),
                mltl_parse_tree_to_mltl_spec(*r), pi, n + 1, first);
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            lemma_update_first(*l, pi, n);
            lemma_update_first(*r, pi, n);
            lemma_update_shape(*l, pi[n as int], n, first);
            lemma_update_shape(*r, pi[n as int], n, first);
            let l2 = mltl_update(*l, pi[n as int], n, first).0;
            let r2 = mltl_update(*r, pi[n as int], n, first).0;
            lemma_until_step(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, mltl_parse_tree_to_mltl_spec(*l),
                a, ub, mltl_parse_tree_to_mltl_spec(*r), pi, n + 1, first);
        },
        _ => {},
    }
}

/// Later passes of time step `n` (after it was read).
pub proof fn lemma_update_reloop<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n + 1),
        n < pi.len(),
    ensures
        tree_inv(mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress).0, pi, n + 1),
        tree_complete(t, n + 1) ==> mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress)
            == (t, LoopProgress::ReloopNoProgress),
    decreases t,
{
    let no = LoopProgress::ReloopNoProgress;
    match t {
        MltlParseTree::Not(d, c) => {
            lemma_update_reloop(*c, pi, n);
            lemma_update_shape(*c, pi[n as int], n, no);
            let (c2, cp) = mltl_update(*c, pi[n as int], n, no);
            lemma_not_step(d.scq, get_scq_from_tree(c2), mltl_parse_tree_to_mltl_spec(*c), pi, n + 1, no);
            lemma_propagate_progress_1(no);
            let (q, p) = not_op(d.scq, get_scq_from_tree(c2), no);
            lemma_propagate_progress_2(cp, p);
            if tree_complete(t, n + 1) {
                assert(tree_complete(*c, n + 1));
                assert(c2 == *c && cp == no);
                assert(next_after(get_scq_from_tree(c2).all_values) == n + 1);
                assert(q == d.scq && p == no);
                assert(with_scq(d, d.scq) == d);
                assert(mltl_update(t, pi[n as int], n, no).0 == t);
            }
        },
        MltlParseTree::And(d, l, r) => {
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_update_shape(*l, pi[n as int], n, no);
            lemma_update_shape(*r, pi[n as int], n, no);
            let (l2, lp) = mltl_update(*l, pi[n as int], n, no);
            let (r2, rp) = mltl_update(*r, pi[n as int], n, no);
            lemma_and_step(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), mltl_parse_tree_to_mltl_spec(*l),
                mltl_parse_tree_to_mltl_spec(*r), pi, n + 1, no);
            lemma_propagate_progress_1(no);
            let (q, p) = and_op(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), no);
            lemma_propagate_progress_3(lp, rp, p);
            if tree_complete(t, n + 1) {
                assert(l2 == *l && lp == no);
                assert(r2 == *r && rp == no);
                assert(tree_complete(*l, n + 1) && tree_complete(*r, n + 1));
                assert(next_after(get_scq_from_tree(l2).all_values) == n + 1);
                assert(next_after(get_scq_from_tree(r2).all_values) == n + 1);
                assert(d.scq.next_time == n + 1);
                assert(q == d.scq);
                assert(p == no);
                assert(with_scq(d, d.scq) == d);
                assert(mltl_update(t, pi[n as int], n, no).0 == MltlParseTree::And(with_scq(d, q), Box::new(l2), Box::new(r2)));
                assert(mltl_update(t, pi[n as int], n, no).0 == t);
                assert(mltl_update(t, pi[n as int], n, no).1 == propagate_progress(seq![lp, rp, p]));
            }
        },
        MltlParseTree::Until(d, l, a, ub, r) => {
            lemma_update_reloop(*l, pi, n);
            lemma_update_reloop(*r, pi, n);
            lemma_update_shape(*l, pi[n as int], n, no);
            lemma_update_shape(*r, pi[n as int], n, no);
            let l2 = mltl_update(*l, pi[n as int], n, no).0;
            let r2 = mltl_update(*r, pi[n as int], n, no).0;
            lemma_until_step(d.scq, get_scq_from_tree(l2), get_scq_from_tree(r2), d.obs, mltl_parse_tree_to_mltl_spec(*l),
                a, ub, mltl_parse_tree_to_mltl_spec(*r), pi, n + 1, no);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Time steps and runs
// ---------------------------------------------------------------------------

pub proof fn lemma_repeat<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat, fuel: nat)
    requires
        tree_inv(t, pi, n + 1),
        n < pi.len(),
    ensures
        tree_inv(repeat_mltl_update(t, pi[n as int], n, fuel), pi, n + 1),
        mltl_parse_tree_to_mltl_spec(repeat_mltl_update(t, pi[n as int], n, fuel)) == mltl_parse_tree_to_mltl_spec(t),
        tree_complete(t, n + 1) ==> repeat_mltl_update(t, pi[n as int], n, fuel) == t,
    decreases fuel,
{
    if fuel > 0 {
        lemma_update_reloop(t, pi, n);
        lemma_update_shape(t, pi[n as int], n, LoopProgress::ReloopNoProgress);
        let (t2, p) = mltl_update(t, pi[n as int], n, LoopProgress::ReloopNoProgress);
        if p != LoopProgress::ReloopNoProgress {
            lemma_repeat(t2, pi, n, (fuel - 1) as nat);
        }
    }
}

/// One time step reads step `n` and keeps the invariant.
pub proof fn lemma_engine_step<A>(t: Tree<A>, pi: Seq<Set<A>>, n: nat)
    requires
        tree_inv(t, pi, n),
        n < pi.len(),
    ensures
        tree_inv(r2u2_engine_step(t, pi[n as int], n), pi, n + 1),
        mltl_parse_tree_to_mltl_spec(r2u2_engine_step(t, pi[n as int], n)) == mltl_parse_tree_to_mltl_spec(t),
        tree_complete(t, n) ==> tree_complete(r2u2_engine_step(t, pi[n as int], n), n + 1),
{
    lemma_update_first(t, pi, n);
    lemma_update_shape(t, pi[n as int], n, LoopProgress::FirstLoop);
    let t1 = mltl_update(t, pi[n as int], n, LoopProgress::FirstLoop).0;
    lemma_repeat(t1, pi, n, step_fuel(t, n));
}

/// After `k` time steps the invariant holds with bound `k` (and, for
/// trees without UNTIL, every node has covered every step).
pub proof fn lemma_run<A>(t: Tree<A>, pi: Seq<Set<A>>, k: nat)
    requires
        tree_inv(t, pi, 0),
        k <= pi.len(),
    ensures
        tree_inv(r2u2_run(t, pi, k), pi, k),
        tree_complete(t, 0) ==> tree_complete(r2u2_run(t, pi, k), k),
        mltl_parse_tree_to_mltl_spec(r2u2_run(t, pi, k)) == mltl_parse_tree_to_mltl_spec(t),
    decreases k,
{
    if k > 0 {
        lemma_run(t, pi, (k - 1) as nat);
        lemma_engine_step(r2u2_run(t, pi, (k - 1) as nat), pi, (k - 1) as nat);
    }
}

/// The initial tree satisfies the invariant with bound 0.
pub proof fn lemma_initial_tree<A>(f: Mltl<A>, pi: Seq<Set<A>>)
    requires
        is_r2u2_form(f),
        intervals_welldef(f),
    ensures
        tree_inv(parse_tree_with_scq(f), pi, 0),
        is_boolean_form(f) ==> tree_complete(parse_tree_with_scq(f), 0),
        mltl_parse_tree_to_mltl_spec(parse_tree_with_scq(f)) == f,
    decreases f,
{
    match f {
        Mltl::Not(phi) => lemma_initial_tree(*phi, pi),
        Mltl::And(phi, psi) | Mltl::Until(phi, _, _, psi) => {
            lemma_initial_tree(*phi, pi);
            lemma_initial_tree(*psi, pi);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Main theorems
// ---------------------------------------------------------------------------

/// After each of the first `k` time steps of `pi`, for φ in r2u2 form:
/// every node's history is sound for its subformula, for the whole trace
/// `pi` (the monitor has read only `pi[0..k]`, so this holds for every trace
/// that starts that way). For φ without UNTIL, every node also covers
/// exactly the steps `0 .. k - 1`.
pub proof fn r2u2_run_correct<A>(phi: Mltl<A>, pi: Seq<Set<A>>, k: nat)
    requires
        is_r2u2_form(phi),
        intervals_welldef(phi),
        k <= pi.len(),
    ensures
        tree_inv(r2u2_run(parse_tree_with_scq(phi), pi, k), pi, k),
        is_boolean_form(phi) ==> tree_complete(r2u2_run(parse_tree_with_scq(phi), pi, k), k),
        mltl_parse_tree_to_mltl_spec(r2u2_run(parse_tree_with_scq(phi), pi, k)) == phi,
{
    lemma_initial_tree(phi, pi);
    lemma_run(parse_tree_with_scq(phi), pi, k);
}

pub proof fn lemma_boolean_is_r2u2_form<A>(f: Mltl<A>)
    requires
        is_boolean_form(f),
    ensures
        is_r2u2_form(f),
    decreases f,
{
    match f {
        Mltl::Not(phi) => lemma_boolean_is_r2u2_form(*phi),
        Mltl::And(phi, psi) => {
            lemma_boolean_is_r2u2_form(*phi);
            lemma_boolean_is_r2u2_form(*psi);
        },
        _ => {},
    }
}

pub proof fn lemma_boolean_welldef<A>(f: Mltl<A>)
    requires
        is_boolean_form(f),
    ensures
        intervals_welldef(f),
    decreases f,
{
    match f {
        Mltl::Not(phi) => lemma_boolean_welldef(*phi),
        Mltl::And(phi, psi) => {
            lemma_boolean_welldef(*phi);
            lemma_boolean_welldef(*psi);
        },
        _ => {},
    }
}

/// Soundness of `r2u2 φ π` for every MLTL formula with well-formed intervals
/// (Isabelle's `r2u2_soundness_alt_style`, which is false for R2U2's bounded
/// queues, `R2U2_Bugs.thy`; it holds for this unbounded model): every
/// verdict the root has written is right. After deaggregation: one verdict
/// per time step from 0, the one at `t` equal to `drop t π ⊨ φ`.
pub proof fn r2u2_sound<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        strictly_increasing(r2u2(phi, pi)),
        next_after(r2u2(phi, pi)) <= pi.len(),
        forall|j: nat| j < next_after(r2u2(phi, pi)) ==>
            #[trigger] value_at(r2u2(phi, pi), j) == Some(semantics_mltl(drop(pi, j), phi)),
        forall|i: int| 0 <= i < deaggregate(r2u2(phi, pi)).len() ==>
            (#[trigger] deaggregate(r2u2(phi, pi))[i]).time == i
            && deaggregate(r2u2(phi, pi))[i].val == semantics_mltl(drop(pi, i as nat), phi),
{
    let c = convert_r2u2_form(phi);
    convert_r2u2_form_is_r2u2_form(phi);
    convert_r2u2_form_welldef_intervals(phi);
    convert_r2u2_form_equiv(phi);
    r2u2_run_correct(c, pi, pi.len());
    let h = r2u2(phi, pi);
    assert forall|j: nat| j < next_after(h) implies #[trigger] value_at(h, j) == Some(semantics_mltl(drop(pi, j), phi)) by {
        assert(value_at(h, j) == Some(semantics_mltl(drop(pi, j), c)));
        assert(semantics_mltl(drop(pi, j), phi) == semantics_mltl(drop(pi, j), c));
    }
    lemma_deaggregate(h);
    assert forall|i: int| 0 <= i < deaggregate(h).len() implies
        (#[trigger] deaggregate(h)[i]).time == i && deaggregate(h)[i].val == semantics_mltl(drop(pi, i as nat), phi) by {
        assert(value_at(h, i as nat) == Some(deaggregate(h)[i].val));
    }
}

/// `r2u2 φ π` for φ built from True, False, Prop, Not and And: one verdict per
/// time step after deaggregation, each equal to `drop t π ⊨ φ`. This is
/// Isabelle's `r2u2_soundness_alt_style` for this fragment, plus completeness.
pub proof fn r2u2_correct_boolean<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        is_boolean_form(phi),
    ensures
        strictly_increasing(r2u2(phi, pi)),
        next_after(r2u2(phi, pi)) == pi.len(),
        forall|j: nat| j < pi.len() ==> #[trigger] value_at(r2u2(phi, pi), j) == Some(semantics_mltl(drop(pi, j), phi)),
        deaggregate(r2u2(phi, pi)).len() == pi.len(),
        forall|i: int| 0 <= i < deaggregate(r2u2(phi, pi)).len() ==>
            (#[trigger] deaggregate(r2u2(phi, pi))[i]).time == i
            && deaggregate(r2u2(phi, pi))[i].val == semantics_mltl(drop(pi, i as nat), phi),
{
    lemma_boolean_is_r2u2_form(phi);
    lemma_boolean_welldef(phi);
    convert_r2u2_form_id(phi);
    r2u2_run_correct(phi, pi, pi.len());
    let h = r2u2(phi, pi);
    lemma_deaggregate(h);
    assert forall|i: int| 0 <= i < deaggregate(h).len() implies
        (#[trigger] deaggregate(h)[i]).time == i && deaggregate(h)[i].val == semantics_mltl(drop(pi, i as nat), phi) by {
        assert(value_at(h, i as nat) == Some(deaggregate(h)[i].val));
    }
}

} // verus!
