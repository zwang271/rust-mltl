//! The executable monitor: one pass, one time step, the initial tree, each
//! proved equal to the ring model (`ring_engine.rs`); and [`Monitor`], the
//! online API.
use vstd::prelude::*;
use std::collections::HashSet;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use mltl_core::properties::*;
use crate::verdict::*;
use crate::observer::*;
use crate::operators::*;
use crate::engine::*;
use crate::ring::*;
use crate::ring_engine::*;
use crate::exec::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub type ExTree = MltlParseTree<usize, ExNode>;

pub open spec fn tview(t: ExTree) -> RTree<usize>
    decreases t,
{
    match t {
        MltlParseTree::True(d) => MltlParseTree::True(d.view()),
        MltlParseTree::False(d) => MltlParseTree::False(d.view()),
        MltlParseTree::Prop(d, p) => MltlParseTree::Prop(d.view(), p),
        MltlParseTree::Not(d, c) => MltlParseTree::Not(d.view(), Box::new(tview(*c))),
        MltlParseTree::And(d, l, r) => MltlParseTree::And(d.view(), Box::new(tview(*l)), Box::new(tview(*r))),
        MltlParseTree::Or(d, l, r) => MltlParseTree::Or(d.view(), Box::new(tview(*l)), Box::new(tview(*r))),
        MltlParseTree::Future(d, a, b, c) => MltlParseTree::Future(d.view(), a, b, Box::new(tview(*c))),
        MltlParseTree::Global(d, a, b, c) => MltlParseTree::Global(d.view(), a, b, Box::new(tview(*c))),
        MltlParseTree::Until(d, l, a, b, r) => MltlParseTree::Until(d.view(), Box::new(tview(*l)), a, b, Box::new(tview(*r))),
        MltlParseTree::Release(d, l, a, b, r) =>
            MltlParseTree::Release(d.view(), Box::new(tview(*l)), a, b, Box::new(tview(*r))),
    }
}

/// Every ring is well-formed (non-empty, write pointer in range).
pub open spec fn twf(t: ExTree) -> bool
    decreases t,
{
    get_aux_data(t).wf() && match t {
        MltlParseTree::Not(_, c) | MltlParseTree::Future(_, _, _, c) | MltlParseTree::Global(_, _, _, c) => twf(*c),
        MltlParseTree::And(_, l, r) | MltlParseTree::Or(_, l, r) | MltlParseTree::Until(_, l, _, _, r)
        | MltlParseTree::Release(_, l, _, _, r) => twf(*l) && twf(*r),
        _ => true,
    }
}

pub proof fn lemma_tview_root(t: ExTree)
    ensures
        get_aux_data(tview(t)) == get_aux_data(t).view(),
{
}

pub fn root_of(t: &ExTree) -> (d: &ExNode)
    ensures
        *d == get_aux_data(*t),
{
    match t {
        MltlParseTree::True(d) | MltlParseTree::False(d) | MltlParseTree::Prop(d, _) | MltlParseTree::Not(d, _)
        | MltlParseTree::And(d, _, _) | MltlParseTree::Or(d, _, _) | MltlParseTree::Future(d, _, _, _)
        | MltlParseTree::Global(d, _, _, _) | MltlParseTree::Until(d, _, _, _, _) | MltlParseTree::Release(d, _, _, _, _) => d,
    }
}

/// Root history after a pass: the old one plus what the root wrote.
pub open spec fn root_wrote(t: RTree<usize>, t2: RTree<usize>, w: Option<ExVerdict>) -> bool {
    &&& w.is_some() ==> get_aux_data(t2).all_values == get_aux_data(t).all_values.push(w.unwrap().vv())
    &&& w.is_none() ==> get_aux_data(t2).all_values == get_aux_data(t).all_values
}

// ---------------------------------------------------------------------------
// One pass
// ---------------------------------------------------------------------------

/// The NOT node's part of a pass, after its child `c2` was updated from `c`.
#[verifier::spinoff_prover]
fn finish_not(d: ExNode, c2: ExTree, cp: LoopProgress, Ghost(c): Ghost<RTree<usize>>, state: &HashSet<usize>, n: usize,
    progress: &LoopProgress) -> (r: Option<(ExTree, LoopProgress, Option<ExVerdict>)>)
    requires
        d.wf(),
        twf(c2),
        (tview(c2), cp) == mltl_update_r(c, state@, n as nat, *progress),
    ensures
        r.is_some() ==> ({
            let (t2, p, w) = r.unwrap();
            let t = MltlParseTree::Not(d.view(), Box::new(c));
            &&& (tview(t2), p) == mltl_update_r(t, state@, n as nat, *progress)
            &&& twf(t2)
            &&& root_wrote(t, tview(t2), w)
        }),
{
    let mut d = d;
    let ghost d0 = d.view();
    let (data, rd) = root_of(&c2).ring.read(d.rd_left, d.next_time);
    let (p, w) = not_ex(&mut d, data, progress)?;
    d.rd_left = rd;
    let pr = propagate2(&cp, &p);
    let t2 = MltlParseTree::Not(d, Box::new(c2));
    proof {
        let t = MltlParseTree::Not(d0, Box::new(c));
        assert(get_ring(tview(c2)) == get_aux_data(c2).ring.view());
        assert(tview(t2) == mltl_update_r(t, state@, n as nat, *progress).0);
    }
    Some((t2, pr, w))
}

/// The AND node's part of a pass.
#[verifier::spinoff_prover]
fn finish_and(d: ExNode, l2: ExTree, lp: LoopProgress, r2: ExTree, rp: LoopProgress, Ghost(l): Ghost<RTree<usize>>,
    Ghost(r): Ghost<RTree<usize>>, state: &HashSet<usize>, n: usize, progress: &LoopProgress)
    -> (res: Option<(ExTree, LoopProgress, Option<ExVerdict>)>)
    requires
        d.wf(),
        twf(l2),
        twf(r2),
        (tview(l2), lp) == mltl_update_r(l, state@, n as nat, *progress),
        (tview(r2), rp) == mltl_update_r(r, state@, n as nat, *progress),
    ensures
        res.is_some() ==> ({
            let (t2, p, w) = res.unwrap();
            let t = MltlParseTree::And(d.view(), Box::new(l), Box::new(r));
            &&& (tview(t2), p) == mltl_update_r(t, state@, n as nat, *progress)
            &&& twf(t2)
            &&& root_wrote(t, tview(t2), w)
        }),
{
    let mut d = d;
    let ghost d0 = d.view();
    let (ld, lrd) = root_of(&l2).ring.read(d.rd_left, d.next_time);
    let (rdd, rrd) = root_of(&r2).ring.read(d.rd_right, d.next_time);
    let (p, w) = and_ex(&mut d, ld, rdd, progress)?;
    d.rd_left = lrd;
    d.rd_right = rrd;
    let pr = propagate3(&lp, &rp, &p);
    let t2 = MltlParseTree::And(d, Box::new(l2), Box::new(r2));
    proof {
        let t = MltlParseTree::And(d0, Box::new(l), Box::new(r));
        assert(get_ring(tview(l2)) == get_aux_data(l2).ring.view());
        assert(get_ring(tview(r2)) == get_aux_data(r2).ring.view());
        assert(tview(t2) == mltl_update_r(t, state@, n as nat, *progress).0);
    }
    Some((t2, pr, w))
}

/// The UNTIL node's part of a pass.
#[verifier::spinoff_prover]
fn finish_until(d: ExNode, l2: ExTree, lp: LoopProgress, a: usize, b: usize, r2: ExTree, rp: LoopProgress,
    Ghost(l): Ghost<RTree<usize>>, Ghost(r): Ghost<RTree<usize>>, state: &HashSet<usize>, n: usize, progress: &LoopProgress)
    -> (res: Option<(ExTree, LoopProgress, Option<ExVerdict>)>)
    requires
        d.wf(),
        twf(l2),
        twf(r2),
        (tview(l2), lp) == mltl_update_r(l, state@, n as nat, *progress),
        (tview(r2), rp) == mltl_update_r(r, state@, n as nat, *progress),
    ensures
        res.is_some() ==> ({
            let (t2, p, w) = res.unwrap();
            let t = MltlParseTree::Until(d.view(), Box::new(l), a, b, Box::new(r));
            &&& (tview(t2), p) == mltl_update_r(t, state@, n as nat, *progress)
            &&& twf(t2)
            &&& root_wrote(t, tview(t2), w)
        }),
{
    let mut d = d;
    let ghost d0 = d.view();
    let (ld, lrd) = root_of(&l2).ring.read(d.rd_left, d.next_time);
    let (rdd, rrd) = root_of(&r2).ring.read(d.rd_right, d.next_time);
    let (p, w) = until_ex(&mut d, ld, rdd, progress)?;
    d.rd_left = lrd;
    d.rd_right = rrd;
    let pr = propagate3(&lp, &rp, &p);
    let t2 = MltlParseTree::Until(d, Box::new(l2), a, b, Box::new(r2));
    proof {
        let t = MltlParseTree::Until(d0, Box::new(l), a, b, Box::new(r));
        assert(get_ring(tview(l2)) == get_aux_data(l2).ring.view());
        assert(get_ring(tview(r2)) == get_aux_data(r2).ring.view());
        assert(tview(t2) == mltl_update_r(t, state@, n as nat, *progress).0);
    }
    Some((t2, pr, w))
}

/// `mltl_update_r`, executed. Returns the new tree, its progress, and the
/// verdict the root wrote (if any); `None` on arithmetic overflow.
pub fn update_ex(t: ExTree, state: &HashSet<usize>, n: usize, progress: &LoopProgress)
    -> (r: Option<(ExTree, LoopProgress, Option<ExVerdict>)>)
    requires
        twf(t),
    ensures
        r.is_some() ==> ({
            let (t2, p, w) = r.unwrap();
            &&& (tview(t2), p) == mltl_update_r(tview(t), state@, n as nat, *progress)
            &&& twf(t2)
            &&& root_wrote(tview(t), tview(t2), w)
        }),
    decreases t,
{
    match t {
        MltlParseTree::True(mut d) => {
            let (p, w) = load_ex(&mut d, ExVerdict { val: true, time: n }, progress);
            Some((MltlParseTree::True(d), p, w))
        },
        MltlParseTree::False(mut d) => {
            let (p, w) = load_ex(&mut d, ExVerdict { val: false, time: n }, progress);
            Some((MltlParseTree::False(d), p, w))
        },
        MltlParseTree::Prop(mut d, a) => {
            let val = state.contains(&a);
            let (p, w) = load_ex(&mut d, ExVerdict { val, time: n }, progress);
            Some((MltlParseTree::Prop(d, a), p, w))
        },
        MltlParseTree::Not(d, c) => {
            let ghost cv = tview(*c);
            let (c2, cp, _) = update_ex(*c, state, n, progress)?;
            finish_not(d, c2, cp, Ghost(cv), state, n, progress)
        },
        MltlParseTree::And(d, l, r) => {
            let ghost (lv, rv) = (tview(*l), tview(*r));
            let (l2, lp, _) = update_ex(*l, state, n, progress)?;
            let (r2, rp, _) = update_ex(*r, state, n, progress)?;
            finish_and(d, l2, lp, r2, rp, Ghost(lv), Ghost(rv), state, n, progress)
        },
        MltlParseTree::Until(d, l, a, b, r) => {
            let ghost (lv, rv) = (tview(*l), tview(*r));
            let (l2, lp, _) = update_ex(*l, state, n, progress)?;
            let (r2, rp, _) = update_ex(*r, state, n, progress)?;
            finish_until(d, l2, lp, a, b, r2, rp, Ghost(lv), Ghost(rv), state, n, progress)
        },
        other => Some((other, LoopProgress::ReloopNoProgress, None)),
    }
}

// ---------------------------------------------------------------------------
// One time step
// ---------------------------------------------------------------------------

pub fn tree_size(t: &ExTree) -> (r: Option<usize>)
    ensures
        r.is_some() ==> r.unwrap() == size_parse_tree(tview(*t)),
    decreases t,
{
    match t {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => Some(1),
        MltlParseTree::Not(_, c) | MltlParseTree::Future(_, _, _, c) | MltlParseTree::Global(_, _, _, c) => {
            let s = tree_size(c)?;
            s.checked_add(1)
        },
        MltlParseTree::And(_, l, r) | MltlParseTree::Or(_, l, r) | MltlParseTree::Until(_, l, _, _, r)
        | MltlParseTree::Release(_, l, _, _, r) => {
            let sl = tree_size(l)?;
            let sr = tree_size(r)?;
            sl.checked_add(sr)?.checked_add(1)
        },
    }
}

/// `r2u2_engine_step_r`, executed; also returns the root's new verdicts.
pub fn step_ex(t: ExTree, state: &HashSet<usize>, n: usize) -> (r: Option<(ExTree, Vec<ExVerdict>)>)
    requires
        twf(t),
    ensures
        r.is_some() ==> ({
            let (t2, out) = r.unwrap();
            &&& tview(t2) == r2u2_engine_step_r(tview(t), state@, n as nat)
            &&& twf(t2)
            &&& get_aux_data(tview(t2)).all_values
                == get_aux_data(tview(t)).all_values + out@.map_values(|v: ExVerdict| v.vv())
        }),
{
    let sz = tree_size(&t)?;
    let n1 = n.checked_add(1)?;
    let fuel = sz.checked_mul(2)?.checked_mul(n1)?.checked_add(1)?;
    assert(fuel == 2 * size_parse_tree(tview(t)) * (n + 1) + 1) by (nonlinear_arith)
        requires fuel == sz * 2 * n1 + 1, sz == size_parse_tree(tview(t)), n1 == n + 1;
    let ghost t0 = tview(t);
    let ghost s = state@;
    let first = LoopProgress::FirstLoop;
    let (t1, _p, w) = update_ex(t, state, n, &first)?;
    let mut out: Vec<ExVerdict> = Vec::new();
    if let Some(v) = w {
        out.push(v);
    }
    proof {
        assert(out@.map_values(|v: ExVerdict| v.vv()) =~= (if w.is_some() { seq![w.unwrap().vv()] } else { Seq::empty() }));
    }
    let ghost target = repeat_mltl_update_r(tview(t1), s, n as nat, fuel as nat);
    let mut cur = t1;
    let mut f = fuel;
    let mut done = false;
    while !done && f > 0
        invariant
            twf(cur),
            !done ==> repeat_mltl_update_r(tview(cur), s, n as nat, f as nat) == target,
            done ==> tview(cur) == target,
            get_aux_data(tview(cur)).all_values == get_aux_data(t0).all_values + out@.map_values(|v: ExVerdict| v.vv()),
            s == state@,
        decreases f, (if done { 0nat } else { 1nat }),
    {
        let no = LoopProgress::ReloopNoProgress;
        let ghost before = tview(cur);
        let ghost out_before = out@;
        let (t2, p, w) = update_ex(cur, state, n, &no)?;
        if let Some(v) = w {
            out.push(v);
        }
        proof {
            assert(out@.map_values(|v: ExVerdict| v.vv()) =~= out_before.map_values(|v: ExVerdict| v.vv())
                + (if w.is_some() { seq![w.unwrap().vv()] } else { Seq::empty() }));
        }
        cur = t2;
        if progress_rlnp(&p) {
            done = true;
        } else {
            f = f - 1;
        }
    }
    proof {
        if !done {
            assert(f == 0);
        }
    }
    Some((cur, out))
}

// ---------------------------------------------------------------------------
// The initial tree
// ---------------------------------------------------------------------------

/// Executable `convert_r2u2_form`.
pub fn convert_r2u2_form_ex(f: &Mltl<usize>) -> (r: Mltl<usize>)
    ensures
        r == convert_r2u2_form(*f),
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(p) => Mltl::Prop(*p),
        Mltl::Not(phi) => Mltl::Not(Box::new(convert_r2u2_form_ex(phi))),
        Mltl::And(phi, psi) => Mltl::And(Box::new(convert_r2u2_form_ex(phi)), Box::new(convert_r2u2_form_ex(psi))),
        Mltl::Or(phi, psi) => Mltl::Not(Box::new(Mltl::And(
            Box::new(Mltl::Not(Box::new(convert_r2u2_form_ex(phi)))),
            Box::new(Mltl::Not(Box::new(convert_r2u2_form_ex(psi)))),
        ))),
        Mltl::Future(a, b, phi) => Mltl::Until(Box::new(Mltl::True), *a, *b, Box::new(convert_r2u2_form_ex(phi))),
        Mltl::Global(a, b, phi) => Mltl::Not(Box::new(Mltl::Until(
            Box::new(Mltl::True), *a, *b, Box::new(Mltl::Not(Box::new(convert_r2u2_form_ex(phi)))),
        ))),
        Mltl::Until(phi, a, b, psi) => Mltl::Until(Box::new(convert_r2u2_form_ex(phi)), *a, *b, Box::new(convert_r2u2_form_ex(psi))),
        Mltl::Release(phi, a, b, psi) => Mltl::Not(Box::new(Mltl::Until(
            Box::new(Mltl::Not(Box::new(convert_r2u2_form_ex(phi)))), *a, *b,
            Box::new(Mltl::Not(Box::new(convert_r2u2_form_ex(psi)))),
        ))),
    }
}

/// Executable `wpd` (`None` on overflow).
pub fn wpd_ex(f: &Mltl<usize>) -> (r: Option<usize>)
    ensures
        r.is_some() ==> r.unwrap() == wpd(*f),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => Some(0),
        Mltl::Not(phi) => wpd_ex(phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            let x = wpd_ex(phi)?;
            let y = wpd_ex(psi)?;
            Some(if x >= y { x } else { y })
        },
        Mltl::Future(_, b, phi) | Mltl::Global(_, b, phi) => {
            let x = wpd_ex(phi)?;
            b.checked_add(x)
        },
        Mltl::Until(phi, _, b, psi) | Mltl::Release(phi, _, b, psi) => {
            let x = wpd_ex(phi)?;
            let y = wpd_ex(psi)?;
            b.checked_add(if x >= y { x } else { y })
        },
    }
}

/// Executable `bpd` (`None` on overflow).
pub fn bpd_ex(f: &Mltl<usize>) -> (r: Option<usize>)
    ensures
        r.is_some() ==> r.unwrap() == bpd(*f),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => Some(0),
        Mltl::Not(phi) => bpd_ex(phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            let x = bpd_ex(phi)?;
            let y = bpd_ex(psi)?;
            Some(if x <= y { x } else { y })
        },
        Mltl::Future(a, _, phi) | Mltl::Global(a, _, phi) => {
            let x = bpd_ex(phi)?;
            a.checked_add(x)
        },
        Mltl::Until(phi, a, _, psi) | Mltl::Release(phi, a, _, psi) => {
            let x = bpd_ex(phi)?;
            let y = bpd_ex(psi)?;
            a.checked_add(if x <= y { x } else { y })
        },
    }
}

/// Executable `operands_wpd_of`.
pub fn operands_wpd_ex(f: &Mltl<usize>) -> (r: Option<usize>)
    ensures
        r.is_some() ==> r.unwrap() == operands_wpd_of(*f),
{
    match f {
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => wpd_ex(phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            let x = wpd_ex(phi)?;
            let y = wpd_ex(psi)?;
            Some(if x >= y { x } else { y })
        },
        _ => Some(0),
    }
}

/// Executable `child_slots` (child `c`, sibling `s`).
pub fn child_slots_ex(w: usize, c: &Mltl<usize>, s: &Mltl<usize>) -> (r: Option<usize>)
    ensures
        r.is_some() ==> r.unwrap() == child_slots(w as nat, *c, *s),
{
    let b = bpd_ex(c)?;
    let ws = wpd_ex(s)?;
    let x = if w >= b { w - b } else { 0 };
    let y = if ws >= b { ws - b } else { 0 };
    let sum = x.checked_add(y)?.checked_add(1)?;
    (sum / 2).checked_add(1)
}

fn initial_ex_node(size: usize, tau: usize, lb: usize, ub: usize) -> (d: ExNode)
    requires
        size > 0,
    ensures
        d.view() == initial_rnode(size as nat, tau as nat, lb as nat, ub as nat),
        d.wf(),
{
    let ring = ExRing::new(size);
    ExNode { ring, next_time: tau, rd_left: 0, rd_right: 0,
        obs: ExObserver { lower_bound: lb, upper_bound: ub, prev_verdict: None }, all_values: Ghost(Seq::empty()) }
}

/// `parse_tree_with_ring f size`, executed (`None` on overflow).
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub fn init_ex(f: &Mltl<usize>, size: usize) -> (r: Option<ExTree>)
    requires
        size > 0,
    ensures
        r.is_some() ==> tview(r.unwrap()) == parse_tree_with_ring(*f, size as nat) && twf(r.unwrap()),
    decreases f,
{
    match f {
        Mltl::True => Some(MltlParseTree::True(initial_ex_node(size, 0, 0, 0))),
        Mltl::False => Some(MltlParseTree::False(initial_ex_node(size, 0, 0, 0))),
        Mltl::Prop(p) => Some(MltlParseTree::Prop(initial_ex_node(size, 0, 0, 0), *p)),
        Mltl::Not(phi) => {
            let c = init_ex(phi, 1)?;
            Some(MltlParseTree::Not(initial_ex_node(size, 0, 0, 0), Box::new(c)))
        },
        Mltl::And(phi, psi) => {
            let w = operands_wpd_ex(f)?;
            let l = init_ex(phi, child_slots_ex(w, phi, psi)?)?;
            let r = init_ex(psi, child_slots_ex(w, psi, phi)?)?;
            Some(MltlParseTree::And(initial_ex_node(size, 0, 0, 0), Box::new(l), Box::new(r)))
        },
        Mltl::Or(phi, psi) => {
            let w = operands_wpd_ex(f)?;
            let l = init_ex(phi, child_slots_ex(w, phi, psi)?)?;
            let r = init_ex(psi, child_slots_ex(w, psi, phi)?)?;
            Some(MltlParseTree::Or(initial_ex_node(size, 0, 0, 0), Box::new(l), Box::new(r)))
        },
        Mltl::Future(a, b, phi) => {
            let c = init_ex(phi, 1)?;
            Some(MltlParseTree::Future(initial_ex_node(size, *a, *a, *b), *a, *b, Box::new(c)))
        },
        Mltl::Global(a, b, phi) => {
            let c = init_ex(phi, 1)?;
            Some(MltlParseTree::Global(initial_ex_node(size, *a, *a, *b), *a, *b, Box::new(c)))
        },
        Mltl::Until(phi, a, b, psi) => {
            let w = operands_wpd_ex(f)?;
            let l = init_ex(phi, child_slots_ex(w, phi, psi)?)?;
            let r = init_ex(psi, child_slots_ex(w, psi, phi)?)?;
            Some(MltlParseTree::Until(initial_ex_node(size, *a, *a, *b), Box::new(l), *a, *b, Box::new(r)))
        },
        Mltl::Release(phi, a, b, psi) => {
            let w = operands_wpd_ex(f)?;
            let l = init_ex(phi, child_slots_ex(w, phi, psi)?)?;
            let r = init_ex(psi, child_slots_ex(w, psi, phi)?)?;
            Some(MltlParseTree::Release(initial_ex_node(size, *a, *a, *b), Box::new(l), *a, *b, Box::new(r)))
        },
    }
}

// ---------------------------------------------------------------------------
// The online monitor
// ---------------------------------------------------------------------------

/// The ring monitor's tree after `k` steps depends only on the first `k` states.
pub proof fn lemma_run_r_prefix<A>(t: RTree<A>, pi: Seq<Set<A>>, pi2: Seq<Set<A>>, k: nat)
    requires
        k <= pi.len(),
        k <= pi2.len(),
        forall|i: int| 0 <= i < k ==> pi[i] == pi2[i],
    ensures
        r2u2_run_r(t, pi, k) == r2u2_run_r(t, pi2, k),
    decreases k,
{
    if k > 0 {
        lemma_run_r_prefix(t, pi, pi2, (k - 1) as nat);
    }
}

/// `pi` begins with the states `prefix`.
pub open spec fn starts_with(pi: Seq<Set<usize>>, prefix: Seq<Set<usize>>) -> bool {
    prefix.len() <= pi.len() && forall|i: int| 0 <= i < prefix.len() ==> pi[i] == prefix[i]
}

/// Executable `intervals_welldef`: every interval `[a, b]` has `a ≤ b`.
pub fn intervals_welldef_ex(f: &Mltl<usize>) -> (r: bool)
    ensures
        r == intervals_welldef(*f),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => true,
        Mltl::Not(phi) => intervals_welldef_ex(phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => intervals_welldef_ex(phi) && intervals_welldef_ex(psi),
        Mltl::Future(a, b, phi) | Mltl::Global(a, b, phi) => *a <= *b && intervals_welldef_ex(phi),
        Mltl::Until(phi, a, b, psi) | Mltl::Release(phi, a, b, psi) =>
            *a <= *b && intervals_welldef_ex(phi) && intervals_welldef_ex(psi),
    }
}

pub open spec fn initial_tree_spec(phi: Mltl<usize>) -> RTree<usize> {
    parse_tree_with_ring(convert_r2u2_form(phi), 1)
}

pub open spec fn verdicts_view(out: Seq<ExVerdict>) -> Seq<Verdict> {
    out.map_values(|v: ExVerdict| v.vv())
}

/// An R2U2 monitor for one formula, fed one time step at a time.
/// (Fields are public so that specs can name them; change them only
/// through the methods, which keep `inv`.)
pub struct Monitor {
    pub tree: Option<ExTree>,
    pub steps: usize,
    pub out: Vec<ExVerdict>,
    /// The formula being monitored.
    pub formula: Ghost<Mltl<usize>>,
    /// The states fed so far.
    pub trace: Ghost<Seq<Set<usize>>>,
}

impl Monitor {
    /// The monitor is the ring model run on the states fed so far, and
    /// `verdicts()` is everything its root has written.
    pub open spec fn inv(&self) -> bool {
        &&& intervals_welldef(self.formula@)
        &&& self.tree.is_some()
        &&& twf(self.tree.unwrap())
        &&& self.trace@.len() == self.steps
        &&& tview(self.tree.unwrap()) == r2u2_run_r(initial_tree_spec(self.formula@), self.trace@, self.steps as nat)
        &&& verdicts_view(self.out@) == get_aux_data(tview(self.tree.unwrap())).all_values
    }

    pub open spec fn steps_spec(&self) -> nat {
        self.steps as nat
    }

    pub open spec fn verdicts_spec(&self) -> Seq<Verdict> {
        verdicts_view(self.out@)
    }

    /// A monitor for `phi`. `None` if an interval has `a > b`, or if the time
    /// bounds overflow `usize`.
    pub fn new(phi: &Mltl<usize>) -> (r: Option<Monitor>)
        ensures
            r.is_some() ==> r.unwrap().inv() && r.unwrap().formula@ == *phi && r.unwrap().steps_spec() == 0,
            r.is_some() ==> r.unwrap().verdicts_spec() == Seq::<Verdict>::empty(),
            intervals_welldef(*phi) == false ==> r.is_none(),
    {
        if !intervals_welldef_ex(phi) {
            return None;
        }
        let c = convert_r2u2_form_ex(phi);
        let tree = init_ex(&c, 1)?;
        let m = Monitor { tree: Some(tree), steps: 0, out: Vec::new(), formula: Ghost(*phi), trace: Ghost(Seq::empty()) };
        proof {
            assert(verdicts_view(m.out@) =~= Seq::<Verdict>::empty());
        }
        Some(m)
    }

    /// Feed the next state (the set of atoms true at this step). Returns
    /// `false` (and the monitor stops) only on arithmetic overflow.
    ///
    /// **The guarantee** (`V` = `verdicts()`, `φ` = the formula): for every
    /// trace `pi` that begins with the states fed so far,
    /// 1. every verdict is right: each step `j` that `V` covers gets the truth
    ///    value of `φ` at `j` (`value_at(V, j)` is the value of the first
    ///    verdict whose time is `≥ j`);
    /// 2. no step waits longer than `wpd(φ)`: every step `j` with
    ///    `j + wpd(φ) < steps` is covered.
    pub fn step(&mut self, state: &HashSet<usize>) -> (ok: bool)
        requires
            old(self).inv(),
        ensures
            ok ==> forall|pi: Seq<Set<usize>>| #[trigger] starts_with(pi, final(self).trace@) ==>
                forall|j: nat| j < next_after(final(self).verdicts_spec()) ==>
                    #[trigger] value_at(final(self).verdicts_spec(), j) == Some(semantics_mltl(drop(pi, j), final(self).formula@)),
            ok ==> next_after(final(self).verdicts_spec()) >= nat_sub(final(self).steps_spec(), wpd(final(self).formula@)),
            ok ==> final(self).trace@ == old(self).trace@.push(state@) && final(self).steps_spec() == old(self).steps_spec() + 1,
            ok ==> final(self).inv(),
            final(self).formula@ == old(self).formula@,
    {
        let n = self.steps;
        let n1 = match n.checked_add(1) {
            Some(x) => x,
            None => { return false; },
        };
        let t = self.tree.take().unwrap();
        let ghost tv = tview(t);
        let ghost out0 = self.out@;
        match step_ex(t, state, n) {
            Some((t2, new_out)) => {
                let ghost trace2 = self.trace@.push(state@);
                proof {
                    lemma_run_r_prefix(initial_tree_spec(self.formula@), self.trace@, trace2, n as nat);
                    assert(trace2[n as int] == state@);
                }
                let mut i: usize = 0;
                while i < new_out.len()
                    invariant
                        i <= new_out.len(),
                        self.out@ == out0 + new_out@.subrange(0, i as int),
                    decreases new_out.len() - i,
                {
                    self.out.push(new_out[i]);
                    proof {
                        assert(new_out@.subrange(0, i as int + 1) =~= new_out@.subrange(0, i as int).push(new_out@[i as int]));
                    }
                    i = i + 1;
                }
                proof {
                    assert(new_out@.subrange(0, new_out.len() as int) =~= new_out@);
                    assert(verdicts_view(out0 + new_out@) =~= verdicts_view(out0) + new_out@.map_values(|v: ExVerdict| v.vv()));
                }
                self.tree = Some(t2);
                self.steps = n1;
                self.trace = Ghost(trace2);
                proof {
                    let ghost m: &Monitor = &*self;
                    assert forall|pi: Seq<Set<usize>>| #[trigger] starts_with(pi, m.trace@) implies
                        forall|j: nat| j < next_after(m.verdicts_spec()) ==>
                            #[trigger] value_at(m.verdicts_spec(), j) == Some(semantics_mltl(drop(pi, j), m.formula@)) by {
                        monitor_correct(m, pi);
                    }
                    monitor_correct(m, m.trace@);
                }
                true
            },
            None => false,
        }
    }

    /// Every verdict the root has written so far, in order (compacted: the
    /// verdict `(v, t)` covers every step after the previous one up to `t`).
    pub fn verdicts(&self) -> (r: &Vec<ExVerdict>)
        ensures
            r@ == self.out@,
    {
        &self.out
    }
}

/// **Correctness of the executable monitor.** After `k` steps on states
/// that begin any trace `pi`: every verdict written so far is right for
/// `pi` (`value_at` gives `drop t pi ⊨ φ` at every covered step `t`), and
/// every step `t` with `t + wpd(φ) < k` is covered.
pub proof fn monitor_correct(m: &Monitor, pi: Seq<Set<usize>>)
    requires
        m.inv(),
        intervals_welldef(m.formula@),
        m.steps_spec() <= pi.len(),
        forall|i: int| 0 <= i < m.steps_spec() ==> pi[i] == m.trace@[i],
    ensures
        forall|j: nat| j < next_after(m.verdicts_spec()) ==>
            #[trigger] value_at(m.verdicts_spec(), j) == Some(semantics_mltl(drop(pi, j), m.formula@)),
        next_after(m.verdicts_spec()) >= nat_sub(m.steps_spec(), wpd(m.formula@)),
{
    let phi = m.formula@;
    let k = m.steps_spec();
    let c = convert_r2u2_form(phi);
    convert_r2u2_form_is_r2u2_form(phi);
    convert_r2u2_form_welldef_intervals(phi);
    convert_r2u2_form_equiv(phi);
    crate::ring_sim::lemma_initial_ring(c, 1);
    crate::soundness::lemma_initial_tree(c, pi);
    crate::promptness::lemma_initial_ready(c);
    crate::queue_size::lemma_initial_nodes_ready(c);
    crate::tight::lemma_initial_tight(c);
    crate::half::lemma_initial_half(c);
    let rt = initial_tree_spec(phi);
    lemma_run_r_prefix(rt, m.trace@, pi, k);
    crate::ring_sim::lemma_sim_run(rt, 1, pi, k);
    crate::ring_sim::lemma_abs_shape(r2u2_run_r(rt, pi, k));
    crate::soundness::r2u2_run_correct(c, pi, k);
    let h = m.verdicts_spec();
    assert forall|j: nat| j < next_after(h) implies #[trigger] value_at(h, j) == Some(semantics_mltl(drop(pi, j), phi)) by {
        assert(value_at(h, j) == Some(semantics_mltl(drop(pi, j), c)));
    }
    if k > 0 {
        crate::promptness::lemma_run_prompt(parse_tree_with_scq(c), pi, k);
        crate::promptness::lemma_wpd_convert(phi);
    }
}

/// Monitor a whole trace. `None` if an interval has `a > b` or on overflow.
///
/// **The guarantee** (`V` = the verdicts, `pi` = the trace): every step `j`
/// that `V` covers gets the truth value of `φ` at `j`, and every step `j` with
/// `j + wpd(φ) < |pi|` is covered. (`V` is also exactly `r2u2_ring φ pi`.)
pub fn monitor_trace(phi: &Mltl<usize>, trace: &Vec<HashSet<usize>>) -> (r: Option<Vec<ExVerdict>>)
    ensures
        r.is_some() ==> forall|j: nat| j < next_after(verdicts_view(r.unwrap()@)) ==>
            #[trigger] value_at(verdicts_view(r.unwrap()@), j)
                == Some(semantics_mltl(drop(trace@.map_values(|s: HashSet<usize>| s@), j), *phi)),
        r.is_some() ==> next_after(verdicts_view(r.unwrap()@)) >= nat_sub(trace@.len() as nat, wpd(*phi)),
        r.is_some() ==> verdicts_view(r.unwrap()@) == r2u2_ring(*phi, trace@.map_values(|s: HashSet<usize>| s@)),
{
    let ghost tv = trace@.map_values(|s: HashSet<usize>| s@);
    let mut m = Monitor::new(phi)?;
    let mut i: usize = 0;
    while i < trace.len()
        invariant
            i <= trace.len(),
            m.inv(),
            m.formula@ == *phi,
            m.steps_spec() == i,
            m.trace@ =~= tv.subrange(0, i as int),
            tv == trace@.map_values(|s: HashSet<usize>| s@),
        decreases trace.len() - i,
    {
        if !m.step(&trace[i]) {
            return None;
        }
        proof {
            assert(tv.subrange(0, i as int + 1) =~= tv.subrange(0, i as int).push(trace@[i as int]@));
        }
        i = i + 1;
    }
    proof {
        assert(tv.subrange(0, trace.len() as int) =~= tv);
    }
    let out = m.verdicts();
    let mut res: Vec<ExVerdict> = Vec::new();
    let mut j: usize = 0;
    while j < out.len()
        invariant
            j <= out.len(),
            res@ == out@.subrange(0, j as int),
        decreases out.len() - j,
    {
        res.push(out[j]);
        proof {
            assert(out@.subrange(0, j as int + 1) =~= out@.subrange(0, j as int).push(out@[j as int]));
        }
        j = j + 1;
    }
    proof {
        assert(out@.subrange(0, out.len() as int) =~= out@);
        crate::ring_sim::r2u2_ring_correct(*phi, tv);
    }
    Some(res)
}

} // verus!
