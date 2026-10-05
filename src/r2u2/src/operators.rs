//! The operators of one node (Isabelle `R2U2_Operators.thy`): what a node
//! does with its own queue and its children's queues in one pass.
use vstd::prelude::*;
use crate::verdict::*;
use crate::scq::*;
use crate::observer::*;

verus! {

/// `datatype LoopProgress`: where the engine is within a time step.
/// `FirstLoop` is the first pass; afterwards the engine repeats passes
/// while some node wrote something (`ReloopWithProgress`).
pub enum LoopProgress {
    FirstLoop,
    ReloopNoProgress,
    ReloopWithProgress,
}

/// `propagate_progress`: no progress only if no part made progress.
/// `FirstLoop` counts as progress (it is never passed on as such).
pub open spec fn propagate_progress(ps: Seq<LoopProgress>) -> LoopProgress
    decreases ps.len(),
{
    if ps.len() == 0 {
        LoopProgress::ReloopNoProgress
    } else if ps[0] == LoopProgress::ReloopNoProgress {
        propagate_progress(ps.subrange(1, ps.len() as int))
    } else {
        LoopProgress::ReloopWithProgress
    }
}

/// `LOAD Q verd progress`: leaves (True, False, Prop) write their verdict
/// for the current time step on the first pass only.
pub open spec fn load(q: Scq, verd: Verdict, progress: LoopProgress) -> (Scq, LoopProgress) {
    if progress == LoopProgress::FirstLoop {
        (scq_write(q, verd), LoopProgress::ReloopWithProgress)
    } else {
        (q, LoopProgress::ReloopNoProgress)
    }
}

/// `scq_write Q v ⦇next_time := time v + 1⦈` with progress: how every
/// operator emits a verdict (it then needs the step after it).
pub open spec fn write_advance(parent: Scq, v: Verdict) -> (Scq, LoopProgress) {
    (Scq { all_values: scq_write(parent, v).all_values, next_time: v.time + 1 }, LoopProgress::ReloopWithProgress)
}

/// `NOT parent_Q Q progress`: read the child's next entry and write its
/// negation with the same timestamp; then ask for the step after it.
pub open spec fn not_op(parent: Scq, child: Scq, progress: LoopProgress) -> (Scq, LoopProgress) {
    not_core(parent, scq_read(parent, child), progress)
}

/// NOT given what it read (`data`); shared by the history and ring models.
pub open spec fn not_core(parent: Scq, data: Option<Verdict>, progress: LoopProgress) -> (Scq, LoopProgress) {
    match data {
        Some(data) => write_advance(parent, Verdict { val: !data.val, time: data.time }),
        None => (parent, propagate_progress(seq![progress])),
    }
}

pub open spec fn min_nat(x: nat, y: nat) -> nat {
    if x <= y { x } else { y }
}

pub open spec fn max_nat(x: nat, y: nat) -> nat {
    if x >= y { x } else { y }
}

/// `AND parent_Q left_Q right_Q progress`: read both children at the
/// parent's `next_time`. Both true: true up to the earlier timestamp. Both
/// false: false up to the later one. Otherwise a false side decides:
/// false up to its timestamp. A true side alone must wait for the other.
pub open spec fn and_op(parent: Scq, left: Scq, right: Scq, progress: LoopProgress) -> (Scq, LoopProgress) {
    and_core(parent, scq_read(parent, left), scq_read(parent, right), progress)
}

/// AND given what it read from each side.
pub open spec fn and_core(parent: Scq, lread: Option<Verdict>, rread: Option<Verdict>, progress: LoopProgress)
    -> (Scq, LoopProgress)
{
    let wait = (parent, propagate_progress(seq![progress]));
    match (lread, rread) {
        (Some(l), Some(r)) =>
            if l.val && r.val {
                write_advance(parent, Verdict { val: true, time: min_nat(l.time, r.time) })
            } else if !l.val && !r.val {
                write_advance(parent, Verdict { val: false, time: max_nat(l.time, r.time) })
            } else if l.val {
                write_advance(parent, Verdict { val: false, time: r.time })
            } else {
                write_advance(parent, Verdict { val: false, time: l.time })
            },
        (Some(l), None) => if !l.val { write_advance(parent, Verdict { val: false, time: l.time }) } else { wait },
        (None, Some(r)) => if !r.val { write_advance(parent, Verdict { val: false, time: r.time }) } else { wait },
        (None, None) => wait,
    }
}

pub proof fn lemma_propagate_progress_2(p: LoopProgress, q: LoopProgress)
    ensures
        propagate_progress(seq![p, q]) == (if p == LoopProgress::ReloopNoProgress && q == LoopProgress::ReloopNoProgress {
            LoopProgress::ReloopNoProgress
        } else {
            LoopProgress::ReloopWithProgress
        }),
{
    reveal_with_fuel(propagate_progress, 3);
    assert(seq![p, q].subrange(1, 2) =~= seq![q]);
    assert(seq![q].subrange(1, 1) =~= Seq::<LoopProgress>::empty());
}

/// `UNTIL parent_Q left_Q right_Q parent_obs progress` (Alexis's pseudocode,
/// with Isabelle's fixes), for `φ U[lb,ub] ψ`. Child times are read from
/// `next_time`, which starts at `lb`; output time `i` concerns child times
/// `i + lb .. i + ub`.
/// - ψ true up to `t_r`: true up to output `t_r - lb`.
/// - ψ false, φ false up to `t_min`: false up to `t_min - lb`.
/// - ψ false up to `t_r` and the window of the next undecided output has
///   passed (`t_r ≥ prev + ub + 1`): false up to `t_r - ub`.
/// - ψ false, φ true, window not passed: skip ahead (`next_time := t_min + 1`)
///   without writing (and without reporting progress).
pub open spec fn until_op(parent: Scq, left: Scq, right: Scq, obs: Observer, progress: LoopProgress)
    -> (Scq, Observer, LoopProgress)
{
    until_core(parent, scq_read(parent, left), scq_read(parent, right), obs, progress)
}

/// UNTIL given what it read from each side.
pub open spec fn until_core(parent: Scq, lread: Option<Verdict>, rread: Option<Verdict>, obs: Observer,
    progress: LoopProgress) -> (Scq, Observer, LoopProgress)
{
    let lb = obs.lower_bound;
    let ub = obs.upper_bound;
    let wait = propagate_progress(seq![progress]);
    let elapsed_from = match obs.prev_verdict {
        None => ub,
        Some(prev) => prev.time + ub + 1,
    };
    match rread {
        None => (parent, obs, wait),
        Some(r) =>
            if r.val {
                let v = Verdict { val: true, time: (r.time - lb) as nat };
                (Scq { all_values: scq_write(parent, v).all_values, next_time: r.time + 1 },
                    Observer { prev_verdict: Some(v), ..obs }, LoopProgress::ReloopWithProgress)
            } else {
                match lread {
                    Some(l) => {
                        let t_min = min_nat(l.time, r.time);
                        if !l.val {
                            let v = Verdict { val: false, time: (t_min - lb) as nat };
                            (Scq { all_values: scq_write(parent, v).all_values, next_time: t_min + 1 },
                                Observer { prev_verdict: Some(v), ..obs }, LoopProgress::ReloopWithProgress)
                        } else if r.time >= elapsed_from {
                            let v = Verdict { val: false, time: (r.time - ub) as nat };
                            (Scq { all_values: scq_write(parent, v).all_values, next_time: max_nat(t_min + 1, v.time + lb + 1) },
                                Observer { prev_verdict: Some(v), ..obs }, LoopProgress::ReloopWithProgress)
                        } else {
                            // As Isabelle and Rust: no progress is reported, although `next_time`
                            // moved (see promptness.rs for why verdicts are still on time).
                            (Scq { all_values: parent.all_values, next_time: t_min + 1 }, obs, wait)
                        }
                    },
                    None =>
                        if r.time >= elapsed_from {
                            let v = Verdict { val: false, time: (r.time - ub) as nat };
                            (Scq { all_values: scq_write(parent, v).all_values, next_time: max_nat(parent.next_time, v.time + lb + 1) },
                                Observer { prev_verdict: Some(v), ..obs }, LoopProgress::ReloopWithProgress)
                        } else {
                            (parent, obs, wait)
                        },
                }
            },
    }
}

pub proof fn lemma_propagate_progress_3(p: LoopProgress, q: LoopProgress, r: LoopProgress)
    ensures
        propagate_progress(seq![p, q, r]) == (if p == LoopProgress::ReloopNoProgress && q == LoopProgress::ReloopNoProgress
            && r == LoopProgress::ReloopNoProgress {
            LoopProgress::ReloopNoProgress
        } else {
            LoopProgress::ReloopWithProgress
        }),
{
    reveal_with_fuel(propagate_progress, 4);
    assert(seq![p, q, r].subrange(1, 3) =~= seq![q, r]);
    lemma_propagate_progress_2(q, r);
}

pub proof fn lemma_propagate_progress_1(p: LoopProgress)
    ensures
        propagate_progress(seq![p]) == (if p == LoopProgress::ReloopNoProgress {
            LoopProgress::ReloopNoProgress
        } else {
            LoopProgress::ReloopWithProgress
        }),
{
    reveal_with_fuel(propagate_progress, 2);
    assert(seq![p].subrange(1, 1) =~= Seq::<LoopProgress>::empty());
}

} // verus!
