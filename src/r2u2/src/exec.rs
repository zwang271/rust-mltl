//! Executable ring buffers and operators, each proved equal to its spec in
//! `ring.rs` / `operators.rs` / `ring_engine.rs`. Times are `usize`;
//! arithmetic is checked, and an operator that would overflow returns
//! `None` (the monitor then stops with an error). Whenever a result is
//! returned it is exactly the spec's.
use vstd::prelude::*;
use crate::verdict::*;
use crate::scq::*;
use crate::observer::*;
use crate::operators::*;
use crate::ring::*;
use crate::ring_engine::*;

verus! {

// ---------------------------------------------------------------------------
// Verdicts
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExVerdict {
    pub val: bool,
    pub time: usize,
}

impl ExVerdict {
    pub open spec fn vv(self) -> Verdict {
        Verdict { val: self.val, time: self.time as nat }
    }
}

pub open spec fn opt_vv(o: Option<ExVerdict>) -> Option<Verdict> {
    match o {
        Some(v) => Some(v.vv()),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Rings
// ---------------------------------------------------------------------------

pub struct ExRing {
    pub slots: Vec<Option<ExVerdict>>,
    pub write_ptr: usize,
}

impl ExRing {
    pub open spec fn view(&self) -> Ring {
        Ring { slots: self.slots@.map_values(|o: Option<ExVerdict>| opt_vv(o)), write_ptr: self.write_ptr as nat }
    }

    pub open spec fn wf(&self) -> bool {
        self.slots.len() > 0 && self.write_ptr < self.slots.len()
    }

    /// `empty_ring size`
    pub fn new(size: usize) -> (r: ExRing)
        requires
            size > 0,
        ensures
            r.view() == empty_ring(size as nat),
            r.wf(),
    {
        let mut slots: Vec<Option<ExVerdict>> = Vec::new();
        let mut i: usize = 0;
        while i < size
            invariant
                i <= size,
                slots.len() == i,
                forall|k: int| 0 <= k < i ==> slots[k] == None::<ExVerdict>,
            decreases size - i,
        {
            slots.push(None);
            i = i + 1;
        }
        let r = ExRing { slots, write_ptr: 0 };
        assert(r.view().slots =~= empty_ring(size as nat).slots);
        r
    }

    /// `ring_write` (Isabelle `scq_write`, ring part).
    pub fn write(&mut self, v: ExVerdict)
        requires
            old(self).wf(),
        ensures
            final(self).view() == ring_write(old(self).view(), v.vv()),
            final(self).wf(),
            final(self).slots.len() == old(self).slots.len(),
    {
        let n = self.slots.len();
        let wp = self.write_ptr;
        let prev = if wp == 0 { n - 1 } else { wp - 1 };
        let same = match self.slots[prev] {
            Some(pv) => pv.val == v.val,
            None => false,
        };
        proof {
            let ghost r = old(self).view();
            assert(prev as nat == circ_minus(r.write_ptr, r.slots.len()));
            assert(r.slots[prev as int] == opt_vv(old(self).slots[prev as int]));
        }
        if same {
            self.slots.set(prev, Some(v));
            proof {
                assert(self.view().slots =~= ring_write(old(self).view(), v.vv()).slots);
            }
        } else {
            self.slots.set(wp, Some(v));
            self.write_ptr = if wp + 1 == n { 0 } else { wp + 1 };
            proof {
                if wp + 1 < n {
                    vstd::arithmetic::div_mod::lemma_small_mod((wp + 1) as nat, n as nat);
                } else {
                    vstd::arithmetic::div_mod::lemma_mod_self_0(n as int);
                }
                assert(self.view().slots =~= ring_write(old(self).view(), v.vv()).slots);
            }
        }
    }

    /// `ring_read` (Isabelle `scq_read_aux`): the entry and the new pointer.
    pub fn read(&self, rd: usize, tau: usize) -> (res: (Option<ExVerdict>, usize))
        requires
            self.wf(),
        ensures
            (opt_vv(res.0), res.1 as nat) == ring_read(self.view(), rd as nat, tau as nat),
    {
        let n = self.slots.len();
        let ghost r = self.view();
        let mut cur = rd;
        let mut fuel = n;
        while true
            invariant
                n == self.slots.len(),
                r == self.view(),
                self.wf(),
                ring_scan(r, cur as nat, tau as nat, fuel as nat) == ring_read(r, rd as nat, tau as nat),
            decreases fuel,
        {
            if fuel == 0 || cur >= n || self.write_ptr >= n || (self.slots[cur].is_none() && cur == 0) {
                return (None, cur);
            }
            let s = self.slots[cur];
            assert(r.slots[cur as int] == opt_vv(s));
            match s {
                Some(v) => {
                    if v.time >= tau {
                        return (Some(v), cur);
                    }
                },
                None => {},
            }
            let nxt = if cur + 1 == n { 0 } else { cur + 1 };
            proof {
                if cur + 1 < n {
                    vstd::arithmetic::div_mod::lemma_small_mod((cur + 1) as nat, n as nat);
                } else {
                    vstd::arithmetic::div_mod::lemma_mod_self_0(n as int);
                }
                assert(nxt as nat == circ_succ(cur as nat, n as nat));
            }
            if nxt == self.write_ptr {
                return (None, cur);
            }
            cur = nxt;
            fuel = fuel - 1;
        }
        (None, cur)
    }
}

// ---------------------------------------------------------------------------
// Nodes
// ---------------------------------------------------------------------------

pub struct ExObserver {
    pub lower_bound: usize,
    pub upper_bound: usize,
    pub prev_verdict: Option<ExVerdict>,
}

impl ExObserver {
    pub open spec fn view(&self) -> Observer {
        Observer { lower_bound: self.lower_bound as nat, upper_bound: self.upper_bound as nat, last_edge: None,
            prev_verdict: opt_vv(self.prev_verdict) }
    }
}

/// A node: ring, `next_time`, read pointers, observer; `all_values` is ghost.
pub struct ExNode {
    pub ring: ExRing,
    pub next_time: usize,
    pub rd_left: usize,
    pub rd_right: usize,
    pub obs: ExObserver,
    pub all_values: Ghost<Seq<Verdict>>,
}

impl ExNode {
    pub open spec fn view(&self) -> RNode {
        RNode { ring: self.ring.view(), all_values: self.all_values@, next_time: self.next_time as nat,
            rd_left: self.rd_left as nat, rd_right: self.rd_right as nat, obs: self.obs.view() }
    }

    pub open spec fn wf(&self) -> bool {
        self.ring.wf()
    }
}

pub fn progress_rlnp(p: &LoopProgress) -> (r: bool)
    ensures
        r == (*p == LoopProgress::ReloopNoProgress),
{
    match p {
        LoopProgress::ReloopNoProgress => true,
        _ => false,
    }
}

/// `propagate_progress [p]`
pub fn propagate1(p: &LoopProgress) -> (r: LoopProgress)
    ensures
        r == propagate_progress(seq![*p]),
{
    proof { lemma_propagate_progress_1(*p); }
    if progress_rlnp(p) { LoopProgress::ReloopNoProgress } else { LoopProgress::ReloopWithProgress }
}

/// `propagate_progress [p, q]`
pub fn propagate2(p: &LoopProgress, q: &LoopProgress) -> (r: LoopProgress)
    ensures
        r == propagate_progress(seq![*p, *q]),
{
    proof { lemma_propagate_progress_2(*p, *q); }
    if progress_rlnp(p) && progress_rlnp(q) { LoopProgress::ReloopNoProgress } else { LoopProgress::ReloopWithProgress }
}

/// `propagate_progress [p, q, r]`
pub fn propagate3(p: &LoopProgress, q: &LoopProgress, r: &LoopProgress) -> (res: LoopProgress)
    ensures
        res == propagate_progress(seq![*p, *q, *r]),
{
    proof { lemma_propagate_progress_3(*p, *q, *r); }
    if progress_rlnp(p) && progress_rlnp(q) && progress_rlnp(r) {
        LoopProgress::ReloopNoProgress
    } else {
        LoopProgress::ReloopWithProgress
    }
}

pub fn copy_progress(p: &LoopProgress) -> (r: LoopProgress)
    ensures
        r == *p,
{
    match p {
        LoopProgress::FirstLoop => LoopProgress::FirstLoop,
        LoopProgress::ReloopNoProgress => LoopProgress::ReloopNoProgress,
        LoopProgress::ReloopWithProgress => LoopProgress::ReloopWithProgress,
    }
}

/// What an operator call did: its progress and the verdict it wrote (if any).
pub open spec fn op_done(old_d: RNode, new_d: RNode, q: Scq, wrote: Option<ExVerdict>) -> bool {
    &&& new_d == store(old_d, q)
    &&& wrote.is_some() ==> q.all_values == old_d.all_values.push(wrote.unwrap().vv())
    &&& wrote.is_none() ==> q.all_values == old_d.all_values
}

/// Write `v` (ring + ghost history) and set `next_time` (when `advance`).
fn write_node(d: &mut ExNode, v: ExVerdict, next: usize, advance: bool)
    requires
        old(d).wf(),
    ensures
        final(d).wf(),
        final(d).view() == store(old(d).view(), Scq {
            all_values: old(d).all_values@.push(v.vv()),
            next_time: if advance { next as nat } else { old(d).next_time as nat },
        }),
{
    d.ring.write(v);
    d.all_values = Ghost(d.all_values@.push(v.vv()));
    if advance {
        d.next_time = next;
    }
}

/// `LOAD`
pub fn load_ex(d: &mut ExNode, v: ExVerdict, progress: &LoopProgress) -> (r: (LoopProgress, Option<ExVerdict>))
    requires
        old(d).wf(),
    ensures
        final(d).wf(),
        r.0 == load(rscq(old(d).view()), v.vv(), *progress).1,
        op_done(old(d).view(), final(d).view(), load(rscq(old(d).view()), v.vv(), *progress).0, r.1),
{
    match progress {
        LoopProgress::FirstLoop => {
            write_node(d, v, 0, false);
            (LoopProgress::ReloopWithProgress, Some(v))
        },
        _ => {
            assert(store(old(d).view(), rscq(old(d).view())) == old(d).view());
            (LoopProgress::ReloopNoProgress, None)
        },
    }
}

/// `NOT` given what it read.
pub fn not_ex(d: &mut ExNode, data: Option<ExVerdict>, progress: &LoopProgress) -> (r: Option<(LoopProgress, Option<ExVerdict>)>)
    requires
        old(d).wf(),
    ensures
        final(d).wf(),
        r.is_some() ==> ({
            let (q, p) = not_core(rscq(old(d).view()), opt_vv(data), *progress);
            r.unwrap().0 == p && op_done(old(d).view(), final(d).view(), q, r.unwrap().1)
        }),
{
    match data {
        Some(x) => {
            let v = ExVerdict { val: !x.val, time: x.time };
            let next = x.time.checked_add(1)?;
            write_node(d, v, next, true);
            Some((LoopProgress::ReloopWithProgress, Some(v)))
        },
        None => {
            assert(store(old(d).view(), rscq(old(d).view())) == old(d).view());
            Some((propagate1(progress), None))
        },
    }
}

/// `AND` given what it read.
pub fn and_ex(d: &mut ExNode, lread: Option<ExVerdict>, rread: Option<ExVerdict>, progress: &LoopProgress)
    -> (r: Option<(LoopProgress, Option<ExVerdict>)>)
    requires
        old(d).wf(),
    ensures
        final(d).wf(),
        r.is_some() ==> ({
            let (q, p) = and_core(rscq(old(d).view()), opt_vv(lread), opt_vv(rread), *progress);
            r.unwrap().0 == p && op_done(old(d).view(), final(d).view(), q, r.unwrap().1)
        }),
{
    let v: Option<ExVerdict> = match (lread, rread) {
        (Some(l), Some(r)) =>
            if l.val && r.val {
                Some(ExVerdict { val: true, time: if l.time <= r.time { l.time } else { r.time } })
            } else if !l.val && !r.val {
                Some(ExVerdict { val: false, time: if l.time >= r.time { l.time } else { r.time } })
            } else if l.val {
                Some(ExVerdict { val: false, time: r.time })
            } else {
                Some(ExVerdict { val: false, time: l.time })
            },
        (Some(l), None) => if !l.val { Some(ExVerdict { val: false, time: l.time }) } else { None },
        (None, Some(r)) => if !r.val { Some(ExVerdict { val: false, time: r.time }) } else { None },
        (None, None) => None,
    };
    match v {
        Some(v) => {
            let next = v.time.checked_add(1)?;
            write_node(d, v, next, true);
            Some((LoopProgress::ReloopWithProgress, Some(v)))
        },
        None => {
            assert(store(old(d).view(), rscq(old(d).view())) == old(d).view());
            Some((propagate1(progress), None))
        },
    }
}

/// `UNTIL` given what it read.
pub fn until_ex(d: &mut ExNode, lread: Option<ExVerdict>, rread: Option<ExVerdict>, progress: &LoopProgress)
    -> (r: Option<(LoopProgress, Option<ExVerdict>)>)
    requires
        old(d).wf(),
    ensures
        final(d).wf(),
        final(d).rd_left == old(d).rd_left && final(d).rd_right == old(d).rd_right,
        r.is_some() ==> ({
            let (q, o, p) = until_core(rscq(old(d).view()), opt_vv(lread), opt_vv(rread), old(d).obs.view(), *progress);
            &&& r.unwrap().0 == p
            &&& final(d).obs.view() == o
            &&& op_done(RNode { obs: o, ..old(d).view() }, final(d).view(), q, r.unwrap().1)
        }),
{
    let lb = d.obs.lower_bound;
    let ub = d.obs.upper_bound;
    let elapsed_from: Option<usize> = match d.obs.prev_verdict {
        None => Some(ub),
        Some(prev) => match prev.time.checked_add(ub) {
            Some(x) => x.checked_add(1),
            None => None,
        },
    };
    let ghost od = old(d).view();
    let ghost ef = match od.obs.prev_verdict { None => od.obs.upper_bound, Some(prev) => prev.time + od.obs.upper_bound + 1 };
    assert(elapsed_from.is_some() ==> elapsed_from.unwrap() == ef);
    assert(elapsed_from.is_none() ==> ef > usize::MAX);
    match rread {
        None => {
            assert(store(od, rscq(od)) == od);
            assert(RNode { obs: od.obs, ..od } == od);
            Some((propagate1(progress), None))
        },
        Some(r) => {
            if r.val {
                let t = r.time.checked_sub(lb)?;
                let next = r.time.checked_add(1)?;
                let v = ExVerdict { val: true, time: t };
                write_node(d, v, next, true);
                d.obs.prev_verdict = Some(v);
                Some((LoopProgress::ReloopWithProgress, Some(v)))
            } else {
                match lread {
                    Some(l) => {
                        let t_min = if l.time <= r.time { l.time } else { r.time };
                        let t_min1 = t_min.checked_add(1)?;
                        if !l.val {
                            let t = t_min.checked_sub(lb)?;
                            let v = ExVerdict { val: false, time: t };
                            write_node(d, v, t_min1, true);
                            d.obs.prev_verdict = Some(v);
                            Some((LoopProgress::ReloopWithProgress, Some(v)))
                        } else if elapsed_from.is_some() && r.time >= elapsed_from.unwrap() {
                            let t = r.time.checked_sub(ub)?;
                            let x = t.checked_add(lb)?.checked_add(1)?;
                            let next = if t_min1 >= x { t_min1 } else { x };
                            let v = ExVerdict { val: false, time: t };
                            write_node(d, v, next, true);
                            d.obs.prev_verdict = Some(v);
                            Some((LoopProgress::ReloopWithProgress, Some(v)))
                        } else {
                            d.next_time = t_min1;
                            assert(d.view() == store(RNode { obs: od.obs, ..od },
                                Scq { all_values: od.all_values, next_time: t_min1 as nat }));
                            Some((propagate1(progress), None))
                        }
                    },
                    None => {
                        if elapsed_from.is_some() && r.time >= elapsed_from.unwrap() {
                            let t = r.time.checked_sub(ub)?;
                            let x = t.checked_add(lb)?.checked_add(1)?;
                            let next = if d.next_time >= x { d.next_time } else { x };
                            let v = ExVerdict { val: false, time: t };
                            write_node(d, v, next, true);
                            d.obs.prev_verdict = Some(v);
                            Some((LoopProgress::ReloopWithProgress, Some(v)))
                        } else {
                            assert(store(od, rscq(od)) == od);
                            assert(RNode { obs: od.obs, ..od } == od);
                            Some((propagate1(progress), None))
                        }
                    },
                }
            }
        },
    }
}

} // verus!
