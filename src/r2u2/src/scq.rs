//! Shared connection queues (Isabelle `R2U2_SCQ.thy`), stage 1: a queue is
//! the full history of its writes (Isabelle's ghost field `all_values`).
//!
//! The ring buffer of the real algorithm (`scq_values`, `write_ptr`, read
//! pointers) is not modelled yet. What an unbounded ring would hold is
//! [`scq_entries`], the compaction of the history; reads search it.
use vstd::prelude::*;
use crate::verdict::*;

verus! {

/// `record SCQ`, history part. `next_time` is, as in Isabelle and R2U2, the
/// first time step this queue's *owner* still needs from its children.
pub struct Scq {
    pub all_values: Seq<Verdict>,
    pub next_time: nat,
}

/// `initial_SCQ sz tau` (no size: the history is unbounded).
pub open spec fn initial_scq(tau: nat) -> Scq {
    Scq { all_values: Seq::empty(), next_time: tau }
}

/// The entries an unbounded R2U2 queue holds: the compacted history.
pub open spec fn scq_entries(q: Scq) -> Seq<Verdict> {
    compact(q.all_values)
}

/// `scq_write Q v`: record the write (compaction happens in [`scq_entries`]).
pub open spec fn scq_write(q: Scq, v: Verdict) -> Scq {
    Scq { all_values: q.all_values.push(v), next_time: q.next_time }
}

/// `scq_read parent_Q child_Q LR`: the first stored entry of the child at or
/// after the parent's `next_time`, if there is one (`undecidedV` in Isabelle
/// is `None`). Without a ring there is no read pointer to update.
pub open spec fn scq_read(parent: Scq, child: Scq) -> Option<Verdict> {
    first_from(scq_entries(child), parent.next_time)
}

/// A read gives an entry at or after `next_time`, within what the child has
/// written, whose value holds for every time from `next_time` to its own.
pub proof fn lemma_scq_read_sound(parent: Scq, child: Scq)
    requires
        strictly_increasing(child.all_values),
        scq_read(parent, child).is_some(),
    ensures
        ({
            let e = scq_read(parent, child).unwrap();
            &&& parent.next_time <= e.time < next_after(child.all_values)
            &&& forall|j: nat| parent.next_time <= j <= e.time ==>
                    #[trigger] value_at(child.all_values, j) == Some(e.val)
        }),
{
    let h = child.all_values;
    let c = compact(h);
    let tau = parent.next_time;
    let e = scq_read(parent, child).unwrap();
    lemma_compact(h);
    lemma_first_from_props(c, tau);
    let k = choose|k: int| 0 <= k < c.len() && c[k] == e;
    if k < c.len() - 1 {
        assert(c[k].time < c[c.len() - 1].time);
    }
    assert forall|j: nat| tau <= j <= e.time implies #[trigger] value_at(h, j) == Some(e.val) by {
        lemma_first_from_range(c, tau, j);
        lemma_compact_value_at(h, j);
    }
}

/// A read finds something exactly when the child has written past `next_time`.
pub proof fn lemma_scq_read_some(parent: Scq, child: Scq)
    requires
        strictly_increasing(child.all_values),
    ensures
        scq_read(parent, child).is_some() <==> parent.next_time < next_after(child.all_values),
{
    lemma_compact(child.all_values);
    lemma_first_from_some(compact(child.all_values), parent.next_time);
}

} // verus!
