//! Verdicts and verdict streams (Isabelle `R2U2_Verdicts.thy`).
//!
//! A queue's history is a list of verdicts with strictly increasing
//! timestamps. Entry `<v, t>` says "the value is `v` at every time after the
//! previous entry's timestamp, up to and including `t`" (aggregation).
//! [`value_at`] reads that meaning back; [`deaggregate`] expands a stream
//! into one verdict per time step, as Isabelle does; [`compact`] is R2U2's
//! write-time compaction (merge with the previous entry when the value is
//! the same).
use vstd::prelude::*;
use mltl_core::mltl::*;

verus! {

// ---------------------------------------------------------------------------
// Verdicts  (record verdict = val, time)
// ---------------------------------------------------------------------------

/// `<v, t>`: Isabelle `record verdict = val :: SCQ_values, time :: nat`.
///
/// Isabelle's third value `Undecided` (with `undecidedV = <Undecided, 0>`)
/// marks "no verdict" and empty queue slots; here that is `Option::None`
/// and the value is a `bool` (`True_SCQ`/`False_SCQ`).
pub struct Verdict {
    pub val: bool,
    pub time: nat,
}

/// `strictly_increasing_verdict_list L` (Isabelle states it on consecutive
/// timestamps; pairwise is equivalent and easier to use).
pub open spec fn strictly_increasing(h: Seq<Verdict>) -> bool {
    forall|i: int, k: int| #![trigger h[i], h[k]] 0 <= i < k < h.len() ==> h[i].time < h[k].time
}

/// The first time step the stream does not yet cover: `time (last L) + 1`,
/// or 0 for the empty stream.
pub open spec fn next_after(h: Seq<Verdict>) -> nat {
    if h.len() == 0 { 0 } else { h.last().time + 1 }
}

/// `is_aggregated L`: neighbouring entries have different values
/// (`successively flip_pred`).
pub open spec fn is_aggregated(h: Seq<Verdict>) -> bool {
    forall|i: int| 0 <= i < h.len() - 1 ==> #[trigger] h[i].val != h[i + 1].val
}

// ---------------------------------------------------------------------------
// Reading a stream at a time step
// ---------------------------------------------------------------------------

/// Index of the first entry with timestamp `>= j` (`s.len()` if none).
pub open spec fn first_idx(s: Seq<Verdict>, j: nat) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else if s[0].time >= j {
        0
    } else {
        1 + first_idx(s.subrange(1, s.len() as int), j)
    }
}

/// The first entry with timestamp `>= j`. This is what a reader asking for
/// time `j` gets from a queue (Isabelle `scq_read`, on an unbounded queue).
pub open spec fn first_from(s: Seq<Verdict>, j: nat) -> Option<Verdict> {
    if first_idx(s, j) < s.len() {
        Some(s[first_idx(s, j) as int])
    } else {
        None
    }
}

/// The value the stream gives time step `j`, if it covers `j`.
pub open spec fn value_at(h: Seq<Verdict>, j: nat) -> Option<bool> {
    match first_from(h, j) {
        Some(v) => Some(v.val),
        None => None,
    }
}

pub proof fn lemma_first_idx(s: Seq<Verdict>, j: nat)
    ensures
        first_idx(s, j) <= s.len(),
        forall|i: int| 0 <= i < first_idx(s, j) ==> #[trigger] s[i].time < j,
        first_idx(s, j) < s.len() ==> s[first_idx(s, j) as int].time >= j,
    decreases s.len(),
{
    if s.len() > 0 && s[0].time < j {
        let t = s.subrange(1, s.len() as int);
        lemma_first_idx(t, j);
        assert forall|i: int| 0 <= i < first_idx(s, j) implies #[trigger] s[i].time < j by {
            if i > 0 {
                assert(s[i] == t[i - 1]);
            }
        }
        if first_idx(s, j) < s.len() {
            assert(s[first_idx(s, j) as int] == t[first_idx(t, j) as int]);
        }
    }
}

/// `first_idx` is the unique index with its two properties.
pub proof fn lemma_first_idx_unique(s: Seq<Verdict>, j: nat, k: nat)
    requires
        k <= s.len(),
        forall|i: int| 0 <= i < k ==> #[trigger] s[i].time < j,
        k < s.len() ==> s[k as int].time >= j,
    ensures
        first_idx(s, j) == k,
{
    lemma_first_idx(s, j);
    let f = first_idx(s, j);
    if f < k {
        assert(s[f as int].time < j);
    }
    if k < f {
        assert(s[k as int].time < j);
    }
}

/// A strictly increasing stream covers exactly the times before `next_after`.
pub proof fn lemma_first_from_some(s: Seq<Verdict>, j: nat)
    requires
        strictly_increasing(s),
    ensures
        first_from(s, j).is_some() <==> j < next_after(s),
{
    lemma_first_idx(s, j);
    if s.len() > 0 {
        if j < next_after(s) {
            if first_idx(s, j) == s.len() {
                assert(s[s.len() - 1].time < j);
            }
        } else {
            assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i].time < j by {
                if i < s.len() - 1 {
                    assert(s[i].time < s[s.len() - 1].time);
                }
            }
            lemma_first_idx_unique(s, j, s.len());
        }
    }
}

/// What a reader gets is in the stream, at or after `j`, and the first such.
pub proof fn lemma_first_from_props(s: Seq<Verdict>, j: nat)
    requires
        first_from(s, j).is_some(),
    ensures
        first_from(s, j).unwrap().time >= j,
        exists|k: int| 0 <= k < s.len() && s[k] == first_from(s, j).unwrap(),
{
    lemma_first_idx(s, j);
    assert(s[first_idx(s, j) as int] == first_from(s, j).unwrap());
}

/// Appending: earlier answers stay; times not yet covered go to the new entry.
pub proof fn lemma_first_from_push(s: Seq<Verdict>, v: Verdict, j: nat)
    ensures
        first_from(s.push(v), j) == (match first_from(s, j) {
            Some(e) => Some(e),
            None => if v.time >= j { Some(v) } else { None },
        }),
{
    let t = s.push(v);
    lemma_first_idx(s, j);
    let f = first_idx(s, j);
    if f < s.len() {
        assert forall|i: int| 0 <= i < f implies #[trigger] t[i].time < j by {
            assert(t[i] == s[i]);
        }
        assert(t[f as int] == s[f as int]);
        lemma_first_idx_unique(t, j, f);
    } else {
        assert forall|i: int| 0 <= i < s.len() implies #[trigger] t[i].time < j by {
            assert(t[i] == s[i]);
        }
        if v.time >= j {
            lemma_first_idx_unique(t, j, s.len());
        } else {
            assert forall|i: int| 0 <= i < t.len() implies #[trigger] t[i].time < j by {
                if i < s.len() {
                    assert(t[i] == s[i]);
                }
            }
            lemma_first_idx_unique(t, j, t.len());
        }
    }
}

/// Appending to a strictly increasing stream keeps every value it already gave.
pub proof fn lemma_value_at_push(s: Seq<Verdict>, v: Verdict, j: nat)
    ensures
        value_at(s, j).is_some() ==> value_at(s.push(v), j) == value_at(s, j),
        value_at(s, j).is_none() ==> value_at(s.push(v), j) == (if v.time >= j { Some(v.val) } else { None }),
{
    lemma_first_from_push(s, v, j);
}

/// If the first entry at or after `j` is `e`, it is also the first at or
/// after every `j'` between `j` and `e.time`: the whole range has `e`'s value.
pub proof fn lemma_first_from_range(s: Seq<Verdict>, j: nat, j2: nat)
    requires
        first_from(s, j).is_some(),
        j <= j2 <= first_from(s, j).unwrap().time,
    ensures
        first_from(s, j2) == first_from(s, j),
{
    lemma_first_idx(s, j);
    let f = first_idx(s, j);
    assert forall|i: int| 0 <= i < f implies #[trigger] s[i].time < j2 by {}
    lemma_first_idx_unique(s, j2, f);
}

// ---------------------------------------------------------------------------
// Compaction  (the overwrite step of scq_write, on an unbounded queue)
// ---------------------------------------------------------------------------

/// What an unbounded R2U2 queue holds after the writes `h`: each write with
/// the same value as the last stored entry overwrites it (Isabelle
/// `scq_write`, compaction branch); otherwise it is appended.
pub open spec fn compact(h: Seq<Verdict>) -> Seq<Verdict>
    decreases h.len(),
{
    if h.len() == 0 {
        Seq::empty()
    } else {
        let c = compact(h.drop_last());
        let v = h.last();
        if c.len() > 0 && c.last().val == v.val {
            c.update(c.len() - 1, v)
        } else {
            c.push(v)
        }
    }
}

/// Shape of a compacted stream: same last entry, strictly increasing,
/// aggregated, no longer than the history.
pub proof fn lemma_compact(h: Seq<Verdict>)
    requires
        strictly_increasing(h),
    ensures
        compact(h).len() <= h.len(),
        compact(h).len() == 0 <==> h.len() == 0,
        h.len() > 0 ==> compact(h).last() == h.last(),
        next_after(compact(h)) == next_after(h),
        strictly_increasing(compact(h)),
        is_aggregated(compact(h)),
    decreases h.len(),
{
    if h.len() > 0 {
        let h0 = h.drop_last();
        let v = h.last();
        assert(strictly_increasing(h0));
        lemma_compact(h0);
        let c0 = compact(h0);
        let c = compact(h);
        if h0.len() > 0 {
            assert(h0.last() == h[h.len() - 2]);
            assert(h0.last().time < v.time);
        }
        if c0.len() > 0 && c0.last().val == v.val {
            assert(c == c0.update(c0.len() - 1, v));
            assert forall|i: int, k: int| #![trigger c[i], c[k]] 0 <= i < k < c.len() implies c[i].time < c[k].time by {
                if k < c.len() - 1 {
                    assert(c[i] == c0[i] && c[k] == c0[k]);
                } else {
                    assert(c[i] == c0[i]);
                    if i < c0.len() - 1 {
                        assert(c0[i].time < c0[c0.len() - 1].time);
                    }
                }
            }
            assert forall|i: int| 0 <= i < c.len() - 1 implies #[trigger] c[i].val != c[i + 1].val by {
                assert(c[i] == c0[i]);
                if i + 1 < c.len() - 1 {
                    assert(c[i + 1] == c0[i + 1]);
                }
            }
        } else {
            assert(c == c0.push(v));
            assert forall|i: int, k: int| #![trigger c[i], c[k]] 0 <= i < k < c.len() implies c[i].time < c[k].time by {
                assert(c[i] == c0[i]);
                if k < c0.len() {
                    assert(c[k] == c0[k]);
                } else if i < c0.len() - 1 {
                    assert(c0[i].time < c0[c0.len() - 1].time);
                }
            }
            assert forall|i: int| 0 <= i < c.len() - 1 implies #[trigger] c[i].val != c[i + 1].val by {
                assert(c[i] == c0[i]);
                if i + 1 < c0.len() {
                    assert(c[i + 1] == c0[i + 1]);
                }
            }
        }
    }
}

/// Compaction keeps the meaning: a compacted stream gives every time step
/// the same value as the full history.
pub proof fn lemma_compact_value_at(h: Seq<Verdict>, j: nat)
    requires
        strictly_increasing(h),
    ensures
        value_at(compact(h), j) == value_at(h, j),
    decreases h.len(),
{
    if h.len() > 0 {
        let h0 = h.drop_last();
        let v = h.last();
        assert(strictly_increasing(h0));
        assert(h0.push(v) =~= h);
        lemma_compact(h0);
        lemma_compact(h);
        lemma_compact_value_at(h0, j);
        lemma_value_at_push(h0, v, j);
        let c0 = compact(h0);
        let c = compact(h);
        if h0.len() > 0 {
            assert(h0.last() == h[h.len() - 2]);
        }
        if c0.len() > 0 && c0.last().val == v.val {
            let last = c0.len() - 1;
            assert(c == c0.update(last, v));
            lemma_first_from_some(c0, j);
            lemma_first_from_some(h0, j);
            lemma_first_from_some(c, j);
            lemma_first_idx(c0, j);
            if j < next_after(c0) {
                let k = first_idx(c0, j);
                assert forall|i: int| 0 <= i < k implies #[trigger] c[i].time < j by {
                    assert(c[i] == c0[i]);
                }
                if k < last {
                    assert(c[k as int] == c0[k as int]);
                }
                lemma_first_idx_unique(c, j, k);
            } else if j <= v.time {
                assert forall|i: int| 0 <= i < last implies #[trigger] c[i].time < j by {
                    assert(c[i] == c0[i]);
                    assert(c0[i].time < c0[last as int].time);
                }
                lemma_first_idx_unique(c, j, last as nat);
            }
        } else {
            assert(c == c0.push(v));
            lemma_value_at_push(c0, v, j);
        }
    }
}

// ---------------------------------------------------------------------------
// Deaggregation  (deaggregate_aux, deaggregate)
// ---------------------------------------------------------------------------

/// `deaggregate_aux L last_time`: expand each entry `<v, t>` into one
/// verdict per time step from `last_time` to `t`.
pub open spec fn deaggregate_aux(l: Seq<Verdict>, last_time: nat) -> Seq<Verdict>
    decreases l.len(),
{
    if l.len() == 0 {
        Seq::empty()
    } else {
        Seq::new(nat_sub(l[0].time + 1, last_time), |i: int| Verdict { val: l[0].val, time: (last_time + i) as nat })
            + deaggregate_aux(l.subrange(1, l.len() as int), l[0].time + 1)
    }
}

/// `deaggregate V = deaggregate_aux V 0`
pub open spec fn deaggregate(l: Seq<Verdict>) -> Seq<Verdict> {
    deaggregate_aux(l, 0)
}

pub proof fn lemma_deaggregate_aux(l: Seq<Verdict>, s: nat)
    requires
        strictly_increasing(l),
        l.len() > 0 ==> l[0].time >= s,
    ensures
        deaggregate_aux(l, s).len() == nat_sub(next_after(l), s),
        forall|i: int| 0 <= i < deaggregate_aux(l, s).len() ==>
            (#[trigger] deaggregate_aux(l, s)[i]).time == s + i
            && value_at(l, (s + i) as nat) == Some(deaggregate_aux(l, s)[i].val),
    decreases l.len(),
{
    if l.len() > 0 {
        let t = l.subrange(1, l.len() as int);
        let s2 = l[0].time + 1;
        assert(strictly_increasing(t)) by {
            assert forall|i: int, k: int| #![trigger t[i], t[k]] 0 <= i < k < t.len() implies t[i].time < t[k].time by {
                assert(t[i] == l[i + 1] && t[k] == l[k + 1]);
            }
        }
        if t.len() > 0 {
            assert(t[0] == l[1]);
            assert(t.last() == l.last());
        }
        lemma_deaggregate_aux(t, s2);
        let r = nat_sub(l[0].time + 1, s);
        let front = Seq::new(r, |i: int| Verdict { val: l[0].val, time: (s + i) as nat });
        let d = deaggregate_aux(l, s);
        assert(d == front + deaggregate_aux(t, s2));
        assert forall|i: int| 0 <= i < d.len() implies
            (#[trigger] d[i]).time == s + i && value_at(l, (s + i) as nat) == Some(d[i].val) by {
            let x = (s + i) as nat;
            if i < r {
                assert(d[i] == front[i]);
                lemma_first_idx_unique(l, x, 0);
            } else {
                assert(d[i] == deaggregate_aux(t, s2)[i - r]);
                assert(l[0].time < x);
                assert(first_idx(l, x) == 1 + first_idx(t, x));
                lemma_first_idx(t, x);
                if first_idx(t, x) < t.len() {
                    assert(l[first_idx(l, x) as int] == t[first_idx(t, x) as int]);
                }
            }
        }
    }
}

/// A strictly increasing stream deaggregates to one verdict per time step
/// `0 .. next_after - 1`, each carrying the value the stream gives that step.
pub proof fn lemma_deaggregate(l: Seq<Verdict>)
    requires
        strictly_increasing(l),
    ensures
        deaggregate(l).len() == next_after(l),
        forall|i: int| 0 <= i < deaggregate(l).len() ==>
            (#[trigger] deaggregate(l)[i]).time == i && value_at(l, i as nat) == Some(deaggregate(l)[i].val),
{
    lemma_deaggregate_aux(l, 0);
}

} // verus!
