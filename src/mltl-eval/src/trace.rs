//! Executable traces: one `HashSet` of true atoms per time step, and the
//! spec trace (`Seq<Set<usize>>`) each one denotes.
use vstd::prelude::*;
use std::collections::HashSet;
use mltl_core::mltl::*;
use mltl_core::properties::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// An executable trace: one set of true atoms per time step.
pub type Trace = [HashSet<usize>];

/// The spec trace denoted by an executable trace.
pub open spec fn trace_view(t: Seq<HashSet<usize>>) -> Seq<Set<usize>> {
    t.map_values(|s: HashSet<usize>| s@)
}

/// Suffixes past the end are all the empty trace: `drop k (drop s π)` is
/// `drop (min(s+k, |π|)) π`.
pub proof fn lemma_suffix_clamp<T>(pi: Seq<T>, s: nat, k: nat)
    requires
        s <= pi.len(),
    ensures
        drop(drop(pi, s), k) == drop(pi, if s + k <= pi.len() { s + k } else { pi.len() }),
{
    lemma_drop_drop(pi, s, k);
    if s + k > pi.len() {
        lemma_drop_past_end(pi, s + k);
    }
}

/// `min(start + k, len)` without overflow.
pub fn clamp_pos(start: usize, k: usize, len: usize) -> (p: usize)
    requires
        start <= len,
    ensures
        p == if start + k <= len { start + k } else { len as int },
{
    if k <= len - start { start + k } else { len }
}


} // verus!
