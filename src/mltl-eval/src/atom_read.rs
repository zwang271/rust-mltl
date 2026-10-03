//! Read access to a trace, independent of how it is stored. The bottom-up
//! evaluator is written once against this trait and proved once; each trace
//! representation proves that its reads agree with the spec trace it
//! denotes (`view_trace`).
use vstd::prelude::*;
use std::collections::HashSet;
use crate::trace::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub trait AtomRead {
    /// The spec trace this value denotes.
    spec fn view_trace(&self) -> Seq<Set<usize>>;

    /// Representation invariant (`true` for representations without one).
    spec fn inv(&self) -> bool;

    fn len(&self) -> (n: usize)
        requires
            self.inv(),
        ensures
            n == self.view_trace().len(),
    ;

    /// Append "does `atom` hold at step i" for i in 0..h to `w`.
    fn push_row(&self, atom: usize, h: usize, w: &mut Vec<bool>)
        requires
            self.inv(),
            h <= self.view_trace().len(),
        ensures
            final(w)@ == old(w)@ + Seq::new(h as nat, |i: int| self.view_trace()[i].contains(atom)),
    ;
}

/// Set-per-step traces (`Trace`).
impl AtomRead for [HashSet<usize>] {
    open spec fn view_trace(&self) -> Seq<Set<usize>> {
        trace_view(self@)
    }

    open spec fn inv(&self) -> bool {
        true
    }

    fn len(&self) -> (n: usize) {
        <[HashSet<usize>]>::len(self)
    }

    fn push_row(&self, atom: usize, h: usize, w: &mut Vec<bool>) {
        let ghost w0 = w@;
        let mut i = 0;
        while i < h
            invariant
                i <= h,
                h <= self@.len(),
                w@ == w0 + Seq::new(i as nat, |m: int| trace_view(self@)[m].contains(atom)),
            decreases h - i,
        {
            let b = self[i].contains(&atom);
            w.push(b);
            i = i + 1;
            assert(w@ =~= w0 + Seq::new(i as nat, |m: int| trace_view(self@)[m].contains(atom)));
        }
    }
}

} // verus!
