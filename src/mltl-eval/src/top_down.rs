//! Top-down evaluation (`mltl_eval`): the executable counterpart of the
//! Isabelle evaluator (`mltl_eval_spec` in mltl-core), with loops over
//! intervals. Proved equal to `semantics_mltl`. See `../EVAL_MLTL.md`.
use vstd::prelude::*;
use std::collections::HashSet;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::trace::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

// ===========================================================================
// Top-down evaluation
// ===========================================================================

/// Top-down evaluation: `mltl_eval(f, t) == semantics_mltl(t, f)`.
pub fn mltl_eval(f: &Mltl<usize>, t: &Trace) -> (r: bool)
    ensures
        r == semantics_mltl(trace_view(t@), *f),
        r == mltl_eval_spec(*f, trace_view(t@)),
{
    let r = eval_at(f, t, 0);
    proof {
        lemma_drop_zero(trace_view(t@));
        mltl_eval_correct(*f, trace_view(t@));
    }
    r
}

/// `f` evaluated on the suffix of `t` starting at `start` (`start == t.len()`
/// is the empty suffix).
fn eval_at(f: &Mltl<usize>, t: &Trace, start: usize) -> (r: bool)
    requires
        start <= t.len(),
    ensures
        r == semantics_mltl(drop(trace_view(t@), start as nat), *f),
    decreases *f, 1nat,
{
    let ghost tv = trace_view(t@);
    let ghost pi = drop(tv, start as nat);
    proof { lemma_drop_len(tv, start as nat); }
    let len = t.len();
    match f {
        Mltl::True => true,
        Mltl::False => false,
        Mltl::Prop(q) => {
            if start < len {
                proof { assert(pi[0] == t@[start as int]@); }
                t[start].contains(q)
            } else {
                false
            }
        },
        Mltl::Not(g) => !eval_at(g, t, start),
        Mltl::And(g, h) => eval_at(g, t, start) && eval_at(h, t, start),
        Mltl::Or(g, h) => eval_at(g, t, start) || eval_at(h, t, start),
        Mltl::Future(a, b, g) => eval_future(f, *a, *b, g, t, start),
        Mltl::Global(a, b, g) => eval_global(f, *a, *b, g, t, start),
        Mltl::Until(g, a, b, h) => eval_until(f, g, *a, *b, h, t, start),
        Mltl::Release(g, a, b, h) => eval_release(f, g, *a, *b, h, t, start),
    }
}


fn eval_future(f: &Mltl<usize>, a: usize, b: usize, g: &Box<Mltl<usize>>, t: &Trace, start: usize) -> (r: bool)
    requires
        start <= t.len(),
        *f == Mltl::<usize>::Future(a, b, *g),
    ensures
        r == semantics_mltl(drop(trace_view(t@), start as nat), *f),
    decreases *f, 0nat,
{
    let ghost tv = trace_view(t@);
    let ghost pi = drop(tv, start as nat);
    proof { lemma_drop_len(tv, start as nat); }
    let len = t.len();
        let rem = len - start;
        if !(a <= b && rem > a) {
            return false;
        }
        // Positions past the end all see the empty suffix, so [a, min(b, rem)] suffices.
        let hi = if b < rem { b } else { rem };
        let mut k = a;
        loop
            invariant
                a <= k <= hi, hi <= rem, hi <= b, hi == b || hi == rem, rem == len - start, len == t.len(), rem > a,
                start <= len, tv == trace_view(t@), pi == drop(tv, start as nat), pi.len() == rem,
                *f == Mltl::<usize>::Future(a, b, *g),
                forall|j: nat| a <= j < k ==> !semantics_mltl(#[trigger] drop(pi, j), **g),
            ensures
                forall|j: nat| a <= j <= hi ==> !semantics_mltl(#[trigger] drop(pi, j), **g),
            decreases hi - k,
        {
            let p = clamp_pos(start, k, len);
            proof {
                assert(f->Future_2 == *g);
                lemma_suffix_clamp(tv, start as nat, k as nat);
                assert(*f == Mltl::<usize>::Future(a, b, *g));
            }
            if eval_at(g, t, p) {
                assert(semantics_mltl(drop(pi, k as nat), **g));
                return true;
            }
            if k == hi { break; }
            k = k + 1;
        }
        proof {
            assert forall|j: nat| a <= j <= b implies !semantics_mltl(#[trigger] drop(pi, j), **g) by {
                if j > hi {
                    lemma_drop_past_end(pi, j);
                    lemma_drop_past_end(pi, hi as nat);
                }
            }
        }
        false
    
}

fn eval_global(f: &Mltl<usize>, a: usize, b: usize, g: &Box<Mltl<usize>>, t: &Trace, start: usize) -> (r: bool)
    requires
        start <= t.len(),
        *f == Mltl::<usize>::Global(a, b, *g),
    ensures
        r == semantics_mltl(drop(trace_view(t@), start as nat), *f),
    decreases *f, 0nat,
{
    let ghost tv = trace_view(t@);
    let ghost pi = drop(tv, start as nat);
    proof { lemma_drop_len(tv, start as nat); }
    let len = t.len();
        let rem = len - start;
        if !(a <= b) {
            return false;
        }
        if rem <= a {
            return true;
        }
        let hi = if b < rem { b } else { rem };
        let mut k = a;
        loop
            invariant
                a <= k <= hi, hi <= rem, hi <= b, hi == b || hi == rem, rem == len - start, len == t.len(), rem > a,
                start <= len, tv == trace_view(t@), pi == drop(tv, start as nat), pi.len() == rem,
                *f == Mltl::<usize>::Global(a, b, *g),
                forall|j: nat| a <= j < k ==> semantics_mltl(#[trigger] drop(pi, j), **g),
            ensures
                forall|j: nat| a <= j <= hi ==> semantics_mltl(#[trigger] drop(pi, j), **g),
            decreases hi - k,
        {
            let p = clamp_pos(start, k, len);
            proof { assert(f->Global_2 == *g);
                lemma_suffix_clamp(tv, start as nat, k as nat); }
            if !eval_at(g, t, p) {
                assert(!semantics_mltl(drop(pi, k as nat), **g));
                return false;
            }
            if k == hi { break; }
            k = k + 1;
        }
        proof {
            assert forall|j: nat| a <= j <= b implies semantics_mltl(#[trigger] drop(pi, j), **g) by {
                if j > hi {
                    lemma_drop_past_end(pi, j);
                    lemma_drop_past_end(pi, hi as nat);
                }
            }
        }
        true
    
}

fn eval_until(f: &Mltl<usize>, g: &Box<Mltl<usize>>, a: usize, b: usize, h: &Box<Mltl<usize>>, t: &Trace, start: usize) -> (r: bool)
    requires
        start <= t.len(),
        *f == Mltl::<usize>::Until(*g, a, b, *h),
    ensures
        r == semantics_mltl(drop(trace_view(t@), start as nat), *f),
    decreases *f, 0nat,
{
    let ghost tv = trace_view(t@);
    let ghost pi = drop(tv, start as nat);
    proof { lemma_drop_len(tv, start as nat); }
    let len = t.len();
        let rem = len - start;
        if !(a <= b && rem > a) {
            return false;
        }
        let hi = if b < rem { b } else { rem };
        let mut k = a;
        loop
            invariant
                a <= k <= hi, hi <= rem, hi <= b, hi == b || hi == rem, rem == len - start, len == t.len(), rem > a,
                start <= len, tv == trace_view(t@), pi == drop(tv, start as nat), pi.len() == rem,
                *f == Mltl::<usize>::Until(*g, a, b, *h),
                forall|j: nat| a <= j < k ==> !semantics_mltl(#[trigger] drop(pi, j), **h)
                    && semantics_mltl(drop(pi, j), **g),
            ensures
                forall|j: nat| a <= j <= hi ==> !semantics_mltl(#[trigger] drop(pi, j), **h)
                    && semantics_mltl(drop(pi, j), **g),
            decreases hi - k,
        {
            let p = clamp_pos(start, k, len);
            proof { assert(f->Until_0 == *g && f->Until_3 == *h);
                lemma_suffix_clamp(tv, start as nat, k as nat); }
            if eval_at(h, t, p) {
                assert(semantics_mltl(drop(pi, k as nat), **h));
                assert(forall|j: nat| (j >= a && j < k) ==> semantics_mltl(#[trigger] drop(pi, j), **g));
                return true;
            }
            if !eval_at(g, t, p) {
                proof {
                    assert forall|i: nat| (a <= i && i <= b) implies !(semantics_mltl(#[trigger] drop(pi, i), **h)
                        && forall|j: nat| (j >= a && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), **g)) by {
                        if i > k {
                            assert(!semantics_mltl(drop(pi, k as nat), **g));
                        }
                    }
                }
                return false;
            }
            if k == hi { break; }
            k = k + 1;
        }
        proof {
            assert forall|i: nat| (a <= i && i <= b) implies !semantics_mltl(#[trigger] drop(pi, i), **h) by {
                if i > hi {
                    lemma_drop_past_end(pi, i);
                    lemma_drop_past_end(pi, hi as nat);
                }
            }
        }
        false
    
}

fn eval_release(f: &Mltl<usize>, g: &Box<Mltl<usize>>, a: usize, b: usize, h: &Box<Mltl<usize>>, t: &Trace, start: usize) -> (r: bool)
    requires
        start <= t.len(),
        *f == Mltl::<usize>::Release(*g, a, b, *h),
    ensures
        r == semantics_mltl(drop(trace_view(t@), start as nat), *f),
    decreases *f, 0nat,
{
    let ghost tv = trace_view(t@);
    let ghost pi = drop(tv, start as nat);
    proof { lemma_drop_len(tv, start as nat); }
    let len = t.len();
        let rem = len - start;
        if !(a <= b) {
            return false;
        }
        if rem <= a {
            return true;
        }
        let hi = if b < rem { b } else { rem };
        let mut k = a;
        loop
            invariant
                a <= k <= hi, hi <= rem, hi <= b, hi == b || hi == rem, rem == len - start, len == t.len(), rem > a,
                start <= len, tv == trace_view(t@), pi == drop(tv, start as nat), pi.len() == rem,
                *f == Mltl::<usize>::Release(*g, a, b, *h),
                forall|j: nat| a <= j < k ==> semantics_mltl(#[trigger] drop(pi, j), **h)
                    && !semantics_mltl(drop(pi, j), **g),
            ensures
                forall|j: nat| a <= j <= hi ==> semantics_mltl(#[trigger] drop(pi, j), **h),
            decreases hi - k,
        {
            let p = clamp_pos(start, k, len);
            proof { assert(f->Release_0 == *g && f->Release_3 == *h);
                lemma_suffix_clamp(tv, start as nat, k as nat); }
            if !eval_at(h, t, p) {
                proof {
                    assert(!semantics_mltl(drop(pi, k as nat), **h));
                    assert forall|j: nat| (j >= a && j <= nat_sub(b as nat, 1)) implies !(
                        semantics_mltl(#[trigger] drop(pi, j), **g)
                        && forall|m: nat| (a <= m && m <= j) ==> semantics_mltl(#[trigger] drop(pi, m), **h)) by {
                        if j >= k {
                            assert(!semantics_mltl(drop(pi, k as nat), **h));
                        }
                    }
                }
                return false;
            }
            if (b == 0 || k < b) && eval_at(g, t, p) {
                proof {
                    assert(semantics_mltl(drop(pi, k as nat), **g));
                    assert(k <= nat_sub(b as nat, 1));
                    assert(forall|m: nat| (a <= m && m <= k) ==> semantics_mltl(#[trigger] drop(pi, m), **h));
                }
                return true;
            }
            proof {
                if !(b == 0 || k < b) {
                    // k == b == hi: the loop ends now, and ψ held on all of [a, b].
                    assert(k == hi);
                } else {
                    assert(!semantics_mltl(drop(pi, k as nat), **g));
                }
            }
            if k == hi { break; }
            k = k + 1;
        }
        proof {
            assert forall|i: nat| (a <= i && i <= b) implies semantics_mltl(#[trigger] drop(pi, i), **h) by {
                if i > hi {
                    lemma_drop_past_end(pi, i);
                    lemma_drop_past_end(pi, hi as nat);
                }
            }
        }
        true
    
}


} // verus!
