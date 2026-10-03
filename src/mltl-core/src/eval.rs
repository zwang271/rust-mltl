//! Executable MLTL evaluation: two verified algorithms.
//!
//! * `mltl_eval` — top-down (direct recursive) evaluation, the executable
//!   counterpart of Isabelle's `mltl_eval` (`mltl_eval_spec` in
//!   `properties.rs`), with interval loops instead of per-step recursion.
//! * `mltl_eval_bottom_up` — bottom-up evaluation: computes, for each
//!   subformula, its truth value at every trace position that can matter, then
//!   combines them with interval scans.
//!
//! Both are proved to return exactly `semantics_mltl` (AFP semantics,
//! including evaluation on the empty suffix past the end of the trace).
//! Algorithms and complexity: `EVAL_MLTL.md` in this directory.
use vstd::prelude::*;
use std::collections::HashSet;
use crate::mltl::*;
use crate::properties::*;

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
fn clamp_pos(start: usize, k: usize, len: usize) -> (p: usize)
    requires
        start <= len,
    ensures
        p == if start + k <= len { start + k } else { len as int },
{
    if k <= len - start { start + k } else { len }
}

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

// ===========================================================================
// Bottom-up evaluation
// ===========================================================================
// For each subformula g we compute a table w with one entry per trace position
// that can influence the answer: w[m] = (drop m π ⊨ g) for m < h, plus a last
// entry w[h] = ([] ⊨ g), the value on the empty suffix. The root needs only
// position 0; a temporal operator with upper bound b needs its children up to
// h + b (capped at the trace length). Interval operators are answered in O(1)
// per position from "next position where the child is true/false" arrays.

/// `w` is a correct table for `f` on positions `0..h` of `tv`, with the
/// empty-suffix value in the last slot.
pub open spec fn sat_ok(tv: Seq<Set<usize>>, f: Mltl<usize>, w: Seq<bool>, h: nat) -> bool {
    &&& w.len() == h + 1
    &&& h <= tv.len()
    &&& forall|m: nat| m < h ==> w[m as int] == semantics_mltl(#[trigger] drop(tv, m), f)
    &&& w[h as int] == semantics_mltl(drop(tv, tv.len()), f)
}

/// Reading a table entry: index `m ≤ h`, where index `h` stands for the empty
/// suffix and may only be read when `h` is the full trace length.
proof fn lemma_sat_read(tv: Seq<Set<usize>>, f: Mltl<usize>, w: Seq<bool>, h: nat, m: nat)
    requires
        sat_ok(tv, f, w, h),
        m <= h,
        m == h ==> h == tv.len(),
    ensures
        w[m as int] == semantics_mltl(drop(tv, m), f),
{
}

/// `nt[j]` is the first index `≥ j` where `w` equals `want` (or `w.len()` if none).
pub open spec fn next_ok(w: Seq<bool>, want: bool, nt: Seq<usize>) -> bool {
    &&& nt.len() == w.len()
    &&& forall|j: int| 0 <= j < w.len() ==> {
        &&& j <= #[trigger] nt[j] <= w.len()
        &&& (nt[j] < w.len() ==> w[nt[j] as int] == want)
        &&& forall|m: int| j <= m < nt[j] ==> w[m] != want
    }
}

fn build_next(w: &Vec<bool>, want: bool) -> (nt: Vec<usize>)
    ensures
        next_ok(w@, want, nt@),
{
    let n = w.len();
    let mut nt: Vec<usize> = Vec::with_capacity(n);
    let mut z = 0;
    while z < n
        invariant
            z <= n, nt.len() == z,
        decreases n - z,
    {
        nt.push(0);
        z = z + 1;
    }
    let mut j = n;
    while j > 0
        invariant
            j <= n, n == w.len(), nt.len() == n,
            forall|jj: int| j <= jj < n ==> {
                &&& jj <= #[trigger] nt@[jj] <= n
                &&& (nt@[jj] < n ==> w@[nt@[jj] as int] == want)
                &&& forall|m: int| jj <= m < nt@[jj] ==> w@[m] != want
            },
        decreases j,
    {
        let idx = j - 1;
        let v = if w[idx] == want { idx } else if idx + 1 < n { nt[idx + 1] } else { n };
        nt.set(idx, v);
        j = idx;
    }
    nt
}

/// Window query: `w` takes value `want` somewhere in `[s, t]` iff `nt[s] ≤ t`.
proof fn lemma_window(w: Seq<bool>, want: bool, nt: Seq<usize>, s: int, t: int)
    requires
        next_ok(w, want, nt),
        0 <= s <= t < w.len(),
    ensures
        (exists|m: int| s <= m <= t && #[trigger] w[m] == want) == (nt[s] <= t),
{
    if nt[s] <= t {
        assert(w[nt[s] as int] == want);
    }
}

/// `drop i π ⊨ F[a,b] g` as a window over absolute positions `[i+a, min(i+b, |π|)]`.
proof fn lemma_future_window(tv: Seq<Set<usize>>, i: nat, a: usize, b: usize, g: Mltl<usize>)
    requires
        i <= tv.len(),
        a <= b,
        tv.len() - i > a,
    ensures
        semantics_mltl(drop(tv, i), Mltl::Future(a, b, Box::new(g))) == exists|m: nat|
            i + a <= m && m <= (if i + b <= tv.len() { i + b } else { tv.len() as int })
                && semantics_mltl(#[trigger] drop(tv, m), g),
{
    let pi = drop(tv, i);
    let len = tv.len();
    lemma_drop_len(tv, i);
    assert forall|k: nat| #[trigger] drop(pi, k) == drop(tv, if i + k <= len { i + k } else { len as nat }) by {
        lemma_suffix_clamp(tv, i, k);
    }
    if semantics_mltl(pi, Mltl::Future(a, b, Box::new(g))) {
        let k = choose|k: nat| (a <= k && k <= b) && semantics_mltl(drop(pi, k), g);
        let m: nat = if i + k <= len { i + k } else { len };
        assert(semantics_mltl(drop(tv, m), g));
    }
    if exists|m: nat| i + a <= m && m <= (if i + b <= len { i + b } else { len as int })
        && semantics_mltl(#[trigger] drop(tv, m), g) {
        let m = choose|m: nat| i + a <= m && m <= (if i + b <= len { i + b } else { len as int })
            && semantics_mltl(#[trigger] drop(tv, m), g);
        let k: nat = (m - i) as nat;
        assert(drop(pi, k) == drop(tv, m));
    }
}

/// `drop i π ⊨ G[a,b] g` as a window (when `|π| - i > a`).
proof fn lemma_global_window(tv: Seq<Set<usize>>, i: nat, a: usize, b: usize, g: Mltl<usize>)
    requires
        i <= tv.len(),
        a <= b,
        tv.len() - i > a,
    ensures
        semantics_mltl(drop(tv, i), Mltl::Global(a, b, Box::new(g))) == forall|m: nat|
            i + a <= m && m <= (if i + b <= tv.len() { i + b } else { tv.len() as int })
                ==> semantics_mltl(#[trigger] drop(tv, m), g),
{
    let pi = drop(tv, i);
    let len = tv.len();
    lemma_drop_len(tv, i);
    assert forall|k: nat| #[trigger] drop(pi, k) == drop(tv, if i + k <= len { i + k } else { len as nat }) by {
        lemma_suffix_clamp(tv, i, k);
    }
    if forall|m: nat| i + a <= m && m <= (if i + b <= len { i + b } else { len as int })
        ==> semantics_mltl(#[trigger] drop(tv, m), g) {
        assert forall|k: nat| (a <= k && k <= b) implies semantics_mltl(#[trigger] drop(pi, k), g) by {
            let m: nat = if i + k <= len { i + k } else { len };
            assert(semantics_mltl(drop(tv, m), g));
        }
    }
    if semantics_mltl(pi, Mltl::Global(a, b, Box::new(g))) {
        assert forall|m: nat| i + a <= m && m <= (if i + b <= len { i + b } else { len as int })
            implies semantics_mltl(#[trigger] drop(tv, m), g) by {
            let k: nat = (m - i) as nat;
            assert(drop(pi, k) == drop(tv, m));
        }
    }
}

/// `drop i π ⊨ φ U[a,b] ψ` as a window: some `m ∈ [i+a, t]` has ψ, and φ
/// holds on `[i+a, m)`.
proof fn lemma_until_window(tv: Seq<Set<usize>>, i: nat, a: usize, b: usize, phi: Mltl<usize>, psi: Mltl<usize>)
    requires
        i <= tv.len(),
        a <= b,
        tv.len() - i > a,
    ensures
        semantics_mltl(drop(tv, i), Mltl::Until(Box::new(phi), a, b, Box::new(psi))) == exists|m: nat|
            i + a <= m && m <= (if i + b <= tv.len() { i + b } else { tv.len() as int })
                && semantics_mltl(#[trigger] drop(tv, m), psi)
                && forall|m2: nat| i + a <= m2 && m2 < m ==> semantics_mltl(#[trigger] drop(tv, m2), phi),
{
    let pi = drop(tv, i);
    let len = tv.len();
    lemma_drop_len(tv, i);
    assert forall|k: nat| #[trigger] drop(pi, k) == drop(tv, if i + k <= len { i + k } else { len as nat }) by {
        lemma_suffix_clamp(tv, i, k);
    }
    if semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi))) {
        let k = choose|k: nat| (a <= k && k <= b) && (semantics_mltl(drop(pi, k), psi)
            && forall|j: nat| (j >= a && j < k) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        let m: nat = if i + k <= len { i + k } else { len };
        assert(semantics_mltl(drop(tv, m), psi));
        assert forall|m2: nat| i + a <= m2 && m2 < m implies semantics_mltl(#[trigger] drop(tv, m2), phi) by {
            let j: nat = (m2 - i) as nat;
            assert(drop(pi, j) == drop(tv, m2));
        }
    }
    if exists|m: nat| i + a <= m && m <= (if i + b <= len { i + b } else { len as int })
        && semantics_mltl(#[trigger] drop(tv, m), psi)
        && forall|m2: nat| i + a <= m2 && m2 < m ==> semantics_mltl(#[trigger] drop(tv, m2), phi) {
        let m = choose|m: nat| i + a <= m && m <= (if i + b <= len { i + b } else { len as int })
            && semantics_mltl(#[trigger] drop(tv, m), psi)
            && forall|m2: nat| i + a <= m2 && m2 < m ==> semantics_mltl(#[trigger] drop(tv, m2), phi);
        let k: nat = (m - i) as nat;
        assert(drop(pi, k) == drop(tv, m));
        assert forall|j: nat| (j >= a && j < k) implies semantics_mltl(#[trigger] drop(pi, j), phi) by {
            assert(drop(pi, j) == drop(tv, i + j));
        }
    }
}

/// `drop i π ⊨ φ R[a,b] ψ` as windows (when `|π| - i > a`): ψ on all of
/// `[i+a, t]`, or some `m ∈ [i+a, u]` has φ with ψ on `[i+a, m]`, where
/// `u = min(i + (b-1), |π|)` (truncating `b-1`).
proof fn lemma_release_window(tv: Seq<Set<usize>>, i: nat, a: usize, b: usize, phi: Mltl<usize>, psi: Mltl<usize>)
    requires
        i <= tv.len(),
        a <= b,
        tv.len() - i > a,
    ensures
        semantics_mltl(drop(tv, i), Mltl::Release(Box::new(phi), a, b, Box::new(psi))) == (
            (forall|m: nat| i + a <= m && m <= (if i + b <= tv.len() { i + b } else { tv.len() as int })
                ==> semantics_mltl(#[trigger] drop(tv, m), psi))
            || exists|m: nat| i + a <= m
                && m <= (if i + nat_sub(b as nat, 1) <= tv.len() { (i + nat_sub(b as nat, 1)) as int } else { tv.len() as int })
                && semantics_mltl(#[trigger] drop(tv, m), phi)
                && forall|m2: nat| i + a <= m2 && m2 <= m ==> semantics_mltl(#[trigger] drop(tv, m2), psi)),
{
    let pi = drop(tv, i);
    let len = tv.len();
    let bm1 = nat_sub(b as nat, 1);
    lemma_drop_len(tv, i);
    assert forall|k: nat| #[trigger] drop(pi, k) == drop(tv, if i + k <= len { i + k } else { len as nat }) by {
        lemma_suffix_clamp(tv, i, k);
    }
    let all_psi = forall|m: nat| i + a <= m && m <= (if i + b <= len { i + b } else { len as int })
        ==> semantics_mltl(#[trigger] drop(tv, m), psi);
    let rel_all = forall|k: nat| (a <= k && k <= b) ==> semantics_mltl(#[trigger] drop(pi, k), psi);
    // ψ on the whole interval: relative and absolute forms agree.
    if all_psi {
        assert forall|k: nat| (a <= k && k <= b) implies semantics_mltl(#[trigger] drop(pi, k), psi) by {
            let m: nat = if i + k <= len { i + k } else { len };
            assert(semantics_mltl(drop(tv, m), psi));
        }
    }
    if rel_all {
        assert forall|m: nat| i + a <= m && m <= (if i + b <= len { i + b } else { len as int })
            implies semantics_mltl(#[trigger] drop(tv, m), psi) by {
            let k: nat = (m - i) as nat;
            assert(drop(pi, k) == drop(tv, m));
        }
    }
    // The φ-witness disjunct.
    let rel_ex = exists|j: nat| (j >= a && j <= bm1) && semantics_mltl(drop(pi, j), phi)
        && forall|k: nat| (a <= k && k <= j) ==> semantics_mltl(#[trigger] drop(pi, k), psi);
    let abs_ex = exists|m: nat| i + a <= m && m <= (if i + bm1 <= len { (i + bm1) as int } else { len as int })
        && semantics_mltl(#[trigger] drop(tv, m), phi)
        && forall|m2: nat| i + a <= m2 && m2 <= m ==> semantics_mltl(#[trigger] drop(tv, m2), psi);
    if rel_ex {
        let j = choose|j: nat| (j >= a && j <= bm1) && semantics_mltl(drop(pi, j), phi)
            && forall|k: nat| (a <= k && k <= j) ==> semantics_mltl(#[trigger] drop(pi, k), psi);
        let m: nat = if i + j <= len { i + j } else { len };
        assert(semantics_mltl(drop(tv, m), phi));
        assert forall|m2: nat| i + a <= m2 && m2 <= m implies semantics_mltl(#[trigger] drop(tv, m2), psi) by {
            let k: nat = if m2 == len && i + j > len { j } else { (m2 - i) as nat };
            if m2 == len && i + j > len {
                assert(drop(pi, j) == drop(tv, len as nat));
            } else {
                assert(drop(pi, k) == drop(tv, m2));
            }
        }
        assert(abs_ex);
    }
    if abs_ex {
        let m = choose|m: nat| i + a <= m && m <= (if i + bm1 <= len { (i + bm1) as int } else { len as int })
            && semantics_mltl(#[trigger] drop(tv, m), phi)
            && forall|m2: nat| i + a <= m2 && m2 <= m ==> semantics_mltl(#[trigger] drop(tv, m2), psi);
        let j: nat = (m - i) as nat;
        assert(drop(pi, j) == drop(tv, m));
        assert forall|k: nat| (a <= k && k <= j) implies semantics_mltl(#[trigger] drop(pi, k), psi) by {
            assert(drop(pi, k) == drop(tv, i + k));
        }
        assert(rel_ex);
    }
}

/// Bottom-up evaluation: `mltl_eval_bottom_up(f, t) == semantics_mltl(t, f)`.
pub fn mltl_eval_bottom_up(f: &Mltl<usize>, t: &Trace) -> (r: bool)
    requires
        t.len() < usize::MAX,
    ensures
        r == semantics_mltl(trace_view(t@), *f),
{
    let h = if t.len() == 0 { 0 } else { 1 };
    let w = sat_table(f, t, h);
    proof {
        lemma_drop_zero(trace_view(t@));
        if t.len() == 0 {
            assert(trace_view(t@).len() == 0);
        }
    }
    w[0]
}

/// The table for `f` on positions `0..h` (plus the empty-suffix slot).
fn sat_table(f: &Mltl<usize>, t: &Trace, h: usize) -> (w: Vec<bool>)
    requires
        h <= t.len(),
        t.len() < usize::MAX,
    ensures
        sat_ok(trace_view(t@), *f, w@, h as nat),
    decreases *f, 1nat,
{
    let ghost tv = trace_view(t@);
    let len = t.len();
    proof { assert(tv.len() == len); lemma_drop_past_end(tv, len as nat); }
    let mut w: Vec<bool> = Vec::with_capacity(h + 1);
    match f {
        Mltl::True | Mltl::False => {
            let val = match f { Mltl::True => true, _ => false };
            let mut i = 0;
            while i <= h
                invariant
                    i <= h + 1, w.len() == i, h < usize::MAX, f is True || f is False,
                    val == (f is True),
                    forall|m: int| 0 <= m < i ==> w@[m] == val,
                decreases h + 1 - i,
            {
                w.push(val);
                i = i + 1;
            }
            w
        },
        Mltl::Prop(q) => {
            let mut i = 0;
            while i < h
                invariant
                    i <= h, h <= len, len == t.len(), w.len() == i, tv == trace_view(t@),
                    *f == Mltl::<usize>::Prop(*q),
                    forall|m: nat| m < i ==> w@[m as int] == semantics_mltl(#[trigger] drop(tv, m), *f),
                decreases h - i,
            {
                proof {
                    lemma_drop_len(tv, i as nat);
                    assert(drop(tv, i as nat)[0] == t@[i as int]@);
                }
                w.push(t[i].contains(q));
                i = i + 1;
            }
            w.push(false);
            w
        },
        Mltl::Not(g) => {
            let wg = sat_table(g, t, h);
            let mut i = 0;
            while i <= h
                invariant
                    i <= h + 1, w.len() == i, h < usize::MAX, wg@.len() == h + 1,
                    forall|m: int| 0 <= m < i ==> w@[m] == !wg@[m],
                decreases h + 1 - i,
            {
                w.push(!wg[i]);
                i = i + 1;
            }
            w
        },
        Mltl::And(g1, g2) | Mltl::Or(g1, g2) => {
            let is_and = match f { Mltl::And(_, _) => true, _ => false };
            let w1 = sat_table(g1, t, h);
            let w2 = sat_table(g2, t, h);
            let mut i = 0;
            while i <= h
                invariant
                    i <= h + 1, w.len() == i, h < usize::MAX, w1@.len() == h + 1, w2@.len() == h + 1,
                    is_and == (f is And),
                    forall|m: int| 0 <= m < i ==> w@[m] == if is_and { w1@[m] && w2@[m] } else { w1@[m] || w2@[m] },
                decreases h + 1 - i,
            {
                w.push(if is_and { w1[i] && w2[i] } else { w1[i] || w2[i] });
                i = i + 1;
            }
            w
        },
        Mltl::Future(a, b, g) => sat_future(f, *a, *b, g, t, h),
        Mltl::Global(a, b, g) => sat_global(f, *a, *b, g, t, h),
        Mltl::Until(g1, a, b, g2) => sat_until(f, g1, *a, *b, g2, t, h),
        Mltl::Release(g1, a, b, g2) => sat_release(f, g1, *a, *b, g2, t, h),
    }
}

/// Child horizon for a temporal node with upper bound `b` and horizon `h`.
fn child_horizon(h: usize, b: usize, len: usize) -> (hc: usize)
    requires
        h <= len,
    ensures
        hc <= len,
        h == 0 ==> hc == 0,
        h > 0 ==> hc == if h + b <= len { h + b } else { len as int },
{
    if h == 0 { 0 } else if b > len - h { len } else { h + b }
}

/// End of the window `[i+a, min(i+b, len)]` for position `i` (given `i < len`).
fn window_end(i: usize, b: usize, len: usize) -> (e: usize)
    requires
        i < len,
    ensures
        e == if i + b <= len { i + b } else { len as int },
{
    if b > len - i { len } else { i + b }
}

/// Window bridge: on a window `[s, e]` that the child table covers, "the
/// child has truth value `want` somewhere" is `nt[s] ≤ e`.
proof fn lemma_window_sem(tv: Seq<Set<usize>>, g: Mltl<usize>, wg: Seq<bool>, hc: nat,
    want: bool, nt: Seq<usize>, s: nat, e: nat)
    requires
        sat_ok(tv, g, wg, hc),
        next_ok(wg, want, nt),
        s <= e <= hc,
        e == hc ==> hc == tv.len(),
    ensures
        (exists|m: nat| s <= m && m <= e && semantics_mltl(#[trigger] drop(tv, m), g) == want) == (nt[s as int] <= e),
        forall|m: nat| s <= m && m <= e ==> wg[m as int] == semantics_mltl(#[trigger] drop(tv, m), g),
{
    assert forall|m: nat| s <= m && m <= e implies wg[m as int] == semantics_mltl(#[trigger] drop(tv, m), g) by {
        lemma_sat_read(tv, g, wg, hc, m);
    }
    lemma_window(wg, want, nt, s as int, e as int);
    if nt[s as int] <= e {
        let m = nt[s as int] as nat;
        assert(semantics_mltl(drop(tv, m), g) == want);
    }
    if exists|m: nat| s <= m && m <= e && semantics_mltl(#[trigger] drop(tv, m), g) == want {
        let m = choose|m: nat| s <= m && m <= e && semantics_mltl(#[trigger] drop(tv, m), g) == want;
        assert(wg[m as int] == want);
    }
}

/// Every window `[i+a, min(i+b, len)]` with `i < h` lies inside the child table.
proof fn lemma_window_in_table(h: nat, b: nat, len: nat, hc: nat, i: nat)
    requires
        i < h, h <= len,
        hc == if h + b <= len { h + b } else { len },
    ensures
        (if i + b <= len { i + b } else { len }) <= hc,
        (if i + b <= len { i + b } else { len }) == hc ==> hc == len,
{
}

fn sat_future(f: &Mltl<usize>, a: usize, b: usize, g: &Box<Mltl<usize>>, t: &Trace, h: usize) -> (w: Vec<bool>)
    requires
        h <= t.len(),
        t.len() < usize::MAX,
        *f == Mltl::<usize>::Future(a, b, *g),
    ensures
        sat_ok(trace_view(t@), *f, w@, h as nat),
    decreases *f, 0nat,
{
    let ghost tv = trace_view(t@);
    let len = t.len();
    proof { assert(tv.len() == len); lemma_drop_past_end(tv, len as nat); assert(f->Future_2 == *g); }
    let hc = child_horizon(h, b, len);
    let wg = sat_table(g, t, hc);
    let nt = build_next(&wg, true);
    let mut w: Vec<bool> = Vec::with_capacity(h + 1);
    let mut i = 0;
    while i < h
        invariant
            i <= h, h <= len, len == t.len(), len < usize::MAX, w.len() == i, tv == trace_view(t@),
            *f == Mltl::<usize>::Future(a, b, *g), tv.len() == len,
            h > 0 ==> hc == if h + b <= len { h + b } else { len as int },
            sat_ok(tv, **g, wg@, hc as nat), next_ok(wg@, true, nt@),
            forall|m: nat| m < i ==> w@[m as int] == semantics_mltl(#[trigger] drop(tv, m), *f),
        decreases h - i,
    {
        let rem = len - i;
        let val = if a <= b && rem > a {
            let s0 = i + a;
            let e = window_end(i, b, len);
            proof {
                lemma_window_in_table(h as nat, b as nat, len as nat, hc as nat, i as nat);
                lemma_window_sem(tv, **g, wg@, hc as nat, true, nt@, s0 as nat, e as nat);
                lemma_future_window(tv, i as nat, a, b, **g);
            }
            nt[s0] <= e
        } else {
            false
        };
        proof { lemma_drop_len(tv, i as nat); }
        w.push(val);
        i = i + 1;
    }
    w.push(false);
    w
}

fn sat_global(f: &Mltl<usize>, a: usize, b: usize, g: &Box<Mltl<usize>>, t: &Trace, h: usize) -> (w: Vec<bool>)
    requires
        h <= t.len(),
        t.len() < usize::MAX,
        *f == Mltl::<usize>::Global(a, b, *g),
    ensures
        sat_ok(trace_view(t@), *f, w@, h as nat),
    decreases *f, 0nat,
{
    let ghost tv = trace_view(t@);
    let len = t.len();
    proof { assert(tv.len() == len); lemma_drop_past_end(tv, len as nat); assert(f->Global_2 == *g); }
    let hc = child_horizon(h, b, len);
    let wg = sat_table(g, t, hc);
    let nf = build_next(&wg, false);
    let mut w: Vec<bool> = Vec::with_capacity(h + 1);
    let mut i = 0;
    while i < h
        invariant
            i <= h, h <= len, len == t.len(), len < usize::MAX, w.len() == i, tv == trace_view(t@),
            *f == Mltl::<usize>::Global(a, b, *g), tv.len() == len,
            h > 0 ==> hc == if h + b <= len { h + b } else { len as int },
            sat_ok(tv, **g, wg@, hc as nat), next_ok(wg@, false, nf@),
            forall|m: nat| m < i ==> w@[m as int] == semantics_mltl(#[trigger] drop(tv, m), *f),
        decreases h - i,
    {
        let rem = len - i;
        let val = if !(a <= b) {
            false
        } else if rem <= a {
            true
        } else {
            let s0 = i + a;
            let e = window_end(i, b, len);
            proof {
                lemma_window_in_table(h as nat, b as nat, len as nat, hc as nat, i as nat);
                lemma_window_sem(tv, **g, wg@, hc as nat, false, nf@, s0 as nat, e as nat);
                lemma_global_window(tv, i as nat, a, b, **g);
            }
            nf[s0] > e
        };
        proof { lemma_drop_len(tv, i as nat); }
        w.push(val);
        i = i + 1;
    }
    w.push(a <= b);
    w
}

fn sat_until(f: &Mltl<usize>, g1: &Box<Mltl<usize>>, a: usize, b: usize, g2: &Box<Mltl<usize>>, t: &Trace, h: usize)
    -> (w: Vec<bool>)
    requires
        h <= t.len(),
        t.len() < usize::MAX,
        *f == Mltl::<usize>::Until(*g1, a, b, *g2),
    ensures
        sat_ok(trace_view(t@), *f, w@, h as nat),
    decreases *f, 0nat,
{
    let ghost tv = trace_view(t@);
    let len = t.len();
    proof { assert(tv.len() == len); lemma_drop_past_end(tv, len as nat); assert(f->Until_0 == *g1 && f->Until_3 == *g2); }
    let hc = child_horizon(h, b, len);
    let w1 = sat_table(g1, t, hc);
    let w2 = sat_table(g2, t, hc);
    let nf1 = build_next(&w1, false);
    let nt2 = build_next(&w2, true);
    let mut w: Vec<bool> = Vec::with_capacity(h + 1);
    let mut i = 0;
    while i < h
        invariant
            i <= h, h <= len, len == t.len(), len < usize::MAX, w.len() == i, tv == trace_view(t@),
            *f == Mltl::<usize>::Until(*g1, a, b, *g2), tv.len() == len,
            h > 0 ==> hc == if h + b <= len { h + b } else { len as int },
            sat_ok(tv, **g1, w1@, hc as nat), next_ok(w1@, false, nf1@),
            sat_ok(tv, **g2, w2@, hc as nat), next_ok(w2@, true, nt2@),
            forall|m: nat| m < i ==> w@[m as int] == semantics_mltl(#[trigger] drop(tv, m), *f),
        decreases h - i,
    {
        let rem = len - i;
        let val = if a <= b && rem > a {
            let s0 = i + a;
            let e = window_end(i, b, len);
            let p = nt2[s0];
            proof {
                lemma_window_in_table(h as nat, b as nat, len as nat, hc as nat, i as nat);
                lemma_window_sem(tv, **g2, w2@, hc as nat, true, nt2@, s0 as nat, e as nat);
                lemma_window_sem(tv, **g1, w1@, hc as nat, false, nf1@, s0 as nat, e as nat);
                lemma_until_window(tv, i as nat, a, b, **g1, **g2);
                let ex = exists|m: nat| s0 <= m && m <= e && semantics_mltl(#[trigger] drop(tv, m), **g2)
                    && forall|m2: nat| s0 <= m2 && m2 < m ==> semantics_mltl(#[trigger] drop(tv, m2), **g1);
                if p <= e && nf1@[s0 as int] >= p {
                    // witness: the first ψ position p; φ holds on [s0, p)
                    assert(w2@[p as int]);
                    assert forall|m2: nat| s0 <= m2 && m2 < p implies semantics_mltl(#[trigger] drop(tv, m2), **g1) by {
                        assert(w1@[m2 as int] != false);
                    }
                    assert(semantics_mltl(drop(tv, p as nat), **g2));
                    assert(ex);
                }
                if ex {
                    let m = choose|m: nat| s0 <= m && m <= e && semantics_mltl(#[trigger] drop(tv, m), **g2)
                        && forall|m2: nat| s0 <= m2 && m2 < m ==> semantics_mltl(#[trigger] drop(tv, m2), **g1);
                    assert(w2@[m as int]);
                    assert(p <= m);
                    if nf1@[s0 as int] < p {
                        let q = nf1@[s0 as int] as nat;
                        assert(!w1@[q as int]);
                        assert(semantics_mltl(drop(tv, q), **g1));
                    }
                }
            }
            p <= e && nf1[s0] >= p
        } else {
            false
        };
        proof { lemma_drop_len(tv, i as nat); }
        w.push(val);
        i = i + 1;
    }
    w.push(false);
    w
}

fn sat_release(f: &Mltl<usize>, g1: &Box<Mltl<usize>>, a: usize, b: usize, g2: &Box<Mltl<usize>>, t: &Trace, h: usize)
    -> (w: Vec<bool>)
    requires
        h <= t.len(),
        t.len() < usize::MAX,
        *f == Mltl::<usize>::Release(*g1, a, b, *g2),
    ensures
        sat_ok(trace_view(t@), *f, w@, h as nat),
    decreases *f, 0nat,
{
    let ghost tv = trace_view(t@);
    let len = t.len();
    proof { assert(tv.len() == len); lemma_drop_past_end(tv, len as nat); assert(f->Release_0 == *g1 && f->Release_3 == *g2); }
    let hc = child_horizon(h, b, len);
    let w1 = sat_table(g1, t, hc);
    let w2 = sat_table(g2, t, hc);
    let nt1 = build_next(&w1, true);
    let nf2 = build_next(&w2, false);
    let bm1 = if b == 0 { 0 } else { b - 1 };
    let mut w: Vec<bool> = Vec::with_capacity(h + 1);
    let mut i = 0;
    while i < h
        invariant
            i <= h, h <= len, len == t.len(), len < usize::MAX, w.len() == i, tv == trace_view(t@),
            *f == Mltl::<usize>::Release(*g1, a, b, *g2), tv.len() == len, bm1 == nat_sub(b as nat, 1),
            h > 0 ==> hc == if h + b <= len { h + b } else { len as int },
            sat_ok(tv, **g1, w1@, hc as nat), next_ok(w1@, true, nt1@),
            sat_ok(tv, **g2, w2@, hc as nat), next_ok(w2@, false, nf2@),
            forall|m: nat| m < i ==> w@[m as int] == semantics_mltl(#[trigger] drop(tv, m), *f),
        decreases h - i,
    {
        let rem = len - i;
        let val = if !(a <= b) {
            false
        } else if rem <= a {
            true
        } else {
            let s0 = i + a;
            let e = window_end(i, b, len);
            let u = window_end(i, bm1, len);
            let q = nf2[s0];
            proof {
                lemma_window_in_table(h as nat, b as nat, len as nat, hc as nat, i as nat);
                lemma_window_sem(tv, **g2, w2@, hc as nat, false, nf2@, s0 as nat, e as nat);
                lemma_release_window(tv, i as nat, a, b, **g1, **g2);
                assert(u <= e);
            }
            if q > e {
                true
            } else if q > s0 {
                let lim = if u < q - 1 { u } else { q - 1 };
                proof {
                    assert(s0 <= lim || lim < s0);
                    let ex = exists|m: nat| s0 <= m && m <= u && semantics_mltl(#[trigger] drop(tv, m), **g1)
                        && forall|m2: nat| s0 <= m2 && m2 <= m ==> semantics_mltl(#[trigger] drop(tv, m2), **g2);
                    assert(!w2@[q as int]);
                    assert(!semantics_mltl(drop(tv, q as nat), **g2));
                    if lim >= s0 {
                        lemma_window_sem(tv, **g1, w1@, hc as nat, true, nt1@, s0 as nat, lim as nat);
                        assert forall|m2: nat| s0 <= m2 && m2 < q implies semantics_mltl(#[trigger] drop(tv, m2), **g2) by {
                            assert(w2@[m2 as int] != false);
                        }
                        if nt1@[s0 as int] <= lim {
                            let m = nt1@[s0 as int] as nat;
                            assert(semantics_mltl(drop(tv, m), **g1));
                            assert(ex);
                        }
                        if ex {
                            let m = choose|m: nat| s0 <= m && m <= u && semantics_mltl(#[trigger] drop(tv, m), **g1)
                                && forall|m2: nat| s0 <= m2 && m2 <= m ==> semantics_mltl(#[trigger] drop(tv, m2), **g2);
                            assert(m < q);
                        }
                    } else if ex {
                        let m = choose|m: nat| s0 <= m && m <= u && semantics_mltl(#[trigger] drop(tv, m), **g1)
                            && forall|m2: nat| s0 <= m2 && m2 <= m ==> semantics_mltl(#[trigger] drop(tv, m2), **g2);
                        assert(m < q);
                    }
                }
                lim >= s0 && nt1[s0] <= lim
            } else {
                proof {
                    assert(q == s0);
                    assert(!w2@[q as int]);
                    assert(!semantics_mltl(drop(tv, s0 as nat), **g2));
                }
                false
            }
        };
        proof { lemma_drop_len(tv, i as nat); }
        w.push(val);
        i = i + 1;
    }
    w.push(a <= b);
    w
}

} // verus!
