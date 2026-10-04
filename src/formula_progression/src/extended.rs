//! Simplified formula progression (`prog`) and its early-evaluation theorem.
//!
//! Mirrors the unpublished `Formula_Progression_Extended.thy`, sections
//! "Correctness" and "Executable Formula Progression with Simplified Outputs".
//! Isabelle's `fun formula_progression_alt` (defined there) is a different
//! thing from AFP's `lemma formula_progression_alt` (in `algorithm.rs`);
//! here it is `formula_progression_alt_spec` / `formula_progression_alt`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithm::*;
use crate::correctness::*;
use crate::simp::*;
use mltl_eval::trace::*;

verus! {

// ---------------------------------------------------------------------------
// Progression and semantic equivalence on non-empty traces
// ---------------------------------------------------------------------------

/// `formula_progression_CE_nonempty`
pub proof fn formula_progression_CE_nonempty<A>(phi: Mltl<A>, phi2: Mltl<A>, pi: Seq<Set<A>>, rho: Seq<Set<A>>)
    requires
        semantic_equiv(phi, phi2),
        intervals_welldef(phi),
        intervals_welldef(phi2),
        rho.len() != 0,
    ensures
        semantics_mltl(rho, formula_progression_spec(phi, pi)) == semantics_mltl(rho, formula_progression_spec(phi2, pi)),
{
    formula_progression_semantics(phi, pi, rho);
    formula_progression_semantics(phi2, pi, rho);
    assert(semantics_mltl(pi + rho, phi) == semantics_mltl(pi + rho, phi2));
}

/// `fp_len1_nonempty_equiv`
pub proof fn fp_len1_nonempty_equiv<A>(phi: Mltl<A>, phi2: Mltl<A>, h: Set<A>, rho: Seq<Set<A>>)
    requires
        semantic_equiv(phi, phi2),
        intervals_welldef(phi),
        intervals_welldef(phi2),
        rho.len() != 0,
    ensures
        semantics_mltl(rho, formula_progression_len1_spec(phi, h))
            == semantics_mltl(rho, formula_progression_len1_spec(phi2, h)),
{
    formula_progression_CE_nonempty(phi, phi2, seq![h], rho);
    assert(seq![h][0] == h);
}

/// `fp_nonempty_taut`
pub proof fn fp_nonempty_taut<A>(phi: Mltl<A>, pi: Seq<Set<A>>, sigma: Seq<Set<A>>)
    requires
        forall|rho: Seq<Set<A>>| rho.len() != 0 ==> #[trigger] semantics_mltl(rho, phi),
        intervals_welldef(phi),
        sigma.len() != 0,
    ensures
        semantics_mltl(sigma, formula_progression_spec(phi, pi)),
{
    formula_progression_semantics(phi, pi, sigma);
    assert(semantics_mltl(pi + sigma, phi));
}

/// `fp_nonempty_contradict`
pub proof fn fp_nonempty_contradict<A>(phi: Mltl<A>, pi: Seq<Set<A>>, sigma: Seq<Set<A>>)
    requires
        forall|rho: Seq<Set<A>>| rho.len() != 0 ==> !#[trigger] semantics_mltl(rho, phi),
        intervals_welldef(phi),
        sigma.len() != 0,
    ensures
        !semantics_mltl(sigma, formula_progression_spec(phi, pi)),
{
    formula_progression_semantics(phi, pi, sigma);
    assert(!semantics_mltl(pi + sigma, phi));
}

// ---------------------------------------------------------------------------
// Simplified progression
// ---------------------------------------------------------------------------

/// `formula_progression_alt φ π` (Extended theory): progress one state,
/// simplify, and stop early once the result is True or False.
pub open spec fn formula_progression_alt_spec<A>(f: Mltl<A>, tr: Seq<Set<A>>) -> Mltl<A>
    decreases tr.len(),
{
    if tr.len() == 0 {
        f
    } else {
        let h_result = simp_mltl_spec(formula_progression_len1_spec(f, tr[0]));
        if h_result == Mltl::<A>::True || h_result == Mltl::<A>::False {
            h_result
        } else {
            formula_progression_alt_spec(h_result, drop(tr, 1))
        }
    }
}

/// `prog φ π = simp_duals (formula_progression_alt φ π)`
pub open spec fn prog_spec<A>(f: Mltl<A>, tr: Seq<Set<A>>) -> Mltl<A> {
    simp_duals_spec(formula_progression_alt_spec(f, tr))
}

/// `fp_alt_welldef`
pub proof fn fp_alt_welldef<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        intervals_welldef(formula_progression_alt_spec(phi, pi)),
    decreases pi.len(),
{
    if pi.len() > 0 {
        let x = formula_progression_len1_spec(phi, pi[0]);
        formula_progression_well_definedness_preserved_len1(phi, pi[0]);
        simp_mltl_welldef(x);
        fp_alt_welldef(simp_mltl_spec(x), drop(pi, 1));
    }
}

/// Helper (not in Isabelle): progressing a constant leaves it unchanged.
pub proof fn formula_progression_constant<A>(c: Mltl<A>, pi: Seq<Set<A>>)
    requires
        c == Mltl::<A>::True || c == Mltl::<A>::False,
    ensures
        formula_progression_spec(c, pi) == c,
    decreases pi.len(),
{
    if pi.len() > 1 {
        formula_progression_constant(c, drop(pi, 1));
    }
}

/// Helper (not in Isabelle): unfolding `formula_progression` on `h # T`.
proof fn formula_progression_cons<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        pi.len() != 0,
    ensures
        formula_progression_spec(phi, pi)
            == formula_progression_spec(formula_progression_len1_spec(phi, pi[0]), drop(pi, 1)),
{
}

/// `formula_progression_alt_equiv_nonempty`
pub proof fn formula_progression_alt_equiv_nonempty<A>(phi: Mltl<A>, pi: Seq<Set<A>>, rho: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        rho.len() != 0,
    ensures
        semantics_mltl(rho, formula_progression_spec(phi, pi))
            == semantics_mltl(rho, formula_progression_alt_spec(phi, pi)),
    decreases pi.len(),
{
    if pi.len() > 0 {
        let t = drop(pi, 1);
        let x = formula_progression_len1_spec(phi, pi[0]);
        let h = simp_mltl_spec(x);
        formula_progression_cons(phi, pi);
        formula_progression_well_definedness_preserved_len1(phi, pi[0]);
        simp_mltl_correct(x);
        simp_mltl_welldef(x);
        formula_progression_CE_nonempty(x, h, t, rho);
        if h == Mltl::<A>::True || h == Mltl::<A>::False {
            formula_progression_constant(h, t);
        } else {
            formula_progression_alt_equiv_nonempty(h, t, rho);
        }
    }
}

/// Helper (not in Isabelle): on non-empty traces `prog` agrees with plain
/// progression.
pub proof fn prog_semantics<A>(phi: Mltl<A>, pi: Seq<Set<A>>, rho: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        rho.len() != 0,
    ensures
        semantics_mltl(rho, prog_spec(phi, pi)) == semantics_mltl(pi + rho, phi),
{
    let x = formula_progression_alt_spec(phi, pi);
    fp_alt_welldef(phi, pi);
    simp_duals_correct(x);
    assert(semantics_mltl(rho, simp_duals_spec(x)) == semantics_mltl(rho, x));
    formula_progression_alt_equiv_nonempty(phi, pi, rho);
    formula_progression_semantics(phi, pi, rho);
}

/// `prog_early_eval` (main theorem of the Extended theory).
///
/// Forward: a syntactic True/False output means every non-empty extension
/// of `π` agrees on `φ`. Weak converse: if every non-empty extension agrees,
/// `prog` is true/false on every non-empty trace.
pub proof fn prog_early_eval<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        prog_spec(phi, pi) == Mltl::<A>::True
            ==> forall|pi2: Seq<Set<A>>| pi2.len() != 0 ==> #[trigger] semantics_mltl(pi + pi2, phi),
        prog_spec(phi, pi) == Mltl::<A>::False
            ==> forall|pi2: Seq<Set<A>>| pi2.len() != 0 ==> !#[trigger] semantics_mltl(pi + pi2, phi),
        (forall|pi2: Seq<Set<A>>| pi2.len() != 0 ==> #[trigger] semantics_mltl(pi + pi2, phi))
            ==> forall|rho: Seq<Set<A>>| rho.len() != 0 ==> #[trigger] semantics_mltl(rho, prog_spec(phi, pi)),
        (forall|pi2: Seq<Set<A>>| pi2.len() != 0 ==> !#[trigger] semantics_mltl(pi + pi2, phi))
            ==> forall|rho: Seq<Set<A>>| rho.len() != 0 ==> !#[trigger] semantics_mltl(rho, prog_spec(phi, pi)),
{
    assert forall|rho: Seq<Set<A>>| rho.len() != 0 implies
        #[trigger] semantics_mltl(rho, prog_spec(phi, pi)) == semantics_mltl(pi + rho, phi) by {
        prog_semantics(phi, pi, rho);
    }
    if prog_spec(phi, pi) == Mltl::<A>::True {
        assert forall|pi2: Seq<Set<A>>| pi2.len() != 0 implies #[trigger] semantics_mltl(pi + pi2, phi) by {
            assert(semantics_mltl(pi2, prog_spec(phi, pi)));
        }
    }
    if prog_spec(phi, pi) == Mltl::<A>::False {
        assert forall|pi2: Seq<Set<A>>| pi2.len() != 0 implies !#[trigger] semantics_mltl(pi + pi2, phi) by {
            assert(!semantics_mltl(pi2, prog_spec(phi, pi)));
        }
    }
}

// ---------------------------------------------------------------------------
// Executable simplified progression
// ---------------------------------------------------------------------------

/// Executable `formula_progression_alt` (Extended theory), taking
/// ownership: a loop with an early exit once the formula is True or False.
pub fn formula_progression_alt_owned(f: Mltl<usize>, tr: &Trace) -> (r: Mltl<usize>)
    ensures
        r == formula_progression_alt_spec(f, trace_view(tr@)),
{
    let ghost tv = trace_view(tr@);
    let ghost f0 = f;
    let mut cur = f;
    let mut i: usize = 0;
    proof {
        lemma_drop_zero(tv);
    }
    while i < tr.len()
        invariant
            i <= tr.len(),
            tv == trace_view(tr@),
            f0 == f,
            formula_progression_alt_spec(f0, tv) == formula_progression_alt_spec(cur, drop(tv, i as nat)),
        decreases tr.len() - i,
    {
        let ghost c0 = cur;
        let h = simp_mltl(formula_progression_len1_owned(cur, &tr[i]));
        proof {
            lemma_drop_drop(tv, i as nat, 1);
            assert(drop(tv, i as nat)[0] == tv[i as int]);
            assert(formula_progression_alt_spec(f0, tv) == formula_progression_alt_spec(c0, drop(tv, i as nat)));
        }
        if is_true_mltl(&h) || is_false_mltl(&h) {
            proof {
                assert(drop(tv, i as nat).len() != 0);
                assert(formula_progression_alt_spec(f0, tv) == h);
            }
            return h;
        }
        cur = h;
        i = i + 1;
    }
    proof {
        lemma_drop_past_end(tv, i as nat);
    }
    cur
}

/// Executable `formula_progression_alt` (Extended theory).
pub fn formula_progression_alt(f: &Mltl<usize>, tr: &Trace) -> (r: Mltl<usize>)
    ensures
        r == formula_progression_alt_spec(*f, trace_view(tr@)),
{
    formula_progression_alt_owned(clone_mltl(f), tr)
}

/// Executable `prog` taking ownership (no copy of `f`; use this when
/// progressing a formula step by step).
pub fn prog_owned(f: Mltl<usize>, tr: &Trace) -> (r: Mltl<usize>)
    ensures
        r == prog_spec(f, trace_view(tr@)),
        // On every non-empty continuation `rho` of the trace, the result
        // holds iff the whole trace satisfies `f` (from Theorem 2) ...
        intervals_welldef(f) ==> forall|rho: Seq<Set<usize>>| rho.len() != 0 ==>
            (#[trigger] semantics_mltl(rho, r) == semantics_mltl(trace_view(tr@) + rho, f)),
        // ... so a True/False result is a final verdict (`prog_early_eval`).
        intervals_welldef(f) && r == Mltl::<usize>::True ==> forall|rho: Seq<Set<usize>>| rho.len() != 0 ==>
            #[trigger] semantics_mltl(trace_view(tr@) + rho, f),
        intervals_welldef(f) && r == Mltl::<usize>::False ==> forall|rho: Seq<Set<usize>>| rho.len() != 0 ==>
            !#[trigger] semantics_mltl(trace_view(tr@) + rho, f),
{
    let ghost f0 = f;
    let r = simp_duals(formula_progression_alt_owned(f, tr));
    proof {
        if intervals_welldef(f0) {
            assert forall|rho: Seq<Set<usize>>| rho.len() != 0 implies
                #[trigger] semantics_mltl(rho, r) == semantics_mltl(trace_view(tr@) + rho, f0) by {
                prog_semantics(f0, trace_view(tr@), rho);
            }
            assert forall|rho: Seq<Set<usize>>| rho.len() != 0 implies
                #[trigger] semantics_mltl(trace_view(tr@) + rho, f0) == semantics_mltl(rho, r) by {
                prog_semantics(f0, trace_view(tr@), rho);
            }
        }
    }
    r
}

/// Executable `prog`: progress `f` over the trace, simplifying after every
/// state and stopping early at True/False; finally undo `Not … Not` shapes.
pub fn prog(f: &Mltl<usize>, tr: &Trace) -> (r: Mltl<usize>)
    ensures
        // Computes exactly Isabelle's `prog f π` ...
        r == prog_spec(*f, trace_view(tr@)),
        // On every non-empty continuation `rho` of the trace, the result
        // holds iff the whole trace satisfies `f` (from Theorem 2) ...
        intervals_welldef(*f) ==> forall|rho: Seq<Set<usize>>| rho.len() != 0 ==>
            (#[trigger] semantics_mltl(rho, r) == semantics_mltl(trace_view(tr@) + rho, *f)),
        // ... so a True/False result is a final verdict (`prog_early_eval`).
        intervals_welldef(*f) && r == Mltl::<usize>::True ==> forall|rho: Seq<Set<usize>>| rho.len() != 0 ==>
            #[trigger] semantics_mltl(trace_view(tr@) + rho, *f),
        intervals_welldef(*f) && r == Mltl::<usize>::False ==> forall|rho: Seq<Set<usize>>| rho.len() != 0 ==>
            !#[trigger] semantics_mltl(trace_view(tr@) + rho, *f),
{
    prog_owned(clone_mltl(f), tr)
}

} // verus!
