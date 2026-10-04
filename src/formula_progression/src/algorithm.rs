//! Formula progression: the algorithm and its structural properties.
//!
//! Mirrors `MLTL_Formula_Progression.thy`, subsection Algorithm, plus the
//! well-definedness lemmas and Theorem 1 (decomposition).
use vstd::prelude::*;
use std::collections::HashSet;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use mltl_eval::trace::*;
#[cfg(verus_only)]
use crate::correctness::{formula_progression_correctness, formula_progression_semantics};

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

// ---------------------------------------------------------------------------
// Algorithm
// ---------------------------------------------------------------------------

/// `weight_operators φ`: the termination measure of
/// `formula_progression_len1` (Release and Global recurse on a rewritten,
/// lighter formula).
pub open spec fn weight_operators<A>(f: Mltl<A>) -> nat
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::And(f1, f2) | Mltl::Or(f1, f2) => weight_operators(*f1) + weight_operators(*f2) + 1,
        Mltl::Not(g) => 1 + weight_operators(*g),
        Mltl::Until(f1, a, b, f2) => (weight_operators(*f1) + weight_operators(*f2) + 1 + a + b) as nat,
        Mltl::Release(f1, a, b, f2) => (10 + weight_operators(*f1) + weight_operators(*f2) + 1 + a + b) as nat,
        Mltl::Global(a, b, g) => (10 + weight_operators(*g) + a + b) as nat,
        Mltl::Future(a, b, g) => (1 + weight_operators(*g) + a + b) as nat,
    }
}

/// `formula_progression_len1 φ s`: progress `φ` over a single trace state `s`.
///
/// Case for case with Isabelle. `a-1`, `b-1` are guarded by `0 < a ≤ b` or
/// `0 = a < b`, so `nat` and `usize` subtraction agree.
pub open spec fn formula_progression_len1_spec<A>(f: Mltl<A>, s: Set<A>) -> Mltl<A>
    decreases weight_operators(f),
    via formula_progression_len1_spec_decreases::<A>
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(p) => if s.contains(p) { Mltl::True } else { Mltl::False },
        Mltl::Not(g) => Mltl::Not(Box::new(formula_progression_len1_spec(*g, s))),
        Mltl::And(f1, f2) => Mltl::And(
            Box::new(formula_progression_len1_spec(*f1, s)),
            Box::new(formula_progression_len1_spec(*f2, s)),
        ),
        Mltl::Or(f1, f2) => Mltl::Or(
            Box::new(formula_progression_len1_spec(*f1, s)),
            Box::new(formula_progression_len1_spec(*f2, s)),
        ),
        Mltl::Until(f1, a, b, f2) =>
            if 0 < a && a <= b {
                Mltl::Until(f1, (a - 1) as usize, (b - 1) as usize, f2)
            } else if 0 == a && a < b {
                Mltl::Or(
                    Box::new(formula_progression_len1_spec(*f2, s)),
                    Box::new(Mltl::And(
                        Box::new(formula_progression_len1_spec(*f1, s)),
                        Box::new(Mltl::Until(f1, 0, (b - 1) as usize, f2)),
                    )),
                )
            } else {
                formula_progression_len1_spec(*f2, s)
            },
        Mltl::Release(f1, a, b, f2) => Mltl::Not(Box::new(formula_progression_len1_spec(
            Mltl::Until(Box::new(Mltl::Not(f1)), a, b, Box::new(Mltl::Not(f2))),
            s,
        ))),
        Mltl::Global(a, b, g) => Mltl::Not(Box::new(formula_progression_len1_spec(
            Mltl::Future(a, b, Box::new(Mltl::Not(g))),
            s,
        ))),
        Mltl::Future(a, b, g) =>
            if 0 < a && a <= b {
                Mltl::Future((a - 1) as usize, (b - 1) as usize, g)
            } else if 0 == a && a < b {
                Mltl::Or(
                    Box::new(formula_progression_len1_spec(*g, s)),
                    Box::new(Mltl::Future(0, (b - 1) as usize, g)),
                )
            } else {
                formula_progression_len1_spec(*g, s)
            },
    }
}

#[via_fn]
proof fn formula_progression_len1_spec_decreases<A>(f: Mltl<A>, s: Set<A>) {
    reveal_with_fuel(weight_operators, 3);
}

/// `formula_progression φ π`: progress `φ` over every state of `π`, in order.
/// On the empty trace it returns `φ` (as in Isabelle).
pub open spec fn formula_progression_spec<A>(f: Mltl<A>, tr: Seq<Set<A>>) -> Mltl<A>
    decreases tr.len(),
{
    if tr.len() == 0 {
        f
    } else if tr.len() == 1 {
        formula_progression_len1_spec(f, tr[0])
    } else {
        formula_progression_spec(formula_progression_len1_spec(f, tr[0]), drop(tr, 1))
    }
}

/// The step function of `formula_progression_alt`'s fold.
pub open spec fn fp_step<A>() -> spec_fn(Mltl<A>, Set<A>) -> Mltl<A> {
    |g: Mltl<A>, x: Set<A>| formula_progression_len1_spec(g, x)
}

/// Helper (not in Isabelle): progressing over `π @ [s]` is one more step.
pub proof fn formula_progression_snoc<A>(f: Mltl<A>, tr: Seq<Set<A>>, s: Set<A>)
    ensures
        formula_progression_spec(f, tr.push(s))
            == formula_progression_len1_spec(formula_progression_spec(f, tr), s),
    decreases tr.len(),
{
    if tr.len() == 0 {
        assert(tr.push(s)[0] == s);
    } else {
        let g = formula_progression_len1_spec(f, tr[0]);
        assert(tr.push(s)[0] == tr[0]);
        assert(drop(tr.push(s), 1) =~= drop(tr, 1).push(s));
        formula_progression_snoc(g, drop(tr, 1), s);
        if tr.len() == 1 {
            assert(drop(tr, 1).len() == 0);
        }
    }
}

/// `formula_progression_alt`: `formula_progression F xs = fold (λx F. len1 F x) xs F`.
/// Isabelle's `fold` on lists is vstd's `fold_left` (state first, then element).
pub proof fn formula_progression_alt<A>(f: Mltl<A>, xs: Seq<Set<A>>)
    ensures
        formula_progression_spec(f, xs) == xs.fold_left(f, fp_step()),
    decreases xs.len(),
{
    if xs.len() > 0 {
        formula_progression_alt(f, xs.drop_last());
        formula_progression_snoc(f, xs.drop_last(), xs.last());
        assert(xs.drop_last().push(xs.last()) =~= xs);
    }
}

/// Helper (not in Isabelle): `formula_progression φ (xs @ ys)
/// = formula_progression (formula_progression φ xs) ys`.
pub proof fn formula_progression_append_traces<A>(f: Mltl<A>, xs: Seq<Set<A>>, ys: Seq<Set<A>>)
    ensures
        formula_progression_spec(f, xs + ys)
            == formula_progression_spec(formula_progression_spec(f, xs), ys),
    decreases ys.len(),
{
    if ys.len() == 0 {
        assert(xs + ys =~= xs);
    } else {
        let ys0 = ys.drop_last();
        formula_progression_append_traces(f, xs, ys0);
        assert(xs + ys =~= (xs + ys0).push(ys.last()));
        assert(ys =~= ys0.push(ys.last()));
        formula_progression_snoc(f, xs + ys0, ys.last());
        formula_progression_snoc(formula_progression_spec(f, xs), ys0, ys.last());
    }
}

// ---------------------------------------------------------------------------
// Empty trace semantics
// ---------------------------------------------------------------------------

/// `semantics_global`: `[] ⊨ G[0,1] φ`
pub proof fn semantics_global<A>(phi: Mltl<A>)
    ensures
        semantics_mltl(Seq::<Set<A>>::empty(), Mltl::Global(0, 1, Box::new(phi))),
{
}

/// `semantics_future`: `[] ⊨ Not (F[0,1] (Not φ))`
pub proof fn semantics_future<A>(phi: Mltl<A>)
    ensures
        semantics_mltl(
            Seq::<Set<A>>::empty(),
            Mltl::Not(Box::new(Mltl::Future(0, 1, Box::new(Mltl::Not(Box::new(phi)))))),
        ),
{
    reveal_with_fuel(semantics_mltl, 2);
}

// ---------------------------------------------------------------------------
// Well-definedness
// ---------------------------------------------------------------------------

pub proof fn formula_progression_well_definedness_preserved_len1<A>(phi: Mltl<A>, s: Set<A>)
    requires
        intervals_welldef(phi),
    ensures
        intervals_welldef(formula_progression_len1_spec(phi, s)),
    decreases weight_operators(phi),
{
    match phi {
        Mltl::Not(g) => formula_progression_well_definedness_preserved_len1(*g, s),
        Mltl::And(f1, f2) => {
            formula_progression_well_definedness_preserved_len1(*f1, s);
            formula_progression_well_definedness_preserved_len1(*f2, s);
        },
        Mltl::Or(f1, f2) => {
            formula_progression_well_definedness_preserved_len1(*f1, s);
            formula_progression_well_definedness_preserved_len1(*f2, s);
        },
        Mltl::Until(f1, _, _, f2) => {
            reveal_with_fuel(intervals_welldef, 3);
            formula_progression_well_definedness_preserved_len1(*f1, s);
            formula_progression_well_definedness_preserved_len1(*f2, s);
        },
        Mltl::Release(f1, a, b, f2) => {
            let u = Mltl::Until(Box::new(Mltl::Not(f1)), a, b, Box::new(Mltl::Not(f2)));
            reveal_with_fuel(weight_operators, 2);
            reveal_with_fuel(intervals_welldef, 2);
            formula_progression_well_definedness_preserved_len1(u, s);
        },
        Mltl::Global(a, b, g) => {
            let fu = Mltl::Future(a, b, Box::new(Mltl::Not(g)));
            reveal_with_fuel(weight_operators, 2);
            reveal_with_fuel(intervals_welldef, 2);
            formula_progression_well_definedness_preserved_len1(fu, s);
        },
        Mltl::Future(_, _, g) => {
            reveal_with_fuel(intervals_welldef, 2);
            formula_progression_well_definedness_preserved_len1(*g, s);
        },
        _ => {},
    }
}

pub proof fn formula_progression_well_definedness_preserved<A>(phi: Mltl<A>, tr: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        intervals_welldef(formula_progression_spec(phi, tr)),
    decreases tr.len(),
{
    if tr.len() > 0 {
        formula_progression_well_definedness_preserved_len1(phi, tr[0]);
        formula_progression_well_definedness_preserved(formula_progression_len1_spec(phi, tr[0]), drop(tr, 1));
    }
}

// ---------------------------------------------------------------------------
// Theorem 1
// ---------------------------------------------------------------------------

/// `formula_progression_identity`: helper for Theorem 1.
pub proof fn formula_progression_identity<A>(phi: Mltl<A>, tr: Seq<Set<A>>, k: nat)
    requires
        k < tr.len(),
    ensures
        formula_progression_spec(formula_progression_spec(phi, take(tr, k)), seq![tr[k as int]])
            == formula_progression_spec(phi, take(tr, k + 1)),
{
    formula_progression_snoc(phi, take(tr, k), tr[k as int]);
    assert(take(tr, k).push(tr[k as int]) =~= take(tr, k + 1));
    assert(seq![tr[k as int]][0] == tr[k as int]);
}

/// Theorem 1, `formula_progression_decomposition`.
pub proof fn formula_progression_decomposition<A>(phi: Mltl<A>, tr: Seq<Set<A>>, k: nat)
    requires
        k >= 1,
        k <= tr.len(),
    ensures
        formula_progression_spec(formula_progression_spec(phi, take(tr, k)), drop(tr, k))
            == formula_progression_spec(phi, tr),
{
    formula_progression_append_traces(phi, take(tr, k), drop(tr, k));
    assert(take(tr, k) + drop(tr, k) =~= tr);
}

// ---------------------------------------------------------------------------
// Executable progression (spec/exec pairs: result == the spec)
// ---------------------------------------------------------------------------

/// Executable `formula_progression_len1`.
///
/// Release and Global are computed directly from their operands, without
/// building the rewritten formula the spec recurses on (so the recursion is
/// structural); the result is the same.
pub fn formula_progression_len1(f: &Mltl<usize>, s: &HashSet<usize>) -> (r: Mltl<usize>)
    ensures
        r == formula_progression_len1_spec(*f, s@),
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(p) => if s.contains(p) { Mltl::True } else { Mltl::False },
        Mltl::Not(g) => Mltl::Not(Box::new(formula_progression_len1(g, s))),
        Mltl::And(f1, f2) => Mltl::And(
            Box::new(formula_progression_len1(f1, s)),
            Box::new(formula_progression_len1(f2, s)),
        ),
        Mltl::Or(f1, f2) => Mltl::Or(
            Box::new(formula_progression_len1(f1, s)),
            Box::new(formula_progression_len1(f2, s)),
        ),
        Mltl::Until(f1, a, b, f2) => {
            let (a, b) = (*a, *b);
            if 0 < a && a <= b {
                Mltl::Until(Box::new(clone_mltl(f1)), a - 1, b - 1, Box::new(clone_mltl(f2)))
            } else if 0 == a && a < b {
                Mltl::Or(
                    Box::new(formula_progression_len1(f2, s)),
                    Box::new(Mltl::And(
                        Box::new(formula_progression_len1(f1, s)),
                        Box::new(Mltl::Until(Box::new(clone_mltl(f1)), 0, b - 1, Box::new(clone_mltl(f2)))),
                    )),
                )
            } else {
                formula_progression_len1(f2, s)
            }
        },
        Mltl::Release(f1, a, b, f2) => {
            // len1 (Not f1 U[a,b] Not f2), negated.
            let (a, b) = (*a, *b);
            let ghost nf1 = Mltl::Not(Box::new(**f1));
            let ghost nf2 = Mltl::Not(Box::new(**f2));
            let u = if 0 < a && a <= b {
                Mltl::Until(
                    Box::new(Mltl::Not(Box::new(clone_mltl(f1)))), a - 1, b - 1,
                    Box::new(Mltl::Not(Box::new(clone_mltl(f2)))),
                )
            } else if 0 == a && a < b {
                Mltl::Or(
                    Box::new(Mltl::Not(Box::new(formula_progression_len1(f2, s)))),
                    Box::new(Mltl::And(
                        Box::new(Mltl::Not(Box::new(formula_progression_len1(f1, s)))),
                        Box::new(Mltl::Until(
                            Box::new(Mltl::Not(Box::new(clone_mltl(f1)))), 0, b - 1,
                            Box::new(Mltl::Not(Box::new(clone_mltl(f2)))),
                        )),
                    )),
                )
            } else {
                Mltl::Not(Box::new(formula_progression_len1(f2, s)))
            };
            proof {
                assert(formula_progression_len1_spec(nf1, s@) == Mltl::Not(Box::new(formula_progression_len1_spec(**f1, s@))));
                assert(formula_progression_len1_spec(nf2, s@) == Mltl::Not(Box::new(formula_progression_len1_spec(**f2, s@))));
                assert(u == formula_progression_len1_spec(Mltl::Until(Box::new(nf1), a, b, Box::new(nf2)), s@));
            }
            Mltl::Not(Box::new(u))
        },
        Mltl::Global(a, b, g) => {
            // len1 (F[a,b] Not g), negated.
            let (a, b) = (*a, *b);
            let ghost ng = Mltl::Not(Box::new(**g));
            let fu = if 0 < a && a <= b {
                Mltl::Future(a - 1, b - 1, Box::new(Mltl::Not(Box::new(clone_mltl(g)))))
            } else if 0 == a && a < b {
                Mltl::Or(
                    Box::new(Mltl::Not(Box::new(formula_progression_len1(g, s)))),
                    Box::new(Mltl::Future(0, b - 1, Box::new(Mltl::Not(Box::new(clone_mltl(g)))))),
                )
            } else {
                Mltl::Not(Box::new(formula_progression_len1(g, s)))
            };
            proof {
                assert(formula_progression_len1_spec(ng, s@) == Mltl::Not(Box::new(formula_progression_len1_spec(**g, s@))));
                assert(fu == formula_progression_len1_spec(Mltl::Future(a, b, Box::new(ng)), s@));
            }
            Mltl::Not(Box::new(fu))
        },
        Mltl::Future(a, b, g) => {
            let (a, b) = (*a, *b);
            if 0 < a && a <= b {
                Mltl::Future(a - 1, b - 1, Box::new(clone_mltl(g)))
            } else if 0 == a && a < b {
                Mltl::Or(
                    Box::new(formula_progression_len1(g, s)),
                    Box::new(Mltl::Future(0, b - 1, Box::new(clone_mltl(g)))),
                )
            } else {
                formula_progression_len1(g, s)
            }
        },
    }
}

/// Executable `formula_progression_len1` taking ownership: operands that
/// reappear in the result are moved and boxes are reused, instead of
/// copying (`formula_progression_len1` borrows and must copy). Same result.
pub fn formula_progression_len1_owned(f: Mltl<usize>, s: &HashSet<usize>) -> (r: Mltl<usize>)
    ensures
        r == formula_progression_len1_spec(f, s@),
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(p) => if s.contains(&p) { Mltl::True } else { Mltl::False },
        Mltl::Not(mut g) => {
            *g = formula_progression_len1_owned(*g, s);
            Mltl::Not(g)
        },
        Mltl::And(mut f1, mut f2) => {
            *f1 = formula_progression_len1_owned(*f1, s);
            *f2 = formula_progression_len1_owned(*f2, s);
            Mltl::And(f1, f2)
        },
        Mltl::Or(mut f1, mut f2) => {
            *f1 = formula_progression_len1_owned(*f1, s);
            *f2 = formula_progression_len1_owned(*f2, s);
            Mltl::Or(f1, f2)
        },
        Mltl::Until(f1, a, b, f2) => {
            if 0 < a && a <= b {
                Mltl::Until(f1, a - 1, b - 1, f2)
            } else if 0 == a && a < b {
                let l2 = formula_progression_len1(&f2, s);
                let l1 = formula_progression_len1(&f1, s);
                Mltl::Or(Box::new(l2), Box::new(Mltl::And(Box::new(l1), Box::new(Mltl::Until(f1, 0, b - 1, f2)))))
            } else {
                formula_progression_len1_owned(*f2, s)
            }
        },
        Mltl::Release(f1, a, b, f2) => {
            // len1 (Not f1 U[a,b] Not f2), negated.
            let ghost nf1 = Mltl::Not(Box::new(*f1));
            let ghost nf2 = Mltl::Not(Box::new(*f2));
            let ghost (g1, g2) = (*f1, *f2);
            let u = if 0 < a && a <= b {
                Mltl::Until(Box::new(Mltl::Not(f1)), a - 1, b - 1, Box::new(Mltl::Not(f2)))
            } else if 0 == a && a < b {
                let l2 = formula_progression_len1(&f2, s);
                let l1 = formula_progression_len1(&f1, s);
                Mltl::Or(
                    Box::new(Mltl::Not(Box::new(l2))),
                    Box::new(Mltl::And(
                        Box::new(Mltl::Not(Box::new(l1))),
                        Box::new(Mltl::Until(Box::new(Mltl::Not(f1)), 0, b - 1, Box::new(Mltl::Not(f2)))),
                    )),
                )
            } else {
                Mltl::Not(Box::new(formula_progression_len1_owned(*f2, s)))
            };
            proof {
                assert(formula_progression_len1_spec(nf1, s@) == Mltl::Not(Box::new(formula_progression_len1_spec(g1, s@))));
                assert(formula_progression_len1_spec(nf2, s@) == Mltl::Not(Box::new(formula_progression_len1_spec(g2, s@))));
                assert(u == formula_progression_len1_spec(Mltl::Until(Box::new(nf1), a, b, Box::new(nf2)), s@));
            }
            Mltl::Not(Box::new(u))
        },
        Mltl::Global(a, b, g) => {
            // len1 (F[a,b] Not g), negated.
            let ghost ng = Mltl::Not(Box::new(*g));
            let ghost g0 = *g;
            let fu = if 0 < a && a <= b {
                Mltl::Future(a - 1, b - 1, Box::new(Mltl::Not(g)))
            } else if 0 == a && a < b {
                let l = formula_progression_len1(&g, s);
                Mltl::Or(Box::new(Mltl::Not(Box::new(l))), Box::new(Mltl::Future(0, b - 1, Box::new(Mltl::Not(g)))))
            } else {
                Mltl::Not(Box::new(formula_progression_len1_owned(*g, s)))
            };
            proof {
                assert(formula_progression_len1_spec(ng, s@) == Mltl::Not(Box::new(formula_progression_len1_spec(g0, s@))));
                assert(fu == formula_progression_len1_spec(Mltl::Future(a, b, Box::new(ng)), s@));
            }
            Mltl::Not(Box::new(fu))
        },
        Mltl::Future(a, b, g) => {
            if 0 < a && a <= b {
                Mltl::Future(a - 1, b - 1, g)
            } else if 0 == a && a < b {
                let l = formula_progression_len1(&g, s);
                Mltl::Or(Box::new(l), Box::new(Mltl::Future(0, b - 1, g)))
            } else {
                formula_progression_len1_owned(*g, s)
            }
        },
    }
}

/// Executable `formula_progression`: one `formula_progression_len1` step per
/// trace state, in a loop (the fold form, `formula_progression_alt`).
pub fn formula_progression(f: &Mltl<usize>, tr: &Trace) -> (r: Mltl<usize>)
    ensures
        // Computes exactly AFP's `formula_progression f π` ...
        r == formula_progression_spec(*f, trace_view(tr@)),
        // ... which holds on a non-empty continuation `rho` iff the whole
        // trace satisfies `f` (Theorem 2, `satisfiability_preservation`) ...
        intervals_welldef(*f) ==> forall|rho: Seq<Set<usize>>| rho.len() != 0 ==>
            (#[trigger] semantics_mltl(rho, r) == semantics_mltl(trace_view(tr@) + rho, *f)),
        // ... and, once the trace is at least as long as `f`'s computation
        // length, is equivalent to True iff the trace satisfies `f`
        // (Theorem 3, `formula_progression_correctness`).
        intervals_welldef(*f) && tr.len() >= complen_mltl(*f) ==>
            (semantic_equiv(r, Mltl::True) == semantics_mltl(trace_view(tr@), *f)),
{
    let ghost tv = trace_view(tr@);
    let mut cur = clone_mltl(f);
    let mut i: usize = 0;
    proof {
        assert(take(tv, 0) =~= Seq::<Set<usize>>::empty());
    }
    while i < tr.len()
        invariant
            i <= tr.len(),
            tv == trace_view(tr@),
            cur == formula_progression_spec(*f, take(tv, i as nat)),
        decreases tr.len() - i,
    {
        proof {
            formula_progression_snoc(*f, take(tv, i as nat), tv[i as int]);
            assert(take(tv, i as nat).push(tv[i as int]) =~= take(tv, (i + 1) as nat));
        }
        cur = formula_progression_len1_owned(cur, &tr[i]);
        i = i + 1;
    }
    proof {
        assert(take(tv, i as nat) =~= tv);
        if intervals_welldef(*f) {
            assert forall|rho: Seq<Set<usize>>| rho.len() != 0 implies
                #[trigger] semantics_mltl(rho, cur) == semantics_mltl(tv + rho, *f) by {
                formula_progression_semantics(*f, tv, rho);
            }
            if tr.len() >= complen_mltl(*f) {
                formula_progression_correctness(*f, tv);
            }
        }
    }
    cur
}

} // verus!
