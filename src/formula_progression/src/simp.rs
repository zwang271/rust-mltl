//! Formula simplifiers used by the simplified progression (`extended.rs`).
//!
//! Mirrors the unpublished `Formula_Progression_Extended.thy`, section
//! "Simp MLTL Function", plus `simp_duals` and `simp_duals_correct`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;

verus! {

// ---------------------------------------------------------------------------
// simp_mltl_aux, simp_mltl
// ---------------------------------------------------------------------------

/// `simp_mltl_aux φ`: one pass of constant folding and idempotence; the flag
/// says whether anything changed. Clauses in Isabelle's (first-match) order.
pub open spec fn simp_mltl_aux_spec<A>(f: Mltl<A>) -> (Mltl<A>, bool)
    decreases f,
{
    match f {
        Mltl::Not(g) => match *g {
            Mltl::True => (Mltl::False, true),
            Mltl::False => (Mltl::True, true),
            Mltl::Not(phi) => (*phi, true),
            _ => {
                let (g2, p) = simp_mltl_aux_spec(*g);
                (Mltl::Not(Box::new(g2)), p)
            },
        },
        Mltl::Or(phi, psi) =>
            if *phi == Mltl::<A>::True || *psi == Mltl::<A>::True {
                (Mltl::True, true)
            } else if *phi == Mltl::<A>::False {
                (simp_mltl_aux_spec(*psi).0, true)
            } else if *psi == Mltl::<A>::False {
                (simp_mltl_aux_spec(*phi).0, true)
            } else if phi == psi {
                (simp_mltl_aux_spec(*phi).0, true)
            } else {
                let (p1, b1) = simp_mltl_aux_spec(*phi);
                let (p2, b2) = simp_mltl_aux_spec(*psi);
                (Mltl::Or(Box::new(p1), Box::new(p2)), b1 || b2)
            },
        Mltl::And(phi, psi) =>
            if *phi == Mltl::<A>::False || *psi == Mltl::<A>::False {
                (Mltl::False, true)
            } else if *phi == Mltl::<A>::True {
                (simp_mltl_aux_spec(*psi).0, true)
            } else if *psi == Mltl::<A>::True {
                (simp_mltl_aux_spec(*phi).0, true)
            } else if phi == psi {
                (simp_mltl_aux_spec(*phi).0, true)
            } else {
                let (p1, b1) = simp_mltl_aux_spec(*phi);
                let (p2, b2) = simp_mltl_aux_spec(*psi);
                (Mltl::And(Box::new(p1), Box::new(p2)), b1 || b2)
            },
        Mltl::Global(a, b, g) =>
            if *g == Mltl::<A>::True {
                (Mltl::True, true)
            } else {
                let (g2, p) = simp_mltl_aux_spec(*g);
                (Mltl::Global(a, b, Box::new(g2)), p)
            },
        Mltl::Future(a, b, g) =>
            if *g == Mltl::<A>::False {
                (Mltl::False, true)
            } else {
                let (g2, p) = simp_mltl_aux_spec(*g);
                (Mltl::Future(a, b, Box::new(g2)), p)
            },
        Mltl::Until(phi, a, b, psi) =>
            if *psi == Mltl::<A>::False {
                (Mltl::False, true)
            } else if *phi == Mltl::<A>::True {
                (Mltl::Future(a, b, Box::new(simp_mltl_aux_spec(*psi).0)), true)
            } else {
                let (p1, b1) = simp_mltl_aux_spec(*phi);
                let (p2, b2) = simp_mltl_aux_spec(*psi);
                (Mltl::Until(Box::new(p1), a, b, Box::new(p2)), b1 || b2)
            },
        Mltl::Release(phi, a, b, psi) =>
            if *psi == Mltl::<A>::True {
                (Mltl::True, true)
            } else if *phi == Mltl::<A>::False {
                (Mltl::Global(a, b, Box::new(simp_mltl_aux_spec(*psi).0)), true)
            } else {
                let (p1, b1) = simp_mltl_aux_spec(*phi);
                let (p2, b2) = simp_mltl_aux_spec(*psi);
                (Mltl::Release(Box::new(p1), a, b, Box::new(p2)), b1 || b2)
            },
        _ => (f, false),
    }
}

/// Helper (not in Isabelle): `simp_size_nondec`, `simp_size` and
/// `simp_mltl_nosimp` in one induction.
pub proof fn simp_mltl_aux_size<A>(f: Mltl<A>)
    ensures
        size_mltl(simp_mltl_aux_spec(f).0) <= size_mltl(f),
        simp_mltl_aux_spec(f).1 ==> size_mltl(simp_mltl_aux_spec(f).0) < size_mltl(f),
        !simp_mltl_aux_spec(f).1 ==> simp_mltl_aux_spec(f).0 == f,
    decreases f,
{
    match f {
        Mltl::Not(g) => {
            simp_mltl_aux_size(*g);
            reveal_with_fuel(size_mltl, 2);
        },
        Mltl::Or(phi, psi) => {
            simp_mltl_aux_size(*phi);
            simp_mltl_aux_size(*psi);
        },
        Mltl::And(phi, psi) => {
            simp_mltl_aux_size(*phi);
            simp_mltl_aux_size(*psi);
        },
        Mltl::Global(_, _, g) => simp_mltl_aux_size(*g),
        Mltl::Future(_, _, g) => simp_mltl_aux_size(*g),
        Mltl::Until(phi, _, _, psi) => {
            simp_mltl_aux_size(*phi);
            simp_mltl_aux_size(*psi);
        },
        Mltl::Release(phi, _, _, psi) => {
            simp_mltl_aux_size(*phi);
            simp_mltl_aux_size(*psi);
        },
        _ => {},
    }
}

pub proof fn simp_size_nondec<A>(f: Mltl<A>)
    ensures
        size_mltl(simp_mltl_aux_spec(f).0) <= size_mltl(f),
{
    simp_mltl_aux_size(f);
}

pub proof fn simp_size<A>(f: Mltl<A>)
    ensures
        simp_mltl_aux_spec(f).1 <==> size_mltl(simp_mltl_aux_spec(f).0) < size_mltl(f),
{
    simp_mltl_aux_size(f);
}

pub proof fn simp_mltl_nosimp<A>(f: Mltl<A>)
    ensures
        !simp_mltl_aux_spec(f).1 <==> f == simp_mltl_aux_spec(f).0,
{
    simp_mltl_aux_size(f);
}

/// `simp_mltl φ`: repeat `simp_mltl_aux` until nothing changes.
pub open spec fn simp_mltl_spec<A>(f: Mltl<A>) -> Mltl<A>
    decreases size_mltl(f),
    via simp_mltl_spec_decreases::<A>
{
    let r = simp_mltl_aux_spec(f);
    if r.1 == false { r.0 } else { simp_mltl_spec(r.0) }
}

#[via_fn]
proof fn simp_mltl_spec_decreases<A>(f: Mltl<A>) {
    simp_mltl_aux_size(f);
}

pub proof fn simp_mltl_aux_welldef<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        intervals_welldef(simp_mltl_aux_spec(f).0),
    decreases f,
{
    match f {
        Mltl::Not(g) => {
            reveal_with_fuel(intervals_welldef, 2);
            simp_mltl_aux_welldef(*g);
        },
        Mltl::Or(phi, psi) => {
            simp_mltl_aux_welldef(*phi);
            simp_mltl_aux_welldef(*psi);
        },
        Mltl::And(phi, psi) => {
            simp_mltl_aux_welldef(*phi);
            simp_mltl_aux_welldef(*psi);
        },
        Mltl::Global(_, _, g) => simp_mltl_aux_welldef(*g),
        Mltl::Future(_, _, g) => simp_mltl_aux_welldef(*g),
        Mltl::Until(phi, _, _, psi) => {
            simp_mltl_aux_welldef(*phi);
            simp_mltl_aux_welldef(*psi);
        },
        Mltl::Release(phi, _, _, psi) => {
            simp_mltl_aux_welldef(*phi);
            simp_mltl_aux_welldef(*psi);
        },
        _ => {},
    }
}

/// Not case of `simp_mltl_aux_correct`.
proof fn simp_mltl_aux_correct_not<A>(g: Mltl<A>)
    requires
        intervals_welldef(g),
        semantic_equiv(g, simp_mltl_aux_spec(g).0),
    ensures
        semantic_equiv(Mltl::Not(Box::new(g)), simp_mltl_aux_spec(Mltl::Not(Box::new(g))).0),
{
    let f = Mltl::Not(Box::new(g));
    match g {
        Mltl::True => { reveal_with_fuel(semantics_mltl, 2); },
        Mltl::False => { reveal_with_fuel(semantics_mltl, 2); },
        Mltl::Not(phi) => {
            not_not_equiv(*phi);
            semantic_equiv_symmetric(*phi, f);
        },
        _ => not_ce(g, simp_mltl_aux_spec(g).0),
    }
}

/// Or case of `simp_mltl_aux_correct`.
proof fn simp_mltl_aux_correct_or<A>(phi: Mltl<A>, psi: Mltl<A>)
    requires
        semantic_equiv(phi, simp_mltl_aux_spec(phi).0),
        semantic_equiv(psi, simp_mltl_aux_spec(psi).0),
    ensures
        semantic_equiv(Mltl::Or(Box::new(phi), Box::new(psi)), simp_mltl_aux_spec(Mltl::Or(Box::new(phi), Box::new(psi))).0),
{
    let f = Mltl::Or(Box::new(phi), Box::new(psi));
    let r = simp_mltl_aux_spec(f).0;
    let p1 = simp_mltl_aux_spec(phi).0;
    let p2 = simp_mltl_aux_spec(psi).0;
    if phi == Mltl::<A>::True || psi == Mltl::<A>::True {
    } else if phi == Mltl::<A>::False {
        assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, f) == semantics_mltl(pi, psi) by {
            reveal_with_fuel(semantics_mltl, 2);
        }
        semantic_equiv_transitive(f, psi, p2);
    } else if psi == Mltl::<A>::False {
        assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, f) == semantics_mltl(pi, phi) by {
            reveal_with_fuel(semantics_mltl, 2);
        }
        semantic_equiv_transitive(f, phi, p1);
    } else if phi == psi {
        assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, f) == semantics_mltl(pi, phi) by {
            reveal_with_fuel(semantics_mltl, 2);
        }
        semantic_equiv_transitive(f, phi, p1);
    } else {
        or_ce_left(phi, p1, psi);
        or_ce_right(p1, psi, p2);
        semantic_equiv_transitive(f, Mltl::Or(Box::new(p1), Box::new(psi)), r);
    }
}

/// And case of `simp_mltl_aux_correct`.
proof fn simp_mltl_aux_correct_and<A>(phi: Mltl<A>, psi: Mltl<A>)
    requires
        semantic_equiv(phi, simp_mltl_aux_spec(phi).0),
        semantic_equiv(psi, simp_mltl_aux_spec(psi).0),
    ensures
        semantic_equiv(Mltl::And(Box::new(phi), Box::new(psi)), simp_mltl_aux_spec(Mltl::And(Box::new(phi), Box::new(psi))).0),
{
    let f = Mltl::And(Box::new(phi), Box::new(psi));
    let r = simp_mltl_aux_spec(f).0;
    let p1 = simp_mltl_aux_spec(phi).0;
    let p2 = simp_mltl_aux_spec(psi).0;
    if phi == Mltl::<A>::False || psi == Mltl::<A>::False {
    } else if phi == Mltl::<A>::True {
        assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, f) == semantics_mltl(pi, psi) by {
            reveal_with_fuel(semantics_mltl, 2);
        }
        semantic_equiv_transitive(f, psi, p2);
    } else if psi == Mltl::<A>::True {
        assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, f) == semantics_mltl(pi, phi) by {
            reveal_with_fuel(semantics_mltl, 2);
        }
        semantic_equiv_transitive(f, phi, p1);
    } else if phi == psi {
        assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, f) == semantics_mltl(pi, phi) by {
            reveal_with_fuel(semantics_mltl, 2);
        }
        semantic_equiv_transitive(f, phi, p1);
    } else {
        and_ce_left(phi, p1, psi);
        and_ce_right(p1, psi, p2);
        semantic_equiv_transitive(f, Mltl::And(Box::new(p1), Box::new(psi)), r);
    }
}

/// Until case of `simp_mltl_aux_correct`.
proof fn simp_mltl_aux_correct_until<A>(phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>)
    requires
        a <= b,
        semantic_equiv(phi, simp_mltl_aux_spec(phi).0),
        semantic_equiv(psi, simp_mltl_aux_spec(psi).0),
    ensures
        semantic_equiv(Mltl::Until(Box::new(phi), a, b, Box::new(psi)),
            simp_mltl_aux_spec(Mltl::Until(Box::new(phi), a, b, Box::new(psi))).0),
{
    let f = Mltl::Until(Box::new(phi), a, b, Box::new(psi));
    let r = simp_mltl_aux_spec(f).0;
    let p1 = simp_mltl_aux_spec(phi).0;
    let p2 = simp_mltl_aux_spec(psi).0;
    if psi == Mltl::<A>::False {
        until_false(a, b, phi);
    } else if phi == Mltl::<A>::True {
        let fu = Mltl::Future(a, b, Box::new(psi));
        future_as_until(a, b, psi);
        semantic_equiv_symmetric(fu, f);
        future_ce(a, b, psi, p2);
        semantic_equiv_transitive(f, fu, r);
    } else {
        until_ce_left(a, b, phi, p1, psi);
        until_ce_right(a, b, p1, psi, p2);
        semantic_equiv_transitive(f, Mltl::Until(Box::new(p1), a, b, Box::new(psi)), r);
    }
}

/// Release case of `simp_mltl_aux_correct`.
proof fn simp_mltl_aux_correct_release<A>(phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>)
    requires
        a <= b,
        semantic_equiv(phi, simp_mltl_aux_spec(phi).0),
        semantic_equiv(psi, simp_mltl_aux_spec(psi).0),
    ensures
        semantic_equiv(Mltl::Release(Box::new(phi), a, b, Box::new(psi)),
            simp_mltl_aux_spec(Mltl::Release(Box::new(phi), a, b, Box::new(psi))).0),
{
    let f = Mltl::Release(Box::new(phi), a, b, Box::new(psi));
    let r = simp_mltl_aux_spec(f).0;
    let p1 = simp_mltl_aux_spec(phi).0;
    let p2 = simp_mltl_aux_spec(psi).0;
    if psi == Mltl::<A>::True {
        release_true(a, b, phi);
    } else if phi == Mltl::<A>::False {
        let gl = Mltl::Global(a, b, Box::new(psi));
        globally_as_release(a, b, psi);
        semantic_equiv_symmetric(gl, f);
        globally_ce(a, b, psi, p2);
        semantic_equiv_transitive(f, gl, r);
    } else {
        release_ce_left(a, b, phi, p1, psi);
        release_ce_right(a, b, p1, psi, p2);
        semantic_equiv_transitive(f, Mltl::Release(Box::new(p1), a, b, Box::new(psi)), r);
    }
}

pub proof fn simp_mltl_aux_correct<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        semantic_equiv(f, simp_mltl_aux_spec(f).0),
    decreases f,
{
    match f {
        Mltl::Not(g) => {
            simp_mltl_aux_correct(*g);
            simp_mltl_aux_correct_not(*g);
        },
        Mltl::Or(phi, psi) => {
            simp_mltl_aux_correct(*phi);
            simp_mltl_aux_correct(*psi);
            simp_mltl_aux_correct_or(*phi, *psi);
        },
        Mltl::And(phi, psi) => {
            simp_mltl_aux_correct(*phi);
            simp_mltl_aux_correct(*psi);
            simp_mltl_aux_correct_and(*phi, *psi);
        },
        Mltl::Global(a, b, g) => {
            simp_mltl_aux_correct(*g);
            if *g == Mltl::<A>::True {
                globally_true::<A>(a, b);
            } else {
                globally_ce(a, b, *g, simp_mltl_aux_spec(*g).0);
            }
        },
        Mltl::Future(a, b, g) => {
            simp_mltl_aux_correct(*g);
            if *g == Mltl::<A>::False {
                future_false::<A>(a, b);
            } else {
                future_ce(a, b, *g, simp_mltl_aux_spec(*g).0);
            }
        },
        Mltl::Until(phi, a, b, psi) => {
            simp_mltl_aux_correct(*phi);
            simp_mltl_aux_correct(*psi);
            simp_mltl_aux_correct_until(*phi, a, b, *psi);
        },
        Mltl::Release(phi, a, b, psi) => {
            simp_mltl_aux_correct(*phi);
            simp_mltl_aux_correct(*psi);
            simp_mltl_aux_correct_release(*phi, a, b, *psi);
        },
        _ => {},
    }
}

pub proof fn simp_mltl_correct<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        semantic_equiv(f, simp_mltl_spec(f)),
    decreases size_mltl(f),
{
    let r = simp_mltl_aux_spec(f);
    simp_mltl_aux_correct(f);
    if r.1 {
        simp_mltl_aux_size(f);
        simp_mltl_aux_welldef(f);
        simp_mltl_correct(r.0);
        semantic_equiv_transitive(f, r.0, simp_mltl_spec(r.0));
    }
}

pub proof fn simp_mltl_welldef<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        intervals_welldef(simp_mltl_spec(f)),
    decreases size_mltl(f),
{
    let r = simp_mltl_aux_spec(f);
    simp_mltl_aux_welldef(f);
    if r.1 {
        simp_mltl_aux_size(f);
        simp_mltl_welldef(r.0);
    }
}

// ---------------------------------------------------------------------------
// simp_duals
// ---------------------------------------------------------------------------

/// `simp_duals φ`: undo the `Not … Not` shapes that progression introduces
/// for Global and Release (and the De Morgan shapes), at the top level and
/// recursively under each undone shape. Clauses in Isabelle's order.
pub open spec fn simp_duals_spec<A>(f: Mltl<A>) -> Mltl<A>
    decreases f,
{
    match f {
        Mltl::Not(g) => match *g {
            Mltl::Global(a, b, h) => match *h {
                Mltl::Not(phi) => Mltl::Future(a, b, Box::new(simp_duals_spec(*phi))),
                _ => f,
            },
            Mltl::Future(a, b, h) => match *h {
                Mltl::Not(phi) => Mltl::Global(a, b, Box::new(simp_duals_spec(*phi))),
                _ => f,
            },
            Mltl::And(x, y) => match (*x, *y) {
                (Mltl::Not(phi), Mltl::Not(psi)) =>
                    Mltl::Or(Box::new(simp_duals_spec(*phi)), Box::new(simp_duals_spec(*psi))),
                _ => f,
            },
            Mltl::Or(x, y) => match (*x, *y) {
                (Mltl::Not(phi), Mltl::Not(psi)) =>
                    Mltl::And(Box::new(simp_duals_spec(*phi)), Box::new(simp_duals_spec(*psi))),
                _ => f,
            },
            Mltl::Until(x, a, b, y) => match (*x, *y) {
                (Mltl::Not(phi), Mltl::Not(psi)) =>
                    Mltl::Release(Box::new(simp_duals_spec(*phi)), a, b, Box::new(simp_duals_spec(*psi))),
                _ => f,
            },
            Mltl::Release(x, a, b, y) => match (*x, *y) {
                (Mltl::Not(phi), Mltl::Not(psi)) =>
                    Mltl::Until(Box::new(simp_duals_spec(*phi)), a, b, Box::new(simp_duals_spec(*psi))),
                _ => f,
            },
            _ => f,
        },
        _ => f,
    }
}

/// `simp_duals_correct`
pub proof fn simp_duals_correct<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        semantic_equiv(simp_duals_spec(f), f),
    decreases f,
{
    reveal_with_fuel(intervals_welldef, 4);
    match f {
        Mltl::Not(g) => match *g {
            Mltl::Global(a, b, h) => match *h {
                Mltl::Not(phi) => {
                    simp_duals_correct(*phi);
                    future_ce(a, b, simp_duals_spec(*phi), *phi);
                    future_globally_dual(a, b, *phi);
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::Future(a, b, phi), f);
                },
                _ => {},
            },
            Mltl::Future(a, b, h) => match *h {
                Mltl::Not(phi) => {
                    simp_duals_correct(*phi);
                    globally_ce(a, b, simp_duals_spec(*phi), *phi);
                    globally_future_dual(a, b, *phi);
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::Global(a, b, phi), f);
                },
                _ => {},
            },
            Mltl::And(x, y) => match (*x, *y) {
                (Mltl::Not(phi), Mltl::Not(psi)) => {
                    let (s1, s2) = (simp_duals_spec(*phi), simp_duals_spec(*psi));
                    simp_duals_correct(*phi);
                    simp_duals_correct(*psi);
                    or_ce_left(s1, *phi, s2);
                    or_ce_right(*phi, s2, *psi);
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::Or(phi, Box::new(s2)), Mltl::Or(phi, psi));
                    assert(semantic_equiv(Mltl::Or(phi, psi), f)) by {
                        reveal_with_fuel(semantics_mltl, 4);
                    }
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::Or(phi, psi), f);
                },
                _ => {},
            },
            Mltl::Or(x, y) => match (*x, *y) {
                (Mltl::Not(phi), Mltl::Not(psi)) => {
                    let (s1, s2) = (simp_duals_spec(*phi), simp_duals_spec(*psi));
                    simp_duals_correct(*phi);
                    simp_duals_correct(*psi);
                    and_ce_left(s1, *phi, s2);
                    and_ce_right(*phi, s2, *psi);
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::And(phi, Box::new(s2)), Mltl::And(phi, psi));
                    assert(semantic_equiv(Mltl::And(phi, psi), f)) by {
                        reveal_with_fuel(semantics_mltl, 4);
                    }
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::And(phi, psi), f);
                },
                _ => {},
            },
            Mltl::Until(x, a, b, y) => match (*x, *y) {
                (Mltl::Not(phi), Mltl::Not(psi)) => {
                    let (s1, s2) = (simp_duals_spec(*phi), simp_duals_spec(*psi));
                    simp_duals_correct(*phi);
                    simp_duals_correct(*psi);
                    release_ce_left(a, b, s1, *phi, s2);
                    release_ce_right(a, b, *phi, s2, *psi);
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::Release(phi, a, b, Box::new(s2)),
                        Mltl::Release(phi, a, b, psi));
                    release_until_dual(a, b, *phi, *psi);
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::Release(phi, a, b, psi), f);
                },
                _ => {},
            },
            Mltl::Release(x, a, b, y) => match (*x, *y) {
                (Mltl::Not(phi), Mltl::Not(psi)) => {
                    let (s1, s2) = (simp_duals_spec(*phi), simp_duals_spec(*psi));
                    simp_duals_correct(*phi);
                    simp_duals_correct(*psi);
                    until_ce_left(a, b, s1, *phi, s2);
                    until_ce_right(a, b, *phi, s2, *psi);
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::Until(phi, a, b, Box::new(s2)),
                        Mltl::Until(phi, a, b, psi));
                    until_release_dual(a, b, *phi, *psi);
                    semantic_equiv_transitive(simp_duals_spec(f), Mltl::Until(phi, a, b, psi), f);
                },
                _ => {},
            },
            _ => {},
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Executable simplifiers (spec/exec pairs: result == the spec)
// ---------------------------------------------------------------------------

/// `*f == True_mltl`
pub fn is_true_mltl(f: &Mltl<usize>) -> (r: bool)
    ensures
        r == (*f == Mltl::<usize>::True),
{
    match f {
        Mltl::True => true,
        _ => false,
    }
}

/// `*f == False_mltl`
pub fn is_false_mltl(f: &Mltl<usize>) -> (r: bool)
    ensures
        r == (*f == Mltl::<usize>::False),
{
    match f {
        Mltl::False => true,
        _ => false,
    }
}

/// Executable `simp_mltl_aux`. Takes ownership: unchanged subformulas are
/// moved and boxes reused, so a pass allocates only for new nodes.
pub fn simp_mltl_aux(f: Mltl<usize>) -> (r: (Mltl<usize>, bool))
    ensures
        r == simp_mltl_aux_spec(f),
    decreases f,
{
    match f {
        Mltl::Not(mut g) => match *g {
            Mltl::True => (Mltl::False, true),
            Mltl::False => (Mltl::True, true),
            Mltl::Not(phi) => (*phi, true),
            other => {
                let (g2, p) = simp_mltl_aux(other);
                *g = g2;
                (Mltl::Not(g), p)
            },
        },
        Mltl::Or(mut phi, mut psi) =>
            if is_true_mltl(&*phi) || is_true_mltl(&*psi) {
                (Mltl::True, true)
            } else if is_false_mltl(&*phi) {
                (simp_mltl_aux(*psi).0, true)
            } else if is_false_mltl(&*psi) {
                (simp_mltl_aux(*phi).0, true)
            } else if eq_mltl(&*phi, &*psi) {
                (simp_mltl_aux(*phi).0, true)
            } else {
                let (p1, b1) = simp_mltl_aux(*phi);
                let (p2, b2) = simp_mltl_aux(*psi);
                *phi = p1;
                *psi = p2;
                (Mltl::Or(phi, psi), b1 || b2)
            },
        Mltl::And(mut phi, mut psi) =>
            if is_false_mltl(&*phi) || is_false_mltl(&*psi) {
                (Mltl::False, true)
            } else if is_true_mltl(&*phi) {
                (simp_mltl_aux(*psi).0, true)
            } else if is_true_mltl(&*psi) {
                (simp_mltl_aux(*phi).0, true)
            } else if eq_mltl(&*phi, &*psi) {
                (simp_mltl_aux(*phi).0, true)
            } else {
                let (p1, b1) = simp_mltl_aux(*phi);
                let (p2, b2) = simp_mltl_aux(*psi);
                *phi = p1;
                *psi = p2;
                (Mltl::And(phi, psi), b1 || b2)
            },
        Mltl::Global(a, b, mut g) =>
            if is_true_mltl(&*g) {
                (Mltl::True, true)
            } else {
                let (g2, p) = simp_mltl_aux(*g);
                *g = g2;
                (Mltl::Global(a, b, g), p)
            },
        Mltl::Future(a, b, mut g) =>
            if is_false_mltl(&*g) {
                (Mltl::False, true)
            } else {
                let (g2, p) = simp_mltl_aux(*g);
                *g = g2;
                (Mltl::Future(a, b, g), p)
            },
        Mltl::Until(mut phi, a, b, mut psi) =>
            if is_false_mltl(&*psi) {
                (Mltl::False, true)
            } else if is_true_mltl(&*phi) {
                *psi = simp_mltl_aux(*psi).0;
                (Mltl::Future(a, b, psi), true)
            } else {
                let (p1, b1) = simp_mltl_aux(*phi);
                let (p2, b2) = simp_mltl_aux(*psi);
                *phi = p1;
                *psi = p2;
                (Mltl::Until(phi, a, b, psi), b1 || b2)
            },
        Mltl::Release(mut phi, a, b, mut psi) =>
            if is_true_mltl(&*psi) {
                (Mltl::True, true)
            } else if is_false_mltl(&*phi) {
                *psi = simp_mltl_aux(*psi).0;
                (Mltl::Global(a, b, psi), true)
            } else {
                let (p1, b1) = simp_mltl_aux(*phi);
                let (p2, b2) = simp_mltl_aux(*psi);
                *phi = p1;
                *psi = p2;
                (Mltl::Release(phi, a, b, psi), b1 || b2)
            },
        _ => (f, false),
    }
}

/// Executable `simp_mltl` (takes ownership): a loop instead of the recursion.
pub fn simp_mltl(f: Mltl<usize>) -> (r: Mltl<usize>)
    ensures
        r == simp_mltl_spec(f),
{
    let ghost f0 = f;
    let (mut cur, mut changed) = simp_mltl_aux(f);
    while changed
        invariant
            simp_mltl_spec(f0) == if changed { simp_mltl_spec(cur) } else { cur },
        decreases size_mltl(cur) + if changed { 1nat } else { 0nat },
    {
        proof {
            simp_mltl_aux_size(cur);
        }
        let (n, c) = simp_mltl_aux(cur);
        cur = n;
        changed = c;
    }
    cur
}

/// Helper (not in Isabelle): `f` matches one of the rewriting clauses of
/// `simp_duals` (otherwise `simp_duals` returns `f` unchanged).
pub open spec fn is_dual_shape<A>(f: Mltl<A>) -> bool {
    match f {
        Mltl::Not(g) => match *g {
            Mltl::Global(_, _, h) | Mltl::Future(_, _, h) => *h is Not,
            Mltl::And(x, y) | Mltl::Or(x, y) | Mltl::Until(x, _, _, y) | Mltl::Release(x, _, _, y) =>
                *x is Not && *y is Not,
            _ => false,
        },
        _ => false,
    }
}

fn is_not_mltl(f: &Mltl<usize>) -> (r: bool)
    ensures
        r == (*f is Not),
{
    match f {
        Mltl::Not(_) => true,
        _ => false,
    }
}

/// Executable `is_dual_shape`.
pub fn dual_shape(f: &Mltl<usize>) -> (r: bool)
    ensures
        r == is_dual_shape(*f),
{
    match f {
        Mltl::Not(g) => match &**g {
            Mltl::Global(_, _, h) => is_not_mltl(&**h),
            Mltl::Future(_, _, h) => is_not_mltl(&**h),
            Mltl::And(x, y) => is_not_mltl(&**x) && is_not_mltl(&**y),
            Mltl::Or(x, y) => is_not_mltl(&**x) && is_not_mltl(&**y),
            Mltl::Until(x, _, _, y) => is_not_mltl(&**x) && is_not_mltl(&**y),
            Mltl::Release(x, _, _, y) => is_not_mltl(&**x) && is_not_mltl(&**y),
            _ => false,
        },
        _ => false,
    }
}

/// Executable `simp_duals` (takes ownership): an input without a dual shape
/// is returned as is (no copy); rewritten nodes reuse their boxes.
pub fn simp_duals(f: Mltl<usize>) -> (r: Mltl<usize>)
    ensures
        r == simp_duals_spec(f),
    decreases f,
{
    if !dual_shape(&f) {
        return f;
    }
    match f {
        Mltl::Not(g) => match *g {
            Mltl::Global(a, b, h) => match *h {
                Mltl::Not(mut phi) => {
                    *phi = simp_duals(*phi);
                    Mltl::Future(a, b, phi)
                },
                other => other,
            },
            Mltl::Future(a, b, h) => match *h {
                Mltl::Not(mut phi) => {
                    *phi = simp_duals(*phi);
                    Mltl::Global(a, b, phi)
                },
                other => other,
            },
            Mltl::And(x, y) => match (*x, *y) {
                (Mltl::Not(mut phi), Mltl::Not(mut psi)) => {
                    *phi = simp_duals(*phi);
                    *psi = simp_duals(*psi);
                    Mltl::Or(phi, psi)
                },
                (other, _) => other,
            },
            Mltl::Or(x, y) => match (*x, *y) {
                (Mltl::Not(mut phi), Mltl::Not(mut psi)) => {
                    *phi = simp_duals(*phi);
                    *psi = simp_duals(*psi);
                    Mltl::And(phi, psi)
                },
                (other, _) => other,
            },
            Mltl::Until(x, a, b, y) => match (*x, *y) {
                (Mltl::Not(mut phi), Mltl::Not(mut psi)) => {
                    *phi = simp_duals(*phi);
                    *psi = simp_duals(*psi);
                    Mltl::Release(phi, a, b, psi)
                },
                (other, _) => other,
            },
            Mltl::Release(x, a, b, y) => match (*x, *y) {
                (Mltl::Not(mut phi), Mltl::Not(mut psi)) => {
                    *phi = simp_duals(*phi);
                    *psi = simp_duals(*psi);
                    Mltl::Until(phi, a, b, psi)
                },
                (other, _) => other,
            },
            other => other,
        },
        other => other,
    }
}

} // verus!
