//! Properties of MLTL.
//!
//! Mirrors AFP `Mission_Time_LTL`, theory `MLTL_Properties.thy`.
//! Correspondence table: agent-docs/correspondence/mission-time-ltl.md.
use vstd::prelude::*;
use crate::mltl::*;

verus! {

broadcast use vstd::set::group_set_lemmas;

// ---------------------------------------------------------------------------
// Useful functions
// ---------------------------------------------------------------------------

/// `intervals_welldef φ`: every interval `[a,b]` in `φ` has `a ≤ b`.
pub open spec fn intervals_welldef<A>(f: Mltl<A>) -> bool
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => true,
        Mltl::Not(phi) => intervals_welldef(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => intervals_welldef(*phi) && intervals_welldef(*psi),
        Mltl::Future(a, b, phi) | Mltl::Global(a, b, phi) => a <= b && intervals_welldef(*phi),
        Mltl::Until(phi, a, b, psi) | Mltl::Release(phi, a, b, psi) =>
            a <= b && intervals_welldef(*phi) && intervals_welldef(*psi),
    }
}

// ---------------------------------------------------------------------------
// Semantic equivalence
// ---------------------------------------------------------------------------

/// `φ ≡_m ψ`: same truth value on every trace (finite-state traces, D16).
pub open spec fn semantic_equiv<A>(phi: Mltl<A>, psi: Mltl<A>) -> bool {
    forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, phi) == semantics_mltl(pi, psi)
}

/// `depth_mltl φ`: nesting depth of operators.
pub open spec fn depth_mltl<A>(f: Mltl<A>) -> nat
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 0,
        Mltl::Not(phi) | Mltl::Global(_, _, phi) | Mltl::Future(_, _, phi) => 1 + depth_mltl(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
        | Mltl::Release(phi, _, _, psi) => 1 + max_nat(depth_mltl(*phi), depth_mltl(*psi)),
    }
}

/// Isabelle `max` on `nat`.
pub open spec fn max_nat(x: nat, y: nat) -> nat {
    if x >= y { x } else { y }
}

/// `subformulas φ`: proper subformulas of `φ` (not including `φ` itself).
pub open spec fn subformulas<A>(f: Mltl<A>) -> Set<Mltl<A>>
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => Set::empty(),
        Mltl::Not(phi) | Mltl::Global(_, _, phi) | Mltl::Future(_, _, phi) =>
            Set::empty().insert(*phi).union(subformulas(*phi)),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
        | Mltl::Release(phi, _, _, psi) =>
            Set::empty().insert(*phi).insert(*psi).union(subformulas(*phi)).union(subformulas(*psi)),
    }
}

// ---------------------------------------------------------------------------
// Basic properties
// ---------------------------------------------------------------------------

pub proof fn future_or_distribute<A>(a: usize, b: usize, phi1: Mltl<A>, phi2: Mltl<A>)
    ensures
        semantic_equiv(
            Mltl::Future(a, b, Box::new(Mltl::Or(Box::new(phi1), Box::new(phi2)))),
            Mltl::Or(Box::new(Mltl::Future(a, b, Box::new(phi1))), Box::new(Mltl::Future(a, b, Box::new(phi2)))),
        ),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn global_and_distribute<A>(a: usize, b: usize, phi1: Mltl<A>, phi2: Mltl<A>)
    ensures
        semantic_equiv(
            Mltl::Global(a, b, Box::new(Mltl::And(Box::new(phi1), Box::new(phi2)))),
            Mltl::And(Box::new(Mltl::Global(a, b, Box::new(phi1))), Box::new(Mltl::Global(a, b, Box::new(phi2)))),
        ),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn not_not_equiv<A>(phi: Mltl<A>)
    ensures
        semantic_equiv(phi, Mltl::Not(Box::new(Mltl::Not(Box::new(phi))))),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn demorgan_and_or<A>(phi: Mltl<A>, psi: Mltl<A>)
    ensures
        semantic_equiv(
            Mltl::Not(Box::new(Mltl::And(Box::new(phi), Box::new(psi)))),
            Mltl::Or(Box::new(Mltl::Not(Box::new(phi))), Box::new(Mltl::Not(Box::new(psi)))),
        ),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn demorgan_or_and<A>(phi: Mltl<A>, psi: Mltl<A>)
    ensures
        semantic_equiv(
            Mltl::Not(Box::new(Mltl::Or(Box::new(phi), Box::new(psi)))),
            Mltl::And(Box::new(Mltl::Not(Box::new(phi))), Box::new(Mltl::Not(Box::new(psi)))),
        ),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn future_as_until<A>(a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(Mltl::Future(a, b, Box::new(phi)), Mltl::Until(Box::new(Mltl::True), a, b, Box::new(phi))),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn globally_as_release<A>(a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(Mltl::Global(a, b, Box::new(phi)), Mltl::Release(Box::new(Mltl::False), a, b, Box::new(phi))),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn until_or_distribute<A>(a: usize, b: usize, phi: Mltl<A>, alpha: Mltl<A>, beta: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(
            Mltl::Until(Box::new(phi), a, b, Box::new(Mltl::Or(Box::new(alpha), Box::new(beta)))),
            Mltl::Or(
                Box::new(Mltl::Until(Box::new(phi), a, b, Box::new(alpha))),
                Box::new(Mltl::Until(Box::new(phi), a, b, Box::new(beta))),
            ),
        ),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn until_and_distribute<A>(a: usize, b: usize, alpha: Mltl<A>, beta: Mltl<A>, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(
            Mltl::Until(Box::new(Mltl::And(Box::new(alpha), Box::new(beta))), a, b, Box::new(phi)),
            Mltl::And(
                Box::new(Mltl::Until(Box::new(alpha), a, b, Box::new(phi))),
                Box::new(Mltl::Until(Box::new(beta), a, b, Box::new(phi))),
            ),
        ),
{
    reveal_with_fuel(semantics_mltl, 2);
    let lhs = Mltl::Until(Box::new(Mltl::And(Box::new(alpha), Box::new(beta))), a, b, Box::new(phi));
    let ua = Mltl::Until(Box::new(alpha), a, b, Box::new(phi));
    let ub = Mltl::Until(Box::new(beta), a, b, Box::new(phi));
    assert forall|pi: Seq<Set<A>>|
        #[trigger] semantics_mltl(pi, lhs) == (semantics_mltl(pi, ua) && semantics_mltl(pi, ub)) by {
        if semantics_mltl(pi, ua) && semantics_mltl(pi, ub) {
            // Take the earlier of the two witnesses.
            let i1 = choose|i: nat| (a <= i && i <= b) && (semantics_mltl(drop(pi, i), phi)
                && forall|j: nat| (j >= a && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), alpha));
            let i2 = choose|i: nat| (a <= i && i <= b) && (semantics_mltl(drop(pi, i), phi)
                && forall|j: nat| (j >= a && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), beta));
            let i = if i1 <= i2 { i1 } else { i2 };
            assert(semantics_mltl(drop(pi, i), phi));
            assert(forall|j: nat| (j >= a && j < i) ==>
                semantics_mltl(#[trigger] drop(pi, j), Mltl::And(Box::new(alpha), Box::new(beta))));
        }
    }
}

pub proof fn release_or_distribute<A>(a: usize, b: usize, alpha: Mltl<A>, beta: Mltl<A>, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(
            Mltl::Release(Box::new(Mltl::Or(Box::new(alpha), Box::new(beta))), a, b, Box::new(phi)),
            Mltl::Or(
                Box::new(Mltl::Release(Box::new(alpha), a, b, Box::new(phi))),
                Box::new(Mltl::Release(Box::new(beta), a, b, Box::new(phi))),
            ),
        ),
{
    reveal_with_fuel(semantics_mltl, 2);
}

/// `¬ (G[1,1] φ ≡_m F[1,1] φ)` — witnessed by the empty trace.
pub proof fn different_next_operators<A>(phi: Mltl<A>)
    ensures
        !semantic_equiv(Mltl::Global(1, 1, Box::new(phi)), Mltl::Future(1, 1, Box::new(phi))),
{
    let e = Seq::<Set<A>>::empty();
    assert(semantics_mltl(e, Mltl::Global(1, 1, Box::new(phi))));
    assert(!semantics_mltl(e, Mltl::Future(1, 1, Box::new(phi))));
}

// ---------------------------------------------------------------------------
// Duality properties
// ---------------------------------------------------------------------------

pub proof fn globally_future_dual<A>(a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(
            Mltl::Global(a, b, Box::new(phi)),
            Mltl::Not(Box::new(Mltl::Future(a, b, Box::new(Mltl::Not(Box::new(phi)))))),
        ),
{
    reveal_with_fuel(semantics_mltl, 3);
}

pub proof fn future_globally_dual<A>(a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(
            Mltl::Future(a, b, Box::new(phi)),
            Mltl::Not(Box::new(Mltl::Global(a, b, Box::new(Mltl::Not(Box::new(phi)))))),
        ),
{
    reveal_with_fuel(semantics_mltl, 3);
}

/// Helper (not in Isabelle, which uses `linorder` reasoning): if `p` fails
/// somewhere in `[a, i0]`, it fails at a first index `i` in that range.
pub proof fn lemma_first_failure(p: spec_fn(nat) -> bool, a: nat, i0: nat) -> (i: nat)
    requires
        a <= i0,
        !p(i0),
    ensures
        a <= i <= i0,
        !p(i),
        forall|k: nat| a <= k < i ==> #[trigger] p(k),
    decreases i0,
{
    if forall|k: nat| a <= k < i0 ==> #[trigger] p(k) {
        i0
    } else {
        let k = choose|k: nat| a <= k < i0 && !#[trigger] p(k);
        lemma_first_failure(p, a, k)
    }
}

/// `π ⊨ φ R[a,b] ψ  ⟹  π ⊨ Not ((Not φ) U[a,b] (Not ψ))`
pub proof fn release_until_dual1<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))),
    ensures
        semantics_mltl(
            pi,
            Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(Box::new(phi))), a, b, Box::new(Mltl::Not(Box::new(psi)))))),
        ),
{
    reveal_with_fuel(semantics_mltl, 3);
}

/// Unfolding of `π ⊨ Not ((Not φ) U[a,b] (Not ψ))` (helper; Isabelle's
/// `not_until_not_unfold` inside `release_until_dual2`).
proof fn not_until_not_unfold<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a <= b,
        pi.len() > a,
        semantics_mltl(
            pi,
            Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(Box::new(phi))), a, b, Box::new(Mltl::Not(Box::new(psi)))))),
        ),
    ensures
        forall|i: nat| (a <= i && i <= b) && !semantics_mltl(#[trigger] drop(pi, i), psi) ==>
            exists|j: nat| (j >= a && j < i) && semantics_mltl(#[trigger] drop(pi, j), phi),
{
    reveal_with_fuel(semantics_mltl, 3);
}

/// `a ≤ b ⟹ π ⊨ Not ((Not φ) U[a,b] (Not ψ))  ⟹  π ⊨ φ R[a,b] ψ`
#[verifier::spinoff_prover]
pub proof fn release_until_dual2<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a <= b,
        semantics_mltl(
            pi,
            Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(Box::new(phi))), a, b, Box::new(Mltl::Not(Box::new(psi)))))),
        ),
    ensures
        semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))),
{
    if pi.len() > a && !(forall|i: nat| (a <= i && i <= b) ==> semantics_mltl(#[trigger] drop(pi, i), psi)) {
        not_until_not_unfold(pi, a, b, phi, psi);
        let i0 = choose|i: nat| (a <= i && i <= b) && !semantics_mltl(#[trigger] drop(pi, i), psi);
        let p = |k: nat| semantics_mltl(drop(pi, k), psi);
        let i = lemma_first_failure(p, a as nat, i0);
        assert forall|k: nat| a <= k < i implies semantics_mltl(#[trigger] drop(pi, k), psi) by {
            assert(p(k));
        }
        // ¬U at the first failure i: some j in [a, i) satisfies φ.
        assert(!semantics_mltl(drop(pi, i), psi));
        let j = choose|j: nat| (j >= a && j < i) && semantics_mltl(#[trigger] drop(pi, j), phi);
        assert(j <= nat_sub(b as nat, 1));
        assert(forall|k: nat| (a <= k && k <= j) ==> semantics_mltl(#[trigger] drop(pi, k), psi));
    }
}

/// `a ≤ b ⟹ φ R[a,b] ψ ≡_m Not ((Not φ) U[a,b] (Not ψ))`
pub proof fn release_until_dual<A>(a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(
            Mltl::Release(Box::new(phi), a, b, Box::new(psi)),
            Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(Box::new(phi))), a, b, Box::new(Mltl::Not(Box::new(psi)))))),
        ),
{
    assert forall|pi: Seq<Set<A>>|
        #[trigger] semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi)))
        == semantics_mltl(
            pi,
            Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(Box::new(phi))), a, b, Box::new(Mltl::Not(Box::new(psi)))))),
        ) by {
        if semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))) {
            release_until_dual1(pi, a, b, phi, psi);
        } else if semantics_mltl(
            pi,
            Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(Box::new(phi))), a, b, Box::new(Mltl::Not(Box::new(psi)))))),
        ) {
            release_until_dual2(pi, a, b, phi, psi);
        }
    }
}

/// `a ≤ b ⟹ φ U[a,b] ψ ≡_m Not ((Not φ) R[a,b] (Not ψ))`
pub proof fn until_release_dual<A>(a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(
            Mltl::Until(Box::new(phi), a, b, Box::new(psi)),
            Mltl::Not(Box::new(Mltl::Release(Box::new(Mltl::Not(Box::new(phi))), a, b, Box::new(Mltl::Not(Box::new(psi)))))),
        ),
{
    let nphi = Mltl::Not(Box::new(phi));
    let npsi = Mltl::Not(Box::new(psi));
    release_until_dual(a, b, nphi, npsi);
    reveal_with_fuel(semantics_mltl, 3);
    // Not Not cancels inside U pointwise; then use the dual on (Not φ, Not ψ).
    assert forall|pi: Seq<Set<A>>|
        #[trigger] semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi)))
        == semantics_mltl(pi, Mltl::Until(
            Box::new(Mltl::Not(Box::new(nphi))), a, b, Box::new(Mltl::Not(Box::new(npsi))))) by {}
    assert forall|pi: Seq<Set<A>>|
        #[trigger] semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi)))
        == semantics_mltl(pi, Mltl::Not(Box::new(Mltl::Release(Box::new(nphi), a, b, Box::new(npsi))))) by {
        assert(semantics_mltl(pi, Mltl::Release(Box::new(nphi), a, b, Box::new(npsi)))
            == semantics_mltl(pi, Mltl::Not(Box::new(Mltl::Until(
                Box::new(Mltl::Not(Box::new(nphi))), a, b, Box::new(Mltl::Not(Box::new(npsi))))))));
    }
}

// ---------------------------------------------------------------------------
// Additional basic properties
// ---------------------------------------------------------------------------

/// `a ≤ b ⟹ φ R[a,b] (α And β) ≡_m (φ R[a,b] α) And (φ R[a,b] β)`
pub proof fn release_and_distribute<A>(a: usize, b: usize, phi: Mltl<A>, alpha: Mltl<A>, beta: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(
            Mltl::Release(Box::new(phi), a, b, Box::new(Mltl::And(Box::new(alpha), Box::new(beta)))),
            Mltl::And(
                Box::new(Mltl::Release(Box::new(phi), a, b, Box::new(alpha))),
                Box::new(Mltl::Release(Box::new(phi), a, b, Box::new(beta))),
            ),
        ),
{
    let ab = Mltl::And(Box::new(alpha), Box::new(beta));
    release_until_dual(a, b, phi, ab);
    release_until_dual(a, b, phi, alpha);
    release_until_dual(a, b, phi, beta);
    reveal_with_fuel(semantics_mltl, 3);
    let nphi = Mltl::Not(Box::new(phi));
    let lhs = Mltl::Release(Box::new(phi), a, b, Box::new(ab));
    let ra = Mltl::Release(Box::new(phi), a, b, Box::new(alpha));
    let rb = Mltl::Release(Box::new(phi), a, b, Box::new(beta));
    let u_ab = Mltl::Until(Box::new(nphi), a, b, Box::new(Mltl::Not(Box::new(ab))));
    let u_a = Mltl::Until(Box::new(nphi), a, b, Box::new(Mltl::Not(Box::new(alpha))));
    let u_b = Mltl::Until(Box::new(nphi), a, b, Box::new(Mltl::Not(Box::new(beta))));
    assert forall|pi: Seq<Set<A>>|
        #[trigger] semantics_mltl(pi, lhs) == (semantics_mltl(pi, ra) && semantics_mltl(pi, rb)) by {
        // ¬(α ∧ β) ≡ ¬α ∨ ¬β pointwise, then until_or_distribute.
        until_or_distribute(a, b, nphi, Mltl::Not(Box::new(alpha)), Mltl::Not(Box::new(beta)));
        let u_or = Mltl::Until(Box::new(nphi), a, b, Box::new(Mltl::Or(
            Box::new(Mltl::Not(Box::new(alpha))), Box::new(Mltl::Not(Box::new(beta))))));
        assert(semantics_mltl(pi, u_ab) == semantics_mltl(pi, u_or));
        assert(semantics_mltl(pi, u_or) == (semantics_mltl(pi, u_a) || semantics_mltl(pi, u_b)));
        assert(semantics_mltl(pi, lhs) == !semantics_mltl(pi, u_ab));
        assert(semantics_mltl(pi, ra) == !semantics_mltl(pi, u_a));
        assert(semantics_mltl(pi, rb) == !semantics_mltl(pi, u_b));
    }
}

// ---------------------------------------------------------------------------
// NNF transformation and properties
// ---------------------------------------------------------------------------

/// `convert_nnf φ`: push negations down to atoms using the dualities.
///
/// Isabelle proves termination of this `fun` automatically (size measure);
/// here the measure is `depth_mltl`, checked by `convert_nnf_decreases`.
pub open spec fn convert_nnf_spec<A>(f: Mltl<A>) -> Mltl<A>
    decreases depth_mltl(f),
    via convert_nnf_spec_decreases::<A>
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(p) => Mltl::Prop(p),
        Mltl::And(phi, psi) => Mltl::And(Box::new(convert_nnf_spec(*phi)), Box::new(convert_nnf_spec(*psi))),
        Mltl::Or(phi, psi) => Mltl::Or(Box::new(convert_nnf_spec(*phi)), Box::new(convert_nnf_spec(*psi))),
        Mltl::Future(a, b, phi) => Mltl::Future(a, b, Box::new(convert_nnf_spec(*phi))),
        Mltl::Global(a, b, phi) => Mltl::Global(a, b, Box::new(convert_nnf_spec(*phi))),
        Mltl::Until(phi, a, b, psi) =>
            Mltl::Until(Box::new(convert_nnf_spec(*phi)), a, b, Box::new(convert_nnf_spec(*psi))),
        Mltl::Release(phi, a, b, psi) =>
            Mltl::Release(Box::new(convert_nnf_spec(*phi)), a, b, Box::new(convert_nnf_spec(*psi))),
        // Rewriting with logical duals
        Mltl::Not(g) => match *g {
            Mltl::True => Mltl::False,
            Mltl::False => Mltl::True,
            Mltl::Prop(p) => Mltl::Not(Box::new(Mltl::Prop(p))),
            Mltl::Not(phi) => convert_nnf_spec(*phi),
            Mltl::And(phi, psi) => Mltl::Or(
                Box::new(convert_nnf_spec(Mltl::Not(phi))),
                Box::new(convert_nnf_spec(Mltl::Not(psi))),
            ),
            Mltl::Or(phi, psi) => Mltl::And(
                Box::new(convert_nnf_spec(Mltl::Not(phi))),
                Box::new(convert_nnf_spec(Mltl::Not(psi))),
            ),
            Mltl::Future(a, b, phi) => Mltl::Global(a, b, Box::new(convert_nnf_spec(Mltl::Not(phi)))),
            Mltl::Global(a, b, phi) => Mltl::Future(a, b, Box::new(convert_nnf_spec(Mltl::Not(phi)))),
            Mltl::Until(phi, a, b, psi) => Mltl::Release(
                Box::new(convert_nnf_spec(Mltl::Not(phi))), a, b,
                Box::new(convert_nnf_spec(Mltl::Not(psi))),
            ),
            Mltl::Release(phi, a, b, psi) => Mltl::Until(
                Box::new(convert_nnf_spec(Mltl::Not(phi))), a, b,
                Box::new(convert_nnf_spec(Mltl::Not(psi))),
            ),
        },
    }
}

#[via_fn]
proof fn convert_nnf_spec_decreases<A>(f: Mltl<A>) {
    reveal_with_fuel(depth_mltl, 2);
    match f {
        Mltl::Not(g) => match *g {
            Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
            | Mltl::Release(phi, _, _, psi) => {
                assert(depth_mltl(Mltl::Not(phi)) == 1 + depth_mltl(*phi));
                assert(depth_mltl(Mltl::Not(psi)) == 1 + depth_mltl(*psi));
            },
            Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
                assert(depth_mltl(Mltl::Not(phi)) == 1 + depth_mltl(*phi));
            },
            _ => {},
        },
        _ => {},
    }
}

/// `intervals_welldef φ ⟹ (π ⊨ convert_nnf φ) = (π ⊨ φ)`
///
/// Isabelle inducts on `depth_mltl φ` (`less_induct`); same here via
/// `decreases`. Temporal cases apply the hypothesis on every suffix
/// `drop(pi, i)`. Each case is a separate `assert ... by` query to keep the
/// solver context small.
#[verifier::spinoff_prover]
pub proof fn convert_nnf_preserves_semantics<A>(pi: Seq<Set<A>>, f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        semantics_mltl(pi, convert_nnf_spec(f)) == semantics_mltl(pi, f),
    decreases depth_mltl(f),
{
    reveal_with_fuel(depth_mltl, 2);
    reveal_with_fuel(intervals_welldef, 2);
    let goal = semantics_mltl(pi, convert_nnf_spec(f)) == semantics_mltl(pi, f);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            convert_nnf_preserves_semantics(pi, *phi);
            convert_nnf_preserves_semantics(pi, *psi);
        },
        Mltl::Future(a, b, phi) | Mltl::Global(a, b, phi) => {
            assert forall|i: nat| semantics_mltl(#[trigger] drop(pi, i), convert_nnf_spec(*phi))
                == semantics_mltl(drop(pi, i), *phi) by {
                convert_nnf_preserves_semantics(drop(pi, i), *phi);
            }
        },
        Mltl::Until(phi, a, b, psi) | Mltl::Release(phi, a, b, psi) => {
            assert forall|i: nat| semantics_mltl(#[trigger] drop(pi, i), convert_nnf_spec(*phi))
                == semantics_mltl(drop(pi, i), *phi)
                && semantics_mltl(drop(pi, i), convert_nnf_spec(*psi)) == semantics_mltl(drop(pi, i), *psi) by {
                convert_nnf_preserves_semantics(drop(pi, i), *phi);
                convert_nnf_preserves_semantics(drop(pi, i), *psi);
            }
        },
        Mltl::Not(g) => match *g {
            Mltl::True | Mltl::False | Mltl::Prop(_) => {
                assert(goal) by { reveal_with_fuel(semantics_mltl, 2); }
            },
            Mltl::Not(phi) => {
                assert(goal) by {
                    reveal_with_fuel(semantics_mltl, 2);
                    convert_nnf_preserves_semantics(pi, *phi);
                }
            },
            Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
                assert(goal) by {
                    reveal_with_fuel(semantics_mltl, 2);
                    convert_nnf_preserves_semantics(pi, Mltl::Not(phi));
                    convert_nnf_preserves_semantics(pi, Mltl::Not(psi));
                }
            },
            Mltl::Future(a, b, phi) | Mltl::Global(a, b, phi) => {
                assert(goal) by {
                    assert forall|i: nat| semantics_mltl(#[trigger] drop(pi, i), convert_nnf_spec(Mltl::Not(phi)))
                        == !semantics_mltl(drop(pi, i), *phi) by {
                        convert_nnf_preserves_semantics(drop(pi, i), Mltl::Not(phi));
                    }
                    reveal_with_fuel(semantics_mltl, 2);
                }
            },
            Mltl::Until(phi, a, b, psi) => {
                // Not (φ U ψ) ≡ (Not φ) R (Not ψ)
                let nphi = convert_nnf_spec(Mltl::Not(phi));
                let npsi = convert_nnf_spec(Mltl::Not(psi));
                let r = Mltl::Release(Box::new(Mltl::Not(phi)), a, b, Box::new(Mltl::Not(psi)));
                assert forall|i: nat| semantics_mltl(#[trigger] drop(pi, i), nphi)
                    == semantics_mltl(drop(pi, i), Mltl::Not(phi))
                    && semantics_mltl(drop(pi, i), npsi) == semantics_mltl(drop(pi, i), Mltl::Not(psi)) by {
                    convert_nnf_preserves_semantics(drop(pi, i), Mltl::Not(phi));
                    convert_nnf_preserves_semantics(drop(pi, i), Mltl::Not(psi));
                }
                assert(semantics_mltl(pi, Mltl::Release(Box::new(nphi), a, b, Box::new(npsi)))
                    == semantics_mltl(pi, r));
                assert(semantics_mltl(pi, Mltl::Until(phi, a, b, psi)) == !semantics_mltl(pi, r)) by {
                    until_release_dual(a, b, *phi, *psi);
                }
            },
            Mltl::Release(phi, a, b, psi) => {
                // Not (φ R ψ) ≡ (Not φ) U (Not ψ)
                let nphi = convert_nnf_spec(Mltl::Not(phi));
                let npsi = convert_nnf_spec(Mltl::Not(psi));
                let u = Mltl::Until(Box::new(Mltl::Not(phi)), a, b, Box::new(Mltl::Not(psi)));
                assert forall|i: nat| semantics_mltl(#[trigger] drop(pi, i), nphi)
                    == semantics_mltl(drop(pi, i), Mltl::Not(phi))
                    && semantics_mltl(drop(pi, i), npsi) == semantics_mltl(drop(pi, i), Mltl::Not(psi)) by {
                    convert_nnf_preserves_semantics(drop(pi, i), Mltl::Not(phi));
                    convert_nnf_preserves_semantics(drop(pi, i), Mltl::Not(psi));
                }
                assert(semantics_mltl(pi, Mltl::Until(Box::new(nphi), a, b, Box::new(npsi)))
                    == semantics_mltl(pi, u));
                assert(semantics_mltl(pi, Mltl::Release(phi, a, b, psi)) == !semantics_mltl(pi, u)) by {
                    release_until_dual(a, b, *phi, *psi);
                }
            },
        },
    }
}

/// `Not F = convert_nnf init_F ⟹ ∃p. F = Prop p`
pub proof fn convert_nnf_form_not_implies_prop<A>(big_f: Mltl<A>, init_f: Mltl<A>)
    requires
        Mltl::Not(Box::new(big_f)) == convert_nnf_spec(init_f),
    ensures
        exists|p: A| big_f == Mltl::Prop(p),
    decreases depth_mltl(init_f),
{
    reveal_with_fuel(depth_mltl, 2);
    match init_f {
        Mltl::Not(g) => match *g {
            Mltl::Prop(p) => {
                assert(big_f == Mltl::<A>::Prop(p));
            },
            Mltl::Not(phi) => convert_nnf_form_not_implies_prop(big_f, *phi),
            _ => {},
        },
        _ => {},
    }
}

/// `convert_nnf (convert_nnf F) = convert_nnf F`
pub proof fn convert_nnf_convert_nnf<A>(f: Mltl<A>)
    ensures
        convert_nnf_spec(convert_nnf_spec(f)) == convert_nnf_spec(f),
    decreases depth_mltl(f),
{
    reveal_with_fuel(depth_mltl, 2);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => match *g {
            Mltl::True | Mltl::False | Mltl::Prop(_) => {},
            Mltl::Not(phi) => convert_nnf_convert_nnf(*phi),
            Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
            | Mltl::Release(phi, _, _, psi) => {
                convert_nnf_convert_nnf(Mltl::Not(phi));
                convert_nnf_convert_nnf(Mltl::Not(psi));
            },
            Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
                convert_nnf_convert_nnf(Mltl::Not(phi));
            },
        },
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
        | Mltl::Release(phi, _, _, psi) => {
            convert_nnf_convert_nnf(*phi);
            convert_nnf_convert_nnf(*psi);
        },
        Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
            convert_nnf_convert_nnf(*phi);
        },
    }
}

/// `F = convert_nnf init_F ⟹ G ∈ subformulas F ⟹ ∃init_G. G = convert_nnf init_G`
///
/// Returns the witness `init_G` (stronger form of Isabelle's `∃`).
pub proof fn nnf_subformulas<A>(init_f: Mltl<A>, g: Mltl<A>) -> (init_g: Mltl<A>)
    requires
        subformulas(convert_nnf_spec(init_f)).contains(g),
    ensures
        g == convert_nnf_spec(init_g),
    decreases depth_mltl(init_f),
{
    reveal_with_fuel(depth_mltl, 2);
    reveal_with_fuel(subformulas, 2);
    match init_f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => { assert(false); arbitrary() },
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
        | Mltl::Release(phi, _, _, psi) => {
            if g == convert_nnf_spec(*phi) {
                *phi
            } else if g == convert_nnf_spec(*psi) {
                *psi
            } else if subformulas(convert_nnf_spec(*phi)).contains(g) {
                nnf_subformulas(*phi, g)
            } else {
                nnf_subformulas(*psi, g)
            }
        },
        Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
            if g == convert_nnf_spec(*phi) {
                *phi
            } else {
                nnf_subformulas(*phi, g)
            }
        },
        Mltl::Not(h) => match *h {
            Mltl::True | Mltl::False => { assert(false); arbitrary() },
            Mltl::Prop(p) => {
                assert(convert_nnf_spec(init_f) == Mltl::Not(Box::new(Mltl::Prop(p))));
                assert(subformulas(Mltl::Not(Box::new(Mltl::Prop(p)))) =~= Set::empty().insert(Mltl::Prop(p)));
                Mltl::Prop(p)
            },
            Mltl::Not(phi) => {
                assert(convert_nnf_spec(init_f) == convert_nnf_spec(*phi));
                nnf_subformulas(*phi, g)
            },
            Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
            | Mltl::Release(phi, _, _, psi) => {
                if g == convert_nnf_spec(Mltl::Not(phi)) {
                    Mltl::Not(phi)
                } else if g == convert_nnf_spec(Mltl::Not(psi)) {
                    Mltl::Not(psi)
                } else if subformulas(convert_nnf_spec(Mltl::Not(phi))).contains(g) {
                    nnf_subformulas(Mltl::Not(phi), g)
                } else {
                    nnf_subformulas(Mltl::Not(psi), g)
                }
            },
            Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
                if g == convert_nnf_spec(Mltl::Not(phi)) {
                    Mltl::Not(phi)
                } else {
                    nnf_subformulas(Mltl::Not(phi), g)
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Computation length
// ---------------------------------------------------------------------------

/// `complen_mltl φ`: trace length needed to evaluate `φ`.
pub open spec fn complen_mltl<A>(f: Mltl<A>) -> nat
    decreases f,
{
    match f {
        Mltl::False | Mltl::True | Mltl::Prop(_) => 1,
        Mltl::Not(phi) => complen_mltl(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => max_nat(complen_mltl(*phi), complen_mltl(*psi)),
        Mltl::Global(_, b, phi) | Mltl::Future(_, b, phi) => (b + complen_mltl(*phi)) as nat,
        Mltl::Release(phi, _, b, psi) | Mltl::Until(phi, _, b, psi) =>
            (b + max_nat(nat_sub(complen_mltl(*phi), 1), complen_mltl(*psi))) as nat,
    }
}

pub proof fn complen_geq_one<A>(f: Mltl<A>)
    ensures
        complen_mltl(f) >= 1,
    decreases f,
{
    match f {
        Mltl::False | Mltl::True | Mltl::Prop(_) => {},
        Mltl::Not(phi) => complen_geq_one(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => complen_geq_one(*phi),
        Mltl::Global(_, _, phi) | Mltl::Future(_, _, phi) => complen_geq_one(*phi),
        Mltl::Release(_, _, _, psi) | Mltl::Until(_, _, _, psi) => complen_geq_one(*psi),
    }
}

/// `make_empty_trace n`: `n` empty states.
pub open spec fn make_empty_trace<A>(n: nat) -> Seq<Set<A>>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        seq![Set::empty()] + make_empty_trace((n - 1) as nat)
    }
}

pub proof fn length_make_empty_trace<A>(n: nat)
    ensures
        make_empty_trace::<A>(n).len() == n,
    decreases n,
{
    if n > 0 {
        length_make_empty_trace::<A>((n - 1) as nat);
    }
}

/// `make_empty_trace (a+1) ⊨_m G[a,b] True = (a ≤ b)`
pub proof fn semantics_of_not_a_lteq_b<A>(a: usize, b: usize)
    ensures
        semantics_mltl(make_empty_trace::<A>((a + 1) as nat), Mltl::Global(a, b, Box::new(Mltl::True))) == (a <= b),
{
    reveal_with_fuel(semantics_mltl, 2);
    length_make_empty_trace::<A>((a + 1) as nat);
}

/// `make_empty_trace (a+1) ⊨_m Not (G[a,b] True) = ¬(a ≤ b)`
pub proof fn semantics_of_not_a_lteq_b2<A>(a: usize, b: usize)
    ensures
        semantics_mltl(
            make_empty_trace::<A>((a + 1) as nat),
            Mltl::Not(Box::new(Mltl::Global(a, b, Box::new(Mltl::True)))),
        ) == !(a <= b),
{
    semantics_of_not_a_lteq_b::<A>(a, b);
}

// ---------------------------------------------------------------------------
// Custom induction rules
// ---------------------------------------------------------------------------
// Isabelle states these as induction rules with named cases; here they are
// lemmas over a predicate `p: spec_fn(Mltl<A>) -> bool`, each case a
// quantified precondition.

/// `MLTL_induct`: for well-defined formulas, a semantics-invariant property
/// holds if it holds for True, False, Prop and is preserved by Not, And, Until.
pub proof fn mltl_induct<A>(p: spec_fn(Mltl<A>) -> bool, f: Mltl<A>)
    requires
        intervals_welldef(f),
        // PProp
        forall|f1: Mltl<A>, g1: Mltl<A>| #[trigger] semantic_equiv(f1, g1) ==> p(f1) == p(g1),
        p(Mltl::True),
        p(Mltl::False),
        forall|q: A| #[trigger] p(Mltl::Prop(q)),
        forall|g1: Mltl<A>| p(g1) ==> #[trigger] p(Mltl::Not(Box::new(g1))),
        forall|f1: Mltl<A>, f2: Mltl<A>| p(f1) && p(f2) ==> #[trigger] p(Mltl::And(Box::new(f1), Box::new(f2))),
        forall|f1: Mltl<A>, f2: Mltl<A>, a: usize, b: usize|
            p(f1) && p(f2) ==> #[trigger] p(Mltl::Until(Box::new(f1), a, b, Box::new(f2))),
    ensures
        p(f),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False => {},
        Mltl::Prop(q) => { assert(p(Mltl::Prop(q))); },
        Mltl::Not(g) => {
            mltl_induct(p, *g);
            assert(p(Mltl::Not(Box::new(*g))));
            assert(p(f));
        },
        Mltl::And(f1, f2) => {
            mltl_induct(p, *f1);
            mltl_induct(p, *f2);
            assert(p(Mltl::And(Box::new(*f1), Box::new(*f2))));
            assert(p(f));
        },
        Mltl::Or(f1, f2) => {
            mltl_induct(p, *f1);
            mltl_induct(p, *f2);
            // F1 Or F2 ≡ Not ((Not F1) And (Not F2))
            let nf1 = Mltl::Not(f1);
            let nf2 = Mltl::Not(f2);
            let rhs = Mltl::Not(Box::new(Mltl::And(Box::new(nf1), Box::new(nf2))));
            assert(p(rhs));
            assert(semantic_equiv(f, rhs)) by { reveal_with_fuel(semantics_mltl, 3); }
            assert(p(f));
        },
        Mltl::Future(a, b, g) => {
            mltl_induct(p, *g);
            let u = Mltl::Until(Box::new(Mltl::True), a, b, g);
            assert(p(u));
            future_as_until(a, b, *g);
            assert(semantic_equiv(f, u));
            assert(p(f));
        },
        Mltl::Global(a, b, g) => {
            mltl_induct(p, *g);
            // G φ ≡ Not (F (Not φ)) ≡ Not (True U (Not φ))
            let ng = Mltl::Not(g);
            let rhs = Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::True), a, b, Box::new(ng))));
            assert(p(rhs));
            globally_future_dual(a, b, *g);
            future_as_until(a, b, ng);
            let fut = Mltl::Future(a, b, Box::new(ng));
            let unt = Mltl::Until(Box::new(Mltl::True), a, b, Box::new(ng));
            assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, f) == semantics_mltl(pi, rhs) by {
                assert(semantics_mltl(pi, f) == semantics_mltl(pi, Mltl::Not(Box::new(fut))));
                assert(semantics_mltl(pi, fut) == semantics_mltl(pi, unt));
            }
            assert(p(f));
        },
        Mltl::Until(f1, a, b, f2) => {
            mltl_induct(p, *f1);
            mltl_induct(p, *f2);
            assert(p(Mltl::Until(Box::new(*f1), a, b, Box::new(*f2))));
            assert(p(f));
        },
        Mltl::Release(f1, a, b, f2) => {
            mltl_induct(p, *f1);
            mltl_induct(p, *f2);
            let rhs = Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(f1)), a, b, Box::new(Mltl::Not(f2)))));
            assert(p(rhs));
            release_until_dual(a, b, *f1, *f2);
            assert(semantic_equiv(f, rhs));
            assert(p(f));
        },
    }
}

/// `nnf_induct`: a property of NNF formulas (`F = convert_nnf init_F`) holds
/// if it holds for True, False, Prop, Not Prop and is preserved by the
/// remaining constructors.
pub proof fn nnf_induct<A>(p: spec_fn(Mltl<A>) -> bool, f: Mltl<A>, init_f: Mltl<A>)
    requires
        f == convert_nnf_spec(init_f),
        p(Mltl::True),
        p(Mltl::False),
        forall|q: A| #[trigger] p(Mltl::Prop(q)),
        forall|f1: Mltl<A>, f2: Mltl<A>| p(f1) && p(f2) ==> #[trigger] p(Mltl::And(Box::new(f1), Box::new(f2))),
        forall|f1: Mltl<A>, f2: Mltl<A>| p(f1) && p(f2) ==> #[trigger] p(Mltl::Or(Box::new(f1), Box::new(f2))),
        forall|f1: Mltl<A>, a: usize, b: usize| p(f1) ==> #[trigger] p(Mltl::Future(a, b, Box::new(f1))),
        forall|f1: Mltl<A>, a: usize, b: usize| p(f1) ==> #[trigger] p(Mltl::Global(a, b, Box::new(f1))),
        forall|f1: Mltl<A>, f2: Mltl<A>, a: usize, b: usize|
            p(f1) && p(f2) ==> #[trigger] p(Mltl::Until(Box::new(f1), a, b, Box::new(f2))),
        forall|f1: Mltl<A>, f2: Mltl<A>, a: usize, b: usize|
            p(f1) && p(f2) ==> #[trigger] p(Mltl::Release(Box::new(f1), a, b, Box::new(f2))),
        forall|q: A| #[trigger] p(Mltl::Not(Box::new(Mltl::Prop(q)))),
    ensures
        p(f),
    decreases f,
{
    reveal_with_fuel(subformulas, 1);
    match f {
        Mltl::True | Mltl::False => {},
        Mltl::Prop(q) => { assert(p(Mltl::Prop(q))); },
        Mltl::Not(g) => {
            convert_nnf_form_not_implies_prop(*g, init_f);
            let q = choose|q: A| *g == Mltl::Prop(q);
            assert(f == Mltl::Not(Box::new(Mltl::Prop(q))));
        },
        Mltl::And(f1, f2) => {
            assert(subformulas(f).contains(*f1));
            assert(subformulas(f).contains(*f2));
            let i1 = nnf_subformulas(init_f, *f1);
            let i2 = nnf_subformulas(init_f, *f2);
            nnf_induct(p, *f1, i1);
            nnf_induct(p, *f2, i2);
            assert(p(Mltl::And(Box::new(*f1), Box::new(*f2))));
        },
        Mltl::Or(f1, f2) => {
            assert(subformulas(f).contains(*f1));
            assert(subformulas(f).contains(*f2));
            let i1 = nnf_subformulas(init_f, *f1);
            let i2 = nnf_subformulas(init_f, *f2);
            nnf_induct(p, *f1, i1);
            nnf_induct(p, *f2, i2);
            assert(p(Mltl::Or(Box::new(*f1), Box::new(*f2))));
        },
        Mltl::Until(f1, a, b, f2) => {
            assert(subformulas(f).contains(*f1));
            assert(subformulas(f).contains(*f2));
            let i1 = nnf_subformulas(init_f, *f1);
            let i2 = nnf_subformulas(init_f, *f2);
            nnf_induct(p, *f1, i1);
            nnf_induct(p, *f2, i2);
            assert(p(Mltl::Until(Box::new(*f1), a, b, Box::new(*f2))));
        },
        Mltl::Release(f1, a, b, f2) => {
            assert(subformulas(f).contains(*f1));
            assert(subformulas(f).contains(*f2));
            let i1 = nnf_subformulas(init_f, *f1);
            let i2 = nnf_subformulas(init_f, *f2);
            nnf_induct(p, *f1, i1);
            nnf_induct(p, *f2, i2);
            assert(p(Mltl::Release(Box::new(*f1), a, b, Box::new(*f2))));
        },
        Mltl::Future(a, b, f1) => {
            assert(subformulas(f).contains(*f1));
            let i1 = nnf_subformulas(init_f, *f1);
            nnf_induct(p, *f1, i1);
            assert(p(Mltl::Future(a, b, Box::new(*f1))));
        },
        Mltl::Global(a, b, f1) => {
            assert(subformulas(f).contains(*f1));
            let i1 = nnf_subformulas(init_f, *f1);
            nnf_induct(p, *f1, i1);
            assert(p(Mltl::Global(a, b, Box::new(*f1))));
        },
    }
}

// ===========================================================================
// MLTL_Properties_Extended.thy (REU2026 isabelle-group; R2U2-specific parts
// omitted, see agent-docs/correspondence/mission-time-ltl.md)
// ===========================================================================

// ---------------------------------------------------------------------------
// Additional equivalence properties
// ---------------------------------------------------------------------------

pub proof fn globally_true<A>(a: usize, b: usize)
    requires
        a <= b,
    ensures
        semantic_equiv(Mltl::<A>::Global(a, b, Box::new(Mltl::True)), Mltl::True),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn future_false<A>(a: usize, b: usize)
    ensures
        semantic_equiv(Mltl::<A>::Future(a, b, Box::new(Mltl::False)), Mltl::False),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn false_until<A>(a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(Mltl::Until(Box::new(Mltl::False), a, b, Box::new(phi)), Mltl::Future(a, a, Box::new(phi))),
{
    reveal_with_fuel(semantics_mltl, 2);
    assert forall|pi: Seq<Set<A>>|
        #[trigger] semantics_mltl(pi, Mltl::Until(Box::new(Mltl::False), a, b, Box::new(phi)))
        == semantics_mltl(pi, Mltl::Future(a, a, Box::new(phi))) by {
        if semantics_mltl(pi, Mltl::Until(Box::new(Mltl::False), a, b, Box::new(phi))) {
            let i = choose|i: nat| (a <= i && i <= b) && (semantics_mltl(drop(pi, i), phi)
                && forall|j: nat| (j >= a && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), Mltl::<A>::False));
            if i > a {
                assert(semantics_mltl(drop(pi, a as nat), Mltl::<A>::False));
            }
        }
    }
}

pub proof fn until_false<A>(a: usize, b: usize, phi: Mltl<A>)
    ensures
        semantic_equiv(Mltl::Until(Box::new(phi), a, b, Box::new(Mltl::False)), Mltl::False),
{
    reveal_with_fuel(semantics_mltl, 2);
}

pub proof fn true_release<A>(a: usize, b: usize, psi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(Mltl::Release(Box::new(Mltl::True), a, b, Box::new(psi)), Mltl::Global(a, a, Box::new(psi))),
{
    reveal_with_fuel(semantics_mltl, 2);
    assert forall|pi: Seq<Set<A>>|
        #[trigger] semantics_mltl(pi, Mltl::Release(Box::new(Mltl::True), a, b, Box::new(psi)))
        == semantics_mltl(pi, Mltl::Global(a, a, Box::new(psi))) by {
        if pi.len() > a && semantics_mltl(drop(pi, a as nat), psi) && a < b {
            // witness j = a for the third disjunct
            assert(semantics_mltl(drop(pi, a as nat), Mltl::<A>::True));
            assert(forall|k: nat| (a <= k && k <= a) ==> semantics_mltl(#[trigger] drop(pi, k), psi));
        }
        if pi.len() > a && semantics_mltl(drop(pi, a as nat), psi) && a == b {
            assert(forall|i: nat| (a <= i && i <= b) ==> semantics_mltl(#[trigger] drop(pi, i), psi));
        }
        if semantics_mltl(pi, Mltl::Release(Box::new(Mltl::True), a, b, Box::new(psi))) && pi.len() > a {
            assert(semantics_mltl(drop(pi, a as nat), psi));
        }
    }
}

pub proof fn release_true<A>(a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        semantic_equiv(Mltl::Release(Box::new(phi), a, b, Box::new(Mltl::True)), Mltl::True),
{
    reveal_with_fuel(semantics_mltl, 2);
}

// Common equivalence pitfalls (the empty trace is the counterexample)

pub proof fn globally_false_is_not_false<A>(a: usize, b: usize)
    requires
        a <= b,
    ensures
        !semantic_equiv(Mltl::<A>::Global(a, b, Box::new(Mltl::False)), Mltl::False),
{
    assert(semantics_mltl(Seq::<Set<A>>::empty(), Mltl::<A>::Global(a, b, Box::new(Mltl::False))));
}

pub proof fn future_true_is_not_true<A>(a: usize, b: usize)
    requires
        a <= b,
    ensures
        !semantic_equiv(Mltl::<A>::Future(a, b, Box::new(Mltl::True)), Mltl::True),
{
    assert(!semantics_mltl(Seq::<Set<A>>::empty(), Mltl::<A>::Future(a, b, Box::new(Mltl::True))));
}

pub proof fn until_true_is_not_true<A>(a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        !semantic_equiv(Mltl::Until(Box::new(phi), a, b, Box::new(Mltl::True)), Mltl::True),
{
    assert(!semantics_mltl(Seq::<Set<A>>::empty(), Mltl::Until(Box::new(phi), a, b, Box::new(Mltl::True))));
}

pub proof fn release_false_is_not_false<A>(a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        !semantic_equiv(Mltl::Release(Box::new(phi), a, b, Box::new(Mltl::False)), Mltl::False),
{
    assert(semantics_mltl(Seq::<Set<A>>::empty(), Mltl::Release(Box::new(phi), a, b, Box::new(Mltl::False))));
}

// ---------------------------------------------------------------------------
// Contextual equivalence (CE) lemmas
// ---------------------------------------------------------------------------

pub proof fn semantic_equiv_reflexive<A>(phi: Mltl<A>)
    ensures
        semantic_equiv(phi, phi),
{
}

pub proof fn semantic_equiv_symmetric<A>(phi: Mltl<A>, psi: Mltl<A>)
    requires
        semantic_equiv(phi, psi),
    ensures
        semantic_equiv(psi, phi),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, psi) == semantics_mltl(pi, phi) by {
        assert(semantics_mltl(pi, phi) == semantics_mltl(pi, psi));
    }
}

pub proof fn semantic_equiv_transitive<A>(phi: Mltl<A>, psi: Mltl<A>, xi: Mltl<A>)
    requires
        semantic_equiv(phi, psi),
        semantic_equiv(psi, xi),
    ensures
        semantic_equiv(phi, xi),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, phi) == semantics_mltl(pi, xi) by {
        assert(semantics_mltl(pi, psi) == semantics_mltl(pi, xi));
    }
}

/// Helper: equivalent formulas agree on every suffix (instantiates
/// `semantic_equiv` at `drop(pi, i)` with the trigger used by `semantics_mltl`).
pub proof fn lemma_equiv_suffixes<A>(pi: Seq<Set<A>>, phi: Mltl<A>, phi2: Mltl<A>)
    requires
        semantic_equiv(phi, phi2),
    ensures
        forall|i: nat| semantics_mltl(#[trigger] drop(pi, i), phi) == semantics_mltl(drop(pi, i), phi2),
{
    assert forall|i: nat| semantics_mltl(#[trigger] drop(pi, i), phi) == semantics_mltl(drop(pi, i), phi2) by {
        assert(semantics_mltl(drop(pi, i), phi) == semantics_mltl(drop(pi, i), phi2));
    }
}

pub proof fn not_ce<A>(phi: Mltl<A>, phi2: Mltl<A>)
    requires
        semantic_equiv(phi, phi2),
    ensures
        semantic_equiv(Mltl::Not(Box::new(phi)), Mltl::Not(Box::new(phi2))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Not(Box::new(phi)))
        == semantics_mltl(pi, Mltl::Not(Box::new(phi2))) by {
        assert(semantics_mltl(pi, phi) == semantics_mltl(pi, phi2));
    }
}

pub proof fn and_ce_left<A>(phi: Mltl<A>, phi2: Mltl<A>, psi: Mltl<A>)
    requires
        semantic_equiv(phi, phi2),
    ensures
        semantic_equiv(Mltl::And(Box::new(phi), Box::new(psi)), Mltl::And(Box::new(phi2), Box::new(psi))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::And(Box::new(phi), Box::new(psi)))
        == semantics_mltl(pi, Mltl::And(Box::new(phi2), Box::new(psi))) by {
        assert(semantics_mltl(pi, phi) == semantics_mltl(pi, phi2));
    }
}

pub proof fn and_ce_right<A>(phi: Mltl<A>, psi: Mltl<A>, psi2: Mltl<A>)
    requires
        semantic_equiv(psi, psi2),
    ensures
        semantic_equiv(Mltl::And(Box::new(phi), Box::new(psi)), Mltl::And(Box::new(phi), Box::new(psi2))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::And(Box::new(phi), Box::new(psi)))
        == semantics_mltl(pi, Mltl::And(Box::new(phi), Box::new(psi2))) by {
        assert(semantics_mltl(pi, psi) == semantics_mltl(pi, psi2));
    }
}

pub proof fn or_ce_left<A>(phi: Mltl<A>, phi2: Mltl<A>, psi: Mltl<A>)
    requires
        semantic_equiv(phi, phi2),
    ensures
        semantic_equiv(Mltl::Or(Box::new(phi), Box::new(psi)), Mltl::Or(Box::new(phi2), Box::new(psi))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Or(Box::new(phi), Box::new(psi)))
        == semantics_mltl(pi, Mltl::Or(Box::new(phi2), Box::new(psi))) by {
        assert(semantics_mltl(pi, phi) == semantics_mltl(pi, phi2));
    }
}

pub proof fn or_ce_right<A>(phi: Mltl<A>, psi: Mltl<A>, psi2: Mltl<A>)
    requires
        semantic_equiv(psi, psi2),
    ensures
        semantic_equiv(Mltl::Or(Box::new(phi), Box::new(psi)), Mltl::Or(Box::new(phi), Box::new(psi2))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Or(Box::new(phi), Box::new(psi)))
        == semantics_mltl(pi, Mltl::Or(Box::new(phi), Box::new(psi2))) by {
        assert(semantics_mltl(pi, psi) == semantics_mltl(pi, psi2));
    }
}

pub proof fn globally_ce<A>(a: usize, b: usize, phi: Mltl<A>, phi2: Mltl<A>)
    requires
        semantic_equiv(phi, phi2),
    ensures
        semantic_equiv(Mltl::Global(a, b, Box::new(phi)), Mltl::Global(a, b, Box::new(phi2))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Global(a, b, Box::new(phi)))
        == semantics_mltl(pi, Mltl::Global(a, b, Box::new(phi2))) by {
        lemma_equiv_suffixes(pi, phi, phi2);
    }
}

pub proof fn future_ce<A>(a: usize, b: usize, phi: Mltl<A>, phi2: Mltl<A>)
    requires
        semantic_equiv(phi, phi2),
    ensures
        semantic_equiv(Mltl::Future(a, b, Box::new(phi)), Mltl::Future(a, b, Box::new(phi2))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Future(a, b, Box::new(phi)))
        == semantics_mltl(pi, Mltl::Future(a, b, Box::new(phi2))) by {
        lemma_equiv_suffixes(pi, phi, phi2);
    }
}

pub proof fn until_ce_left<A>(a: usize, b: usize, phi: Mltl<A>, phi2: Mltl<A>, psi: Mltl<A>)
    requires
        semantic_equiv(phi, phi2),
    ensures
        semantic_equiv(Mltl::Until(Box::new(phi), a, b, Box::new(psi)), Mltl::Until(Box::new(phi2), a, b, Box::new(psi))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi)))
        == semantics_mltl(pi, Mltl::Until(Box::new(phi2), a, b, Box::new(psi))) by {
        lemma_equiv_suffixes(pi, phi, phi2);
    }
}

pub proof fn until_ce_right<A>(a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>, psi2: Mltl<A>)
    requires
        semantic_equiv(psi, psi2),
    ensures
        semantic_equiv(Mltl::Until(Box::new(phi), a, b, Box::new(psi)), Mltl::Until(Box::new(phi), a, b, Box::new(psi2))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi)))
        == semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi2))) by {
        lemma_equiv_suffixes(pi, psi, psi2);
    }
}

pub proof fn release_ce_left<A>(a: usize, b: usize, phi: Mltl<A>, phi2: Mltl<A>, psi: Mltl<A>)
    requires
        semantic_equiv(phi, phi2),
    ensures
        semantic_equiv(Mltl::Release(Box::new(phi), a, b, Box::new(psi)), Mltl::Release(Box::new(phi2), a, b, Box::new(psi))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi)))
        == semantics_mltl(pi, Mltl::Release(Box::new(phi2), a, b, Box::new(psi))) by {
        lemma_equiv_suffixes(pi, phi, phi2);
    }
}

pub proof fn release_ce_right<A>(a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>, psi2: Mltl<A>)
    requires
        semantic_equiv(psi, psi2),
    ensures
        semantic_equiv(Mltl::Release(Box::new(phi), a, b, Box::new(psi)), Mltl::Release(Box::new(phi), a, b, Box::new(psi2))),
{
    assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi)))
        == semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi2))) by {
        lemma_equiv_suffixes(pi, psi, psi2);
    }
}

// ---------------------------------------------------------------------------
// Boolean normal form (BNF): only True, Prop, Not, And, Until
// ---------------------------------------------------------------------------

/// `is_bnf` (Isabelle: `inductive`). Encoded as the recursive predicate given
/// by Isabelle's `inductive_simps`; the induction rule is `is_bnf_induct`.
pub open spec fn is_bnf<A>(f: Mltl<A>) -> bool
    decreases f,
{
    match f {
        Mltl::True | Mltl::Prop(_) => true,
        Mltl::Not(phi) => is_bnf(*phi),
        Mltl::And(phi, psi) | Mltl::Until(phi, _, _, psi) => is_bnf(*phi) && is_bnf(*psi),
        Mltl::False | Mltl::Or(_, _) | Mltl::Future(_, _, _) | Mltl::Global(_, _, _)
        | Mltl::Release(_, _, _, _) => false,
    }
}

/// `is_bnf.induct`
pub proof fn is_bnf_induct<A>(p: spec_fn(Mltl<A>) -> bool, f: Mltl<A>)
    requires
        is_bnf(f),
        p(Mltl::True),
        forall|q: A| #[trigger] p(Mltl::Prop(q)),
        forall|phi: Mltl<A>| is_bnf(phi) && p(phi) ==> #[trigger] p(Mltl::Not(Box::new(phi))),
        forall|phi: Mltl<A>, psi: Mltl<A>| is_bnf(phi) && p(phi) && is_bnf(psi) && p(psi)
            ==> #[trigger] p(Mltl::And(Box::new(phi), Box::new(psi))),
        forall|phi: Mltl<A>, psi: Mltl<A>, a: usize, b: usize| is_bnf(phi) && p(phi) && is_bnf(psi) && p(psi)
            ==> #[trigger] p(Mltl::Until(Box::new(phi), a, b, Box::new(psi))),
    ensures
        p(f),
    decreases f,
{
    match f {
        Mltl::True => {},
        Mltl::Prop(q) => { assert(p(Mltl::Prop(q))); },
        Mltl::Not(phi) => {
            is_bnf_induct(p, *phi);
            assert(p(Mltl::Not(Box::new(*phi))));
        },
        Mltl::And(phi, psi) => {
            is_bnf_induct(p, *phi);
            is_bnf_induct(p, *psi);
            assert(p(Mltl::And(Box::new(*phi), Box::new(*psi))));
        },
        Mltl::Until(phi, a, b, psi) => {
            is_bnf_induct(p, *phi);
            is_bnf_induct(p, *psi);
            assert(p(Mltl::Until(Box::new(*phi), a, b, Box::new(*psi))));
        },
        _ => {},
    }
}

/// `convert_bnf`: rewrite into BNF using the standard dualities.
pub open spec fn convert_bnf_spec<A>(f: Mltl<A>) -> Mltl<A>
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::Not(Box::new(Mltl::True)),
        Mltl::Prop(p) => Mltl::Prop(p),
        Mltl::Not(phi) => Mltl::Not(Box::new(convert_bnf_spec(*phi))),
        Mltl::And(phi, psi) => Mltl::And(Box::new(convert_bnf_spec(*phi)), Box::new(convert_bnf_spec(*psi))),
        Mltl::Or(phi, psi) => Mltl::Not(Box::new(Mltl::And(
            Box::new(Mltl::Not(Box::new(convert_bnf_spec(*phi)))),
            Box::new(Mltl::Not(Box::new(convert_bnf_spec(*psi)))),
        ))),
        Mltl::Future(a, b, phi) => Mltl::Until(Box::new(Mltl::True), a, b, Box::new(convert_bnf_spec(*phi))),
        Mltl::Global(a, b, phi) => Mltl::Not(Box::new(Mltl::Until(
            Box::new(Mltl::True), a, b, Box::new(Mltl::Not(Box::new(convert_bnf_spec(*phi)))),
        ))),
        Mltl::Until(phi, a, b, psi) => Mltl::Until(Box::new(convert_bnf_spec(*phi)), a, b, Box::new(convert_bnf_spec(*psi))),
        Mltl::Release(phi, a, b, psi) => Mltl::Not(Box::new(Mltl::Until(
            Box::new(Mltl::Not(Box::new(convert_bnf_spec(*phi)))), a, b,
            Box::new(Mltl::Not(Box::new(convert_bnf_spec(*psi)))),
        ))),
    }
}

pub proof fn convert_bnf_is_bnf<A>(f: Mltl<A>)
    ensures
        is_bnf(convert_bnf_spec(f)),
    decreases f,
{
    reveal_with_fuel(is_bnf, 4);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => convert_bnf_is_bnf(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            convert_bnf_is_bnf(*phi);
            convert_bnf_is_bnf(*psi);
        },
    }
}

pub proof fn convert_bnf_welldef<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        intervals_welldef(convert_bnf_spec(f)),
    decreases f,
{
    reveal_with_fuel(intervals_welldef, 4);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => convert_bnf_welldef(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            convert_bnf_welldef(*phi);
            convert_bnf_welldef(*psi);
        },
    }
}

/// `intervals_welldef φ ⟹ φ ≡_m convert_bnf φ`
pub proof fn convert_bnf_equiv<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        semantic_equiv(f, convert_bnf_spec(f)),
    decreases f,
{
    match f {
        Mltl::True | Mltl::Prop(_) => {},
        Mltl::False => {
            assert(semantic_equiv(f, convert_bnf_spec(f))) by { reveal_with_fuel(semantics_mltl, 2); }
        },
        Mltl::Not(phi) => {
            convert_bnf_equiv(*phi);
            not_ce(*phi, convert_bnf_spec(*phi));
        },
        Mltl::And(phi, psi) => {
            convert_bnf_equiv(*phi);
            convert_bnf_equiv(*psi);
            and_ce_left(*phi, convert_bnf_spec(*phi), *psi);
            and_ce_right(convert_bnf_spec(*phi), *psi, convert_bnf_spec(*psi));
            semantic_equiv_transitive(f, Mltl::And(Box::new(convert_bnf_spec(*phi)), psi), convert_bnf_spec(f));
        },
        Mltl::Or(phi, psi) => {
            convert_bnf_equiv(*phi);
            convert_bnf_equiv(*psi);
            let (c1, c2) = (convert_bnf_spec(*phi), convert_bnf_spec(*psi));
            assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, f) == semantics_mltl(pi, convert_bnf_spec(f)) by {
                reveal_with_fuel(semantics_mltl, 3);
                assert(semantics_mltl(pi, *phi) == semantics_mltl(pi, c1));
                assert(semantics_mltl(pi, *psi) == semantics_mltl(pi, c2));
            }
        },
        Mltl::Future(a, b, phi) => {
            convert_bnf_equiv(*phi);
            future_ce(a, b, *phi, convert_bnf_spec(*phi));
            future_as_until(a, b, convert_bnf_spec(*phi));
            semantic_equiv_transitive(f, Mltl::Future(a, b, Box::new(convert_bnf_spec(*phi))), convert_bnf_spec(f));
        },
        Mltl::Global(a, b, phi) => {
            convert_bnf_equiv(*phi);
            let c = convert_bnf_spec(*phi);
            globally_ce(a, b, *phi, c);
            globally_future_dual(a, b, c);
            future_as_until(a, b, Mltl::Not(Box::new(c)));
            let fut = Mltl::Future(a, b, Box::new(Mltl::Not(Box::new(c))));
            let unt = Mltl::Until(Box::new(Mltl::True), a, b, Box::new(Mltl::Not(Box::new(c))));
            not_ce(fut, unt);
            semantic_equiv_transitive(f, Mltl::Global(a, b, Box::new(c)), Mltl::Not(Box::new(fut)));
            semantic_equiv_transitive(f, Mltl::Not(Box::new(fut)), convert_bnf_spec(f));
        },
        Mltl::Until(phi, a, b, psi) => {
            convert_bnf_equiv(*phi);
            convert_bnf_equiv(*psi);
            until_ce_left(a, b, *phi, convert_bnf_spec(*phi), *psi);
            until_ce_right(a, b, convert_bnf_spec(*phi), *psi, convert_bnf_spec(*psi));
            semantic_equiv_transitive(f, Mltl::Until(Box::new(convert_bnf_spec(*phi)), a, b, psi), convert_bnf_spec(f));
        },
        Mltl::Release(phi, a, b, psi) => {
            convert_bnf_equiv(*phi);
            convert_bnf_equiv(*psi);
            let (c1, c2) = (convert_bnf_spec(*phi), convert_bnf_spec(*psi));
            release_ce_left(a, b, *phi, c1, *psi);
            release_ce_right(a, b, c1, *psi, c2);
            semantic_equiv_transitive(f, Mltl::Release(Box::new(c1), a, b, psi), Mltl::Release(Box::new(c1), a, b, Box::new(c2)));
            release_until_dual(a, b, c1, c2);
            semantic_equiv_transitive(f, Mltl::Release(Box::new(c1), a, b, Box::new(c2)), convert_bnf_spec(f));
        },
    }
}

pub proof fn convert_bnf_complen<A>(f: Mltl<A>)
    ensures
        complen_mltl(f) == complen_mltl(convert_bnf_spec(f)),
    decreases f,
{
    reveal_with_fuel(complen_mltl, 4);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => convert_bnf_complen(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            convert_bnf_complen(*phi);
            convert_bnf_complen(*psi);
        },
    }
}

pub proof fn bnf_convert_bnf<A>(f: Mltl<A>)
    requires
        is_bnf(f),
    ensures
        convert_bnf_spec(f) == f,
    decreases f,
{
    match f {
        Mltl::Not(phi) => bnf_convert_bnf(*phi),
        Mltl::And(phi, psi) | Mltl::Until(phi, _, _, psi) => {
            bnf_convert_bnf(*phi);
            bnf_convert_bnf(*psi);
        },
        _ => {},
    }
}

pub proof fn convert_bnf_convert_bnf<A>(f: Mltl<A>)
    ensures
        convert_bnf_spec(convert_bnf_spec(f)) == convert_bnf_spec(f),
{
    convert_bnf_is_bnf(f);
    bnf_convert_bnf(convert_bnf_spec(f));
}

// ---------------------------------------------------------------------------
// Semantic unrolling lemmas (cases a = b and a < b)
// ---------------------------------------------------------------------------

/// `complen φ ≤ length π` for a temporal operator with upper bound `b`
/// implies `b < length π` (helper used by every unrolling lemma).
proof fn lemma_complen_bound<A>(pi: Seq<Set<A>>, f: Mltl<A>)
    requires
        pi.len() >= complen_mltl(f),
    ensures
        f is Future ==> f->Future_1 < pi.len(),
        f is Global ==> f->Global_1 < pi.len(),
        f is Until ==> f->Until_2 < pi.len(),
        f is Release ==> f->Release_2 < pi.len(),
{
    match f {
        Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => complen_geq_one(*phi),
        Mltl::Until(_, _, _, psi) | Mltl::Release(_, _, _, psi) => complen_geq_one(*psi),
        _ => {},
    }
}

pub proof fn until_base_mltl_semantics<A>(pi: Seq<Set<A>>, a: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        pi.len() > a,
    ensures
        semantics_mltl(pi, Mltl::Until(Box::new(phi), a, a, Box::new(psi))) == semantics_mltl(drop(pi, a as nat), psi),
{
}

pub proof fn until_unrolling_mltl_semantics<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a < b,
        pi.len() >= complen_mltl(Mltl::Until(Box::new(phi), a, b, Box::new(psi))),
    ensures
        semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi))) == (
            semantics_mltl(drop(pi, a as nat), psi) || (semantics_mltl(drop(pi, a as nat), phi)
                && semantics_mltl(pi, Mltl::Until(Box::new(phi), (a + 1) as usize, b, Box::new(psi))))),
{
    lemma_complen_bound(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi)));
    let lhs = semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi)));
    let rest = semantics_mltl(pi, Mltl::Until(Box::new(phi), (a + 1) as usize, b, Box::new(psi)));
    if lhs {
        let i = choose|i: nat| (a <= i && i <= b) && (semantics_mltl(drop(pi, i), psi)
            && forall|j: nat| (j >= a && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        if i > a {
            assert(semantics_mltl(drop(pi, a as nat), phi));
            assert(forall|j: nat| (j >= a + 1 && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
            assert(rest);
        }
    }
    if semantics_mltl(drop(pi, a as nat), psi) {
        assert(forall|j: nat| (j >= a && j < a) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        assert(lhs);
    }
    if semantics_mltl(drop(pi, a as nat), phi) && rest {
        let i = choose|i: nat| (a + 1 <= i && i <= b) && (semantics_mltl(drop(pi, i), psi)
            && forall|j: nat| (j >= a + 1 && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        assert(forall|j: nat| (j >= a && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        assert(lhs);
    }
}

pub proof fn future_base_mltl_semantics<A>(pi: Seq<Set<A>>, a: usize, psi: Mltl<A>)
    requires
        pi.len() > a,
    ensures
        semantics_mltl(pi, Mltl::Future(a, a, Box::new(psi))) == semantics_mltl(drop(pi, a as nat), psi),
{
}

pub proof fn future_unrolling_mltl_semantics<A>(pi: Seq<Set<A>>, a: usize, b: usize, psi: Mltl<A>)
    requires
        a < b,
        pi.len() >= complen_mltl(Mltl::Future(a, b, Box::new(psi))),
    ensures
        semantics_mltl(pi, Mltl::Future(a, b, Box::new(psi))) == (
            semantics_mltl(drop(pi, a as nat), psi)
                || semantics_mltl(pi, Mltl::Future((a + 1) as usize, b, Box::new(psi)))),
{
    lemma_complen_bound(pi, Mltl::Future(a, b, Box::new(psi)));
    if semantics_mltl(pi, Mltl::Future(a, b, Box::new(psi))) {
        let i = choose|i: nat| (a <= i && i <= b) && semantics_mltl(drop(pi, i), psi);
        if i > a {
            assert(semantics_mltl(pi, Mltl::Future((a + 1) as usize, b, Box::new(psi))));
        }
    }
}

pub proof fn global_base_mltl_semantics<A>(pi: Seq<Set<A>>, a: usize, psi: Mltl<A>)
    requires
        pi.len() > a,
    ensures
        semantics_mltl(pi, Mltl::Global(a, a, Box::new(psi))) == semantics_mltl(drop(pi, a as nat), psi),
{
    if semantics_mltl(drop(pi, a as nat), psi) {
        assert(forall|i: nat| (a <= i && i <= a) ==> semantics_mltl(#[trigger] drop(pi, i), psi));
    }
}

pub proof fn global_unrolling_mltl_semantics<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        a < b,
        pi.len() >= complen_mltl(Mltl::Global(a, b, Box::new(phi))),
    ensures
        semantics_mltl(pi, Mltl::Global(a, b, Box::new(phi))) == (
            semantics_mltl(drop(pi, a as nat), phi)
                && semantics_mltl(pi, Mltl::Global((a + 1) as usize, b, Box::new(phi)))),
{
    lemma_complen_bound(pi, Mltl::Global(a, b, Box::new(phi)));
    if semantics_mltl(drop(pi, a as nat), phi) && semantics_mltl(pi, Mltl::Global((a + 1) as usize, b, Box::new(phi))) {
        assert(forall|i: nat| (a <= i && i <= b) ==> semantics_mltl(#[trigger] drop(pi, i), phi));
    }
}

pub proof fn release_base_mltl_semantics<A>(pi: Seq<Set<A>>, a: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        pi.len() > a,
    ensures
        semantics_mltl(pi, Mltl::Release(Box::new(phi), a, a, Box::new(psi))) == semantics_mltl(drop(pi, a as nat), psi),
{
    if semantics_mltl(drop(pi, a as nat), psi) {
        assert(forall|i: nat| (a <= i && i <= a) ==> semantics_mltl(#[trigger] drop(pi, i), psi));
    }
}

pub proof fn release_unrolling_mltl_semantics<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a < b,
        pi.len() >= complen_mltl(Mltl::Release(Box::new(phi), a, b, Box::new(psi))),
    ensures
        semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))) == (
            semantics_mltl(drop(pi, a as nat), psi) && (semantics_mltl(drop(pi, a as nat), phi)
                || semantics_mltl(pi, Mltl::Release(Box::new(phi), (a + 1) as usize, b, Box::new(psi))))),
{
    lemma_complen_bound(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi)));
    let lhs = semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi)));
    let rest = semantics_mltl(pi, Mltl::Release(Box::new(phi), (a + 1) as usize, b, Box::new(psi)));
    let pa = semantics_mltl(drop(pi, a as nat), phi);
    let qa = semantics_mltl(drop(pi, a as nat), psi);
    if lhs {
        if forall|i: nat| (a <= i && i <= b) ==> semantics_mltl(#[trigger] drop(pi, i), psi) {
            assert(qa);
            assert(forall|i: nat| (a + 1 <= i && i <= b) ==> semantics_mltl(#[trigger] drop(pi, i), psi));
        } else {
            let j = choose|j: nat| (j >= a && j <= nat_sub(b as nat, 1)) && semantics_mltl(drop(pi, j), phi)
                && forall|k: nat| (a <= k && k <= j) ==> semantics_mltl(#[trigger] drop(pi, k), psi);
            assert(qa);
            if j > a {
                assert(forall|k: nat| (a + 1 <= k && k <= j) ==> semantics_mltl(#[trigger] drop(pi, k), psi));
                assert(rest);
            }
        }
    }
    if qa && pa {
        assert(forall|k: nat| (a <= k && k <= a) ==> semantics_mltl(#[trigger] drop(pi, k), psi));
        assert(lhs);
    }
    if qa && rest {
        if forall|i: nat| (a + 1 <= i && i <= b) ==> semantics_mltl(#[trigger] drop(pi, i), psi) {
            assert(forall|i: nat| (a <= i && i <= b) ==> semantics_mltl(#[trigger] drop(pi, i), psi));
        } else {
            let j = choose|j: nat| (j >= a + 1 && j <= nat_sub(b as nat, 1)) && semantics_mltl(drop(pi, j), phi)
                && forall|k: nat| (a + 1 <= k && k <= j) ==> semantics_mltl(#[trigger] drop(pi, k), psi);
            assert(forall|k: nat| (a <= k && k <= j) ==> semantics_mltl(#[trigger] drop(pi, k), psi));
        }
        assert(lhs);
    }
}

// ---------------------------------------------------------------------------
// Normalized shifted-trace semantic unrolling
// ---------------------------------------------------------------------------

pub proof fn bounded_exists_shift(p: spec_fn(nat) -> bool, k: nat, b: nat)
    requires
        k <= b,
    ensures
        (exists|i: nat| k <= i && i <= b && #[trigger] p(i))
            == (exists|j: nat| j <= b - k && #[trigger] p(j + k)),
{
    if exists|i: nat| k <= i && i <= b && #[trigger] p(i) {
        let i = choose|i: nat| k <= i && i <= b && #[trigger] p(i);
        assert(p((i - k) as nat + k));
    }
    if exists|j: nat| j <= b - k && #[trigger] p(j + k) {
        let j = choose|j: nat| j <= b - k && #[trigger] p(j + k);
        assert(p(j + k));
    }
}

pub proof fn bounded_forall_shift(p: spec_fn(nat) -> bool, k: nat, b: nat)
    requires
        k <= b,
    ensures
        (forall|i: nat| k <= i && i <= b ==> #[trigger] p(i))
            == (forall|j: nat| j <= b - k ==> #[trigger] p(j + k)),
{
    if forall|j: nat| j <= b - k ==> #[trigger] p(j + k) {
        assert forall|i: nat| k <= i && i <= b implies #[trigger] p(i) by {
            assert(p((i - k) as nat + k));
        }
    }
}

pub proof fn bounded_until_shift(q: spec_fn(nat) -> bool, p: spec_fn(nat) -> bool, k: nat, b: nat)
    requires
        k <= b,
    ensures
        (exists|i: nat| k <= i && i <= b && #[trigger] q(i) && (forall|m: nat| k <= m && m < i ==> #[trigger] p(m)))
            == (exists|j: nat| j <= b - k && #[trigger] q(j + k) && (forall|n: nat| n < j ==> #[trigger] p(n + k))),
{
    if exists|i: nat| k <= i && i <= b && #[trigger] q(i) && (forall|m: nat| k <= m && m < i ==> #[trigger] p(m)) {
        let i = choose|i: nat| k <= i && i <= b && #[trigger] q(i) && (forall|m: nat| k <= m && m < i ==> #[trigger] p(m));
        let j = (i - k) as nat;
        assert(q(j + k));
        assert forall|n: nat| n < j implies #[trigger] p(n + k) by {}
    }
    if exists|j: nat| j <= b - k && #[trigger] q(j + k) && (forall|n: nat| n < j ==> #[trigger] p(n + k)) {
        let j = choose|j: nat| j <= b - k && #[trigger] q(j + k) && (forall|n: nat| n < j ==> #[trigger] p(n + k));
        assert forall|m: nat| k <= m && m < j + k implies #[trigger] p(m) by {
            assert(p((m - k) as nat + k));
        }
        assert(q(j + k));
    }
}

/// `k ≤ b ⟹ (π ⊨ F[k,b] φ) = (drop k π ⊨ F[0,b-k] φ)`
pub proof fn semantic_shift_f<A>(pi: Seq<Set<A>>, k: usize, b: usize, phi: Mltl<A>)
    requires
        k <= b,
    ensures
        semantics_mltl(pi, Mltl::Future(k, b, Box::new(phi)))
            == semantics_mltl(drop(pi, k as nat), Mltl::Future(0, (b - k) as usize, Box::new(phi))),
{
    let d = drop(pi, k as nat);
    lemma_drop_len(pi, k as nat);
    assert forall|j: nat| #[trigger] drop(d, j) == drop(pi, (k + j) as nat) by { lemma_drop_drop(pi, k as nat, j); }
    if semantics_mltl(pi, Mltl::Future(k, b, Box::new(phi))) {
        let i = choose|i: nat| (k <= i && i <= b) && semantics_mltl(drop(pi, i), phi);
        assert(drop(d, (i - k) as nat) == drop(pi, i));
    }
}

/// `k ≤ b ⟹ (π ⊨ φ U[k,b] ψ) = (drop k π ⊨ φ U[0,b-k] ψ)`
pub proof fn semantic_shift_u<A>(pi: Seq<Set<A>>, k: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        k <= b,
    ensures
        semantics_mltl(pi, Mltl::Until(Box::new(phi), k, b, Box::new(psi)))
            == semantics_mltl(drop(pi, k as nat), Mltl::Until(Box::new(phi), 0, (b - k) as usize, Box::new(psi))),
{
    let d = drop(pi, k as nat);
    lemma_drop_len(pi, k as nat);
    assert forall|j: nat| #[trigger] drop(d, j) == drop(pi, (k + j) as nat) by { lemma_drop_drop(pi, k as nat, j); }
    if semantics_mltl(pi, Mltl::Until(Box::new(phi), k, b, Box::new(psi))) {
        let i = choose|i: nat| (k <= i && i <= b) && (semantics_mltl(drop(pi, i), psi)
            && forall|j: nat| (j >= k && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        let i2 = (i - k) as nat;
        assert(drop(d, i2) == drop(pi, i));
        assert forall|j: nat| (j >= 0 && j < i2) implies semantics_mltl(#[trigger] drop(d, j), phi) by {
            assert(drop(d, j) == drop(pi, (k + j) as nat));
        }
    }
    if semantics_mltl(d, Mltl::Until(Box::new(phi), 0, (b - k) as usize, Box::new(psi))) {
        let i2 = choose|i: nat| (0 <= i && i <= b - k) && (semantics_mltl(drop(d, i), psi)
            && forall|j: nat| (j >= 0 && j < i) ==> semantics_mltl(#[trigger] drop(d, j), phi));
        assert(drop(d, i2) == drop(pi, (k + i2) as nat));
        assert forall|j: nat| (j >= k && j < k + i2) implies semantics_mltl(#[trigger] drop(pi, j), phi) by {
            assert(drop(d, (j - k) as nat) == drop(pi, j));
        }
    }
}

/// `k ≤ b ⟹ (π ⊨ G[k,b] φ) = (drop k π ⊨ G[0,b-k] φ)`
pub proof fn semantic_shift_g<A>(pi: Seq<Set<A>>, k: usize, b: usize, phi: Mltl<A>)
    requires
        k <= b,
    ensures
        semantics_mltl(pi, Mltl::Global(k, b, Box::new(phi)))
            == semantics_mltl(drop(pi, k as nat), Mltl::Global(0, (b - k) as usize, Box::new(phi))),
{
    let d = drop(pi, k as nat);
    lemma_drop_len(pi, k as nat);
    assert forall|j: nat| #[trigger] drop(d, j) == drop(pi, (k + j) as nat) by { lemma_drop_drop(pi, k as nat, j); }
    if semantics_mltl(d, Mltl::Global(0, (b - k) as usize, Box::new(phi))) && pi.len() > k {
        assert forall|i: nat| (k <= i && i <= b) implies semantics_mltl(#[trigger] drop(pi, i), phi) by {
            assert(drop(d, (i - k) as nat) == drop(pi, i));
        }
    }
}

/// `k ≤ b ⟹ (π ⊨ φ R[k,b] ψ) = (drop k π ⊨ φ R[0,b-k] ψ)` (via the duals)
pub proof fn semantic_shift_r<A>(pi: Seq<Set<A>>, k: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        k <= b,
    ensures
        semantics_mltl(pi, Mltl::Release(Box::new(phi), k, b, Box::new(psi)))
            == semantics_mltl(drop(pi, k as nat), Mltl::Release(Box::new(phi), 0, (b - k) as usize, Box::new(psi))),
{
    let nphi = Mltl::Not(Box::new(phi));
    let npsi = Mltl::Not(Box::new(psi));
    release_until_dual(k, b, phi, psi);
    release_until_dual(0, (b - k) as usize, phi, psi);
    semantic_shift_u(pi, k, b, nphi, npsi);
    assert(semantics_mltl(pi, Mltl::Release(Box::new(phi), k, b, Box::new(psi)))
        == !semantics_mltl(pi, Mltl::Until(Box::new(nphi), k, b, Box::new(npsi))));
    assert(semantics_mltl(drop(pi, k as nat), Mltl::Release(Box::new(phi), 0, (b - k) as usize, Box::new(psi)))
        == !semantics_mltl(drop(pi, k as nat), Mltl::Until(Box::new(nphi), 0, (b - k) as usize, Box::new(npsi))));
}

pub proof fn semantic_unroll_f<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        a < b,
        complen_mltl(Mltl::Future(a, b, Box::new(phi))) <= pi.len(),
    ensures
        semantics_mltl(pi, Mltl::Future(a, b, Box::new(phi))) == (semantics_mltl(drop(pi, a as nat), phi)
            || semantics_mltl(drop(pi, (a + 1) as nat), Mltl::Future(0, (b - a - 1) as usize, Box::new(phi)))),
{
    future_unrolling_mltl_semantics(pi, a, b, phi);
    semantic_shift_f(pi, (a + 1) as usize, b, phi);
}

pub proof fn semantic_unroll_u<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a < b,
        complen_mltl(Mltl::Until(Box::new(phi), a, b, Box::new(psi))) <= pi.len(),
    ensures
        semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi))) == (semantics_mltl(drop(pi, a as nat), psi)
            || (semantics_mltl(drop(pi, a as nat), phi)
                && semantics_mltl(drop(pi, (a + 1) as nat), Mltl::Until(Box::new(phi), 0, (b - a - 1) as usize, Box::new(psi))))),
{
    until_unrolling_mltl_semantics(pi, a, b, phi, psi);
    semantic_shift_u(pi, (a + 1) as usize, b, phi, psi);
}

pub proof fn semantic_unroll_g<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        a < b,
        complen_mltl(Mltl::Global(a, b, Box::new(phi))) <= pi.len(),
    ensures
        semantics_mltl(pi, Mltl::Global(a, b, Box::new(phi))) == (semantics_mltl(drop(pi, a as nat), phi)
            && semantics_mltl(drop(pi, (a + 1) as nat), Mltl::Global(0, (b - a - 1) as usize, Box::new(phi)))),
{
    global_unrolling_mltl_semantics(pi, a, b, phi);
    semantic_shift_g(pi, (a + 1) as usize, b, phi);
}

pub proof fn semantic_unroll_r<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a < b,
        complen_mltl(Mltl::Release(Box::new(phi), a, b, Box::new(psi))) <= pi.len(),
    ensures
        semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))) == (semantics_mltl(drop(pi, a as nat), psi)
            && (semantics_mltl(drop(pi, a as nat), phi)
                || semantics_mltl(drop(pi, (a + 1) as nat), Mltl::Release(Box::new(phi), 0, (b - a - 1) as usize, Box::new(psi))))),
{
    release_unrolling_mltl_semantics(pi, a, b, phi, psi);
    semantic_shift_r(pi, (a + 1) as usize, b, phi, psi);
}

// ---------------------------------------------------------------------------
// Executable semantic evaluation (spec-level; exec counterpart is T2.7)
// ---------------------------------------------------------------------------
// The checked evaluator `mltl_eval` does the interval and end-of-trace checks
// once when entering a temporal operator; `mltl_eval_unchecked` then follows
// the base/recursive cases of the unrolling lemmas. Nested subformulas go back
// through `mltl_eval` on the new suffix.

pub open spec fn mltl_eval_interval_width<A>(f: Mltl<A>) -> nat {
    match f {
        Mltl::Future(a, b, _) | Mltl::Global(a, b, _) => nat_sub(b as nat, a as nat),
        Mltl::Until(_, a, b, _) | Mltl::Release(_, a, b, _) => nat_sub(b as nat, a as nat),
        _ => 0,
    }
}

/// `mltl_eval` (Isabelle: `function`, mutually recursive with
/// `mltl_eval_unchecked`; termination by lexicographic `size φ`, interval
/// width, checked-before-unchecked. Here `depth_mltl` replaces `size`.)
pub open spec fn mltl_eval_spec<A>(f: Mltl<A>, pi: Seq<Set<A>>) -> bool
    decreases depth_mltl(f), mltl_eval_interval_width(f), 1nat,
    via mltl_eval_spec_decreases::<A>
{
    match f {
        Mltl::True => true,
        Mltl::False => false,
        Mltl::Prop(q) => pi.len() != 0 && pi[0].contains(q),
        Mltl::Not(phi) => !mltl_eval_spec(*phi, pi),
        Mltl::And(phi, psi) => mltl_eval_spec(*phi, pi) && mltl_eval_spec(*psi, pi),
        Mltl::Or(phi, psi) => mltl_eval_spec(*phi, pi) || mltl_eval_spec(*psi, pi),
        Mltl::Future(a, b, _) | Mltl::Until(_, a, b, _) =>
            if b < a { false } else if a >= pi.len() { false } else { mltl_eval_unchecked_spec(f, pi) },
        Mltl::Global(a, b, _) | Mltl::Release(_, a, b, _) =>
            if b < a { false } else if a >= pi.len() { true } else { mltl_eval_unchecked_spec(f, pi) },
    }
}

pub open spec fn mltl_eval_unchecked_spec<A>(f: Mltl<A>, pi: Seq<Set<A>>) -> bool
    decreases depth_mltl(f), mltl_eval_interval_width(f), 0nat,
    via mltl_eval_unchecked_spec_decreases::<A>
{
    match f {
        Mltl::True => true,
        Mltl::False => false,
        Mltl::Prop(q) => pi.len() != 0 && pi[0].contains(q),
        Mltl::Not(phi) => !mltl_eval_spec(*phi, pi),
        Mltl::And(phi, psi) => mltl_eval_spec(*phi, pi) && mltl_eval_spec(*psi, pi),
        Mltl::Or(phi, psi) => mltl_eval_spec(*phi, pi) || mltl_eval_spec(*psi, pi),
        Mltl::Future(a, b, phi) =>
            if b < a { false }
            else if mltl_eval_spec(*phi, drop(pi, a as nat)) { true }
            else if a == b { false }
            else { mltl_eval_unchecked_spec(Mltl::Future((a + 1) as usize, b, phi), pi) },
        Mltl::Global(a, b, phi) =>
            if b < a { false }
            else if !mltl_eval_spec(*phi, drop(pi, a as nat)) { false }
            else if a == b { true }
            else { mltl_eval_unchecked_spec(Mltl::Global((a + 1) as usize, b, phi), pi) },
        Mltl::Until(phi, a, b, psi) =>
            if b < a { false }
            else if mltl_eval_spec(*psi, drop(pi, a as nat)) { true }
            else if a == b { false }
            else if mltl_eval_spec(*phi, drop(pi, a as nat)) {
                mltl_eval_unchecked_spec(Mltl::Until(phi, (a + 1) as usize, b, psi), pi)
            } else { false },
        Mltl::Release(phi, a, b, psi) =>
            if b < a { false }
            else if !mltl_eval_spec(*psi, drop(pi, a as nat)) { false }
            else if a == b { true }
            else if mltl_eval_spec(*phi, drop(pi, a as nat)) { true }
            else { mltl_eval_unchecked_spec(Mltl::Release(phi, (a + 1) as usize, b, psi), pi) },
    }
}

#[via_fn]
proof fn mltl_eval_spec_decreases<A>(f: Mltl<A>, pi: Seq<Set<A>>) {
    reveal_with_fuel(depth_mltl, 2);
}

#[via_fn]
proof fn mltl_eval_unchecked_spec_decreases<A>(f: Mltl<A>, pi: Seq<Set<A>>) {
    reveal_with_fuel(depth_mltl, 2);
}

pub proof fn mltl_eval_future_base<A>(pi: Seq<Set<A>>, a: usize, phi: Mltl<A>)
    requires
        a < pi.len(),
    ensures
        mltl_eval_spec(Mltl::Future(a, a, Box::new(phi)), pi) == mltl_eval_spec(phi, drop(pi, a as nat)),
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
}

pub proof fn mltl_eval_global_base<A>(pi: Seq<Set<A>>, a: usize, phi: Mltl<A>)
    requires
        a < pi.len(),
    ensures
        mltl_eval_spec(Mltl::Global(a, a, Box::new(phi)), pi) == mltl_eval_spec(phi, drop(pi, a as nat)),
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
}

pub proof fn mltl_eval_until_base<A>(pi: Seq<Set<A>>, a: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a < pi.len(),
    ensures
        mltl_eval_spec(Mltl::Until(Box::new(phi), a, a, Box::new(psi)), pi) == mltl_eval_spec(psi, drop(pi, a as nat)),
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
}

pub proof fn mltl_eval_release_base<A>(pi: Seq<Set<A>>, a: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a < pi.len(),
    ensures
        mltl_eval_spec(Mltl::Release(Box::new(phi), a, a, Box::new(psi)), pi) == mltl_eval_spec(psi, drop(pi, a as nat)),
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
}

pub proof fn mltl_eval_future_unrolling<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        a < b,
        complen_mltl(Mltl::Future(a, b, Box::new(phi))) <= pi.len(),
    ensures
        mltl_eval_spec(Mltl::Future(a, b, Box::new(phi)), pi) == (mltl_eval_spec(phi, drop(pi, a as nat))
            || mltl_eval_spec(Mltl::Future((a + 1) as usize, b, Box::new(phi)), pi)),
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
    lemma_complen_bound(pi, Mltl::Future(a, b, Box::new(phi)));
}

pub proof fn mltl_eval_global_unrolling<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        a < b,
        complen_mltl(Mltl::Global(a, b, Box::new(phi))) <= pi.len(),
    ensures
        mltl_eval_spec(Mltl::Global(a, b, Box::new(phi)), pi) == (mltl_eval_spec(phi, drop(pi, a as nat))
            && mltl_eval_spec(Mltl::Global((a + 1) as usize, b, Box::new(phi)), pi)),
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
    lemma_complen_bound(pi, Mltl::Global(a, b, Box::new(phi)));
}

pub proof fn mltl_eval_until_unrolling<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a < b,
        complen_mltl(Mltl::Until(Box::new(phi), a, b, Box::new(psi))) <= pi.len(),
    ensures
        mltl_eval_spec(Mltl::Until(Box::new(phi), a, b, Box::new(psi)), pi) == (mltl_eval_spec(psi, drop(pi, a as nat))
            || (mltl_eval_spec(phi, drop(pi, a as nat))
                && mltl_eval_spec(Mltl::Until(Box::new(phi), (a + 1) as usize, b, Box::new(psi)), pi))),
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
    lemma_complen_bound(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi)));
}

pub proof fn mltl_eval_release_unrolling<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a < b,
        complen_mltl(Mltl::Release(Box::new(phi), a, b, Box::new(psi))) <= pi.len(),
    ensures
        mltl_eval_spec(Mltl::Release(Box::new(phi), a, b, Box::new(psi)), pi) == (mltl_eval_spec(psi, drop(pi, a as nat))
            && (mltl_eval_spec(phi, drop(pi, a as nat))
                || mltl_eval_spec(Mltl::Release(Box::new(phi), (a + 1) as usize, b, Box::new(psi)), pi))),
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
    lemma_complen_bound(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi)));
}

pub proof fn mltl_eval_unchecked_future_interval<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        mltl_eval_unchecked_spec(Mltl::Future(a, b, Box::new(phi)), pi)
            == exists|i: nat| a <= i && i <= b && mltl_eval_spec(phi, #[trigger] drop(pi, i)),
    decreases b - a,
{
    if a < b {
        mltl_eval_unchecked_future_interval(pi, (a + 1) as usize, b, phi);
        if exists|i: nat| a <= i && i <= b && mltl_eval_spec(phi, #[trigger] drop(pi, i)) {
            let i = choose|i: nat| a <= i && i <= b && mltl_eval_spec(phi, #[trigger] drop(pi, i));
            if i > a { assert(mltl_eval_spec(phi, drop(pi, i))); }
        }
    } else {
        if exists|i: nat| a <= i && i <= b && mltl_eval_spec(phi, #[trigger] drop(pi, i)) {
            let i = choose|i: nat| a <= i && i <= b && mltl_eval_spec(phi, #[trigger] drop(pi, i));
            assert(i == a);
        }
    }
}

pub proof fn bounded_forall_unroll(p: spec_fn(nat) -> bool, a: nat, b: nat)
    requires
        a < b,
    ensures
        (forall|i: nat| a <= i && i <= b ==> #[trigger] p(i))
            == (p(a) && forall|i: nat| a + 1 <= i && i <= b ==> #[trigger] p(i)),
{
    if p(a) && forall|i: nat| a + 1 <= i && i <= b ==> #[trigger] p(i) {
        assert forall|i: nat| a <= i && i <= b implies #[trigger] p(i) by {
            if i > a {}
        }
    }
}

pub proof fn mltl_eval_unchecked_global_interval<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        a <= b,
    ensures
        mltl_eval_unchecked_spec(Mltl::Global(a, b, Box::new(phi)), pi)
            == forall|i: nat| a <= i && i <= b ==> mltl_eval_spec(phi, #[trigger] drop(pi, i)),
    decreases b - a,
{
    if a < b {
        mltl_eval_unchecked_global_interval(pi, (a + 1) as usize, b, phi);
        if mltl_eval_spec(phi, drop(pi, a as nat))
            && forall|i: nat| a + 1 <= i && i <= b ==> mltl_eval_spec(phi, #[trigger] drop(pi, i)) {
            assert forall|i: nat| a <= i && i <= b implies mltl_eval_spec(phi, #[trigger] drop(pi, i)) by {
                if i > a {}
            }
        }
    } else {
        if mltl_eval_spec(phi, drop(pi, a as nat)) {
            assert forall|i: nat| a <= i && i <= b implies mltl_eval_spec(phi, #[trigger] drop(pi, i)) by {
                assert(i == a);
            }
        }
    }
}

pub proof fn bounded_until_unroll(q: spec_fn(nat) -> bool, p: spec_fn(nat) -> bool, a: nat, b: nat)
    requires
        a < b,
    ensures
        (exists|i: nat| a <= i && i <= b && #[trigger] q(i) && (forall|j: nat| a <= j && j < i ==> #[trigger] p(j)))
            == (q(a) || (p(a) && exists|i: nat| a + 1 <= i && i <= b && #[trigger] q(i)
                && (forall|j: nat| a + 1 <= j && j < i ==> #[trigger] p(j)))),
{
    if exists|i: nat| a <= i && i <= b && #[trigger] q(i) && (forall|j: nat| a <= j && j < i ==> #[trigger] p(j)) {
        let i = choose|i: nat| a <= i && i <= b && #[trigger] q(i) && (forall|j: nat| a <= j && j < i ==> #[trigger] p(j));
        if i > a {
            assert(p(a));
            assert(q(i));
        }
    }
    if q(a) {
        assert(forall|j: nat| a <= j && j < a ==> #[trigger] p(j));
    }
    if p(a) && exists|i: nat| a + 1 <= i && i <= b && #[trigger] q(i) && (forall|j: nat| a + 1 <= j && j < i ==> #[trigger] p(j)) {
        let i = choose|i: nat| a + 1 <= i && i <= b && #[trigger] q(i) && (forall|j: nat| a + 1 <= j && j < i ==> #[trigger] p(j));
        assert forall|j: nat| a <= j && j < i implies #[trigger] p(j) by {
            if j > a {}
        }
        assert(q(i));
    }
}

pub proof fn mltl_eval_unchecked_until_interval<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a <= b,
    ensures
        mltl_eval_unchecked_spec(Mltl::Until(Box::new(phi), a, b, Box::new(psi)), pi)
            == exists|i: nat| a <= i && i <= b && mltl_eval_spec(psi, #[trigger] drop(pi, i))
                && forall|j: nat| a <= j && j < i ==> mltl_eval_spec(phi, #[trigger] drop(pi, j)),
    decreases b - a,
{
    let q = |i: nat| mltl_eval_spec(psi, drop(pi, i));
    let p = |j: nat| mltl_eval_spec(phi, drop(pi, j));
    let lhs = exists|i: nat| a <= i && i <= b && mltl_eval_spec(psi, #[trigger] drop(pi, i))
        && forall|j: nat| a <= j && j < i ==> mltl_eval_spec(phi, #[trigger] drop(pi, j));
    if a < b {
        mltl_eval_unchecked_until_interval(pi, (a + 1) as usize, b, phi, psi);
        let rest = exists|i: nat| a + 1 <= i && i <= b && mltl_eval_spec(psi, #[trigger] drop(pi, i))
            && forall|j: nat| a + 1 <= j && j < i ==> mltl_eval_spec(phi, #[trigger] drop(pi, j));
        if lhs {
            let i = choose|i: nat| a <= i && i <= b && mltl_eval_spec(psi, #[trigger] drop(pi, i))
                && forall|j: nat| a <= j && j < i ==> mltl_eval_spec(phi, #[trigger] drop(pi, j));
            if i > a {
                assert(mltl_eval_spec(phi, drop(pi, a as nat)));
                assert(forall|j: nat| a + 1 <= j && j < i ==> mltl_eval_spec(phi, #[trigger] drop(pi, j)));
                assert(rest);
            }
        }
        if mltl_eval_spec(psi, drop(pi, a as nat)) {
            assert(forall|j: nat| a <= j && j < a ==> mltl_eval_spec(phi, #[trigger] drop(pi, j)));
            assert(lhs);
        }
        if mltl_eval_spec(phi, drop(pi, a as nat)) && rest {
            let i = choose|i: nat| a + 1 <= i && i <= b && mltl_eval_spec(psi, #[trigger] drop(pi, i))
                && forall|j: nat| a + 1 <= j && j < i ==> mltl_eval_spec(phi, #[trigger] drop(pi, j));
            assert forall|j: nat| a <= j && j < i implies mltl_eval_spec(phi, #[trigger] drop(pi, j)) by {
                if j > a {}
            }
            assert(lhs);
        }
    } else {
        if mltl_eval_spec(psi, drop(pi, a as nat)) {
            assert(forall|j: nat| a <= j && j < a ==> mltl_eval_spec(phi, #[trigger] drop(pi, j)));
        }
    }
}

pub proof fn mltl_eval_unchecked_release_dual<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        a <= b,
    ensures
        mltl_eval_unchecked_spec(Mltl::Release(Box::new(phi), a, b, Box::new(psi)), pi)
            == !mltl_eval_unchecked_spec(
                Mltl::Until(Box::new(Mltl::Not(Box::new(phi))), a, b, Box::new(Mltl::Not(Box::new(psi)))), pi),
    decreases b - a,
{
    reveal_with_fuel(mltl_eval_spec, 2);
    reveal_with_fuel(mltl_eval_unchecked_spec, 2);
    if a < b {
        mltl_eval_unchecked_release_dual(pi, (a + 1) as usize, b, phi, psi);
    }
}

/// IH shape used by the `mltl_eval_correct` case lemmas.
pub open spec fn eval_agrees_on_suffixes<A>(pi: Seq<Set<A>>, phi: Mltl<A>) -> bool {
    forall|i: nat| mltl_eval_spec(phi, #[trigger] drop(pi, i)) == semantics_mltl(drop(pi, i), phi)
}

proof fn mltl_eval_correct_future<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        eval_agrees_on_suffixes(pi, phi),
    ensures
        mltl_eval_spec(Mltl::Future(a, b, Box::new(phi)), pi) == semantics_mltl(pi, Mltl::Future(a, b, Box::new(phi))),
{
    if a <= b && a < pi.len() {
        mltl_eval_unchecked_future_interval(pi, a, b, phi);
    }
}

proof fn mltl_eval_correct_global<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>)
    requires
        eval_agrees_on_suffixes(pi, phi),
    ensures
        mltl_eval_spec(Mltl::Global(a, b, Box::new(phi)), pi) == semantics_mltl(pi, Mltl::Global(a, b, Box::new(phi))),
{
    if a <= b && a < pi.len() {
        mltl_eval_unchecked_global_interval(pi, a, b, phi);
    }
}

proof fn mltl_eval_correct_until<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        eval_agrees_on_suffixes(pi, phi),
        eval_agrees_on_suffixes(pi, psi),
    ensures
        mltl_eval_spec(Mltl::Until(Box::new(phi), a, b, Box::new(psi)), pi)
            == semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi))),
{
    if a <= b && a < pi.len() {
        mltl_eval_unchecked_until_interval(pi, a, b, phi, psi);
    }
}

proof fn mltl_eval_correct_release<A>(pi: Seq<Set<A>>, a: usize, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        eval_agrees_on_suffixes(pi, Mltl::Not(Box::new(phi))),
        eval_agrees_on_suffixes(pi, Mltl::Not(Box::new(psi))),
    ensures
        mltl_eval_spec(Mltl::Release(Box::new(phi), a, b, Box::new(psi)), pi)
            == semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))),
{
    if a <= b && a < pi.len() {
        let nphi = Mltl::Not(Box::new(phi));
        let npsi = Mltl::Not(Box::new(psi));
        mltl_eval_unchecked_release_dual(pi, a, b, phi, psi);
        mltl_eval_correct_until(pi, a, b, nphi, npsi);
        release_until_dual(a, b, phi, psi);
        let u = Mltl::Until(Box::new(nphi), a, b, Box::new(npsi));
        assert(mltl_eval_spec(u, pi) == mltl_eval_unchecked_spec(u, pi));
        assert(semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))) == !semantics_mltl(pi, u));
    }
}

/// `mltl_eval φ π = semantics_mltl π φ`
pub proof fn mltl_eval_correct<A>(f: Mltl<A>, pi: Seq<Set<A>>)
    ensures
        mltl_eval_spec(f, pi) == semantics_mltl(pi, f),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(phi) => mltl_eval_correct(*phi, pi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            mltl_eval_correct(*phi, pi);
            mltl_eval_correct(*psi, pi);
        },
        Mltl::Future(a, b, phi) => {
            assert forall|i: nat| mltl_eval_spec(*phi, #[trigger] drop(pi, i)) == semantics_mltl(drop(pi, i), *phi) by {
                mltl_eval_correct(*phi, drop(pi, i));
            }
            mltl_eval_correct_future(pi, a, b, *phi);
        },
        Mltl::Global(a, b, phi) => {
            assert forall|i: nat| mltl_eval_spec(*phi, #[trigger] drop(pi, i)) == semantics_mltl(drop(pi, i), *phi) by {
                mltl_eval_correct(*phi, drop(pi, i));
            }
            mltl_eval_correct_global(pi, a, b, *phi);
        },
        Mltl::Until(phi, a, b, psi) => {
            assert forall|i: nat| mltl_eval_spec(*phi, #[trigger] drop(pi, i)) == semantics_mltl(drop(pi, i), *phi) by {
                mltl_eval_correct(*phi, drop(pi, i));
            }
            assert forall|i: nat| mltl_eval_spec(*psi, #[trigger] drop(pi, i)) == semantics_mltl(drop(pi, i), *psi) by {
                mltl_eval_correct(*psi, drop(pi, i));
            }
            mltl_eval_correct_until(pi, a, b, *phi, *psi);
        },
        Mltl::Release(phi, a, b, psi) => {
            assert forall|i: nat| mltl_eval_spec(Mltl::Not(phi), #[trigger] drop(pi, i))
                == semantics_mltl(drop(pi, i), Mltl::Not(phi)) by {
                mltl_eval_correct(*phi, drop(pi, i));
            }
            assert forall|i: nat| mltl_eval_spec(Mltl::Not(psi), #[trigger] drop(pi, i))
                == semantics_mltl(drop(pi, i), Mltl::Not(psi)) by {
                mltl_eval_correct(*psi, drop(pi, i));
            }
            mltl_eval_correct_release(pi, a, b, *phi, *psi);
        },
    }
}

// ---------------------------------------------------------------------------
// MLTL satisfiability
// ---------------------------------------------------------------------------

/// `MLTL_SAT φ = (∃π. π ⊨_m φ)` (finite-state traces, D16)
pub open spec fn mltl_sat<A>(phi: Mltl<A>) -> bool {
    exists|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, phi)
}

/// `MLTL_SAT_LEN φ n = (∃π. length π ≥ n ∧ π ⊨_m φ)`
pub open spec fn mltl_sat_len<A>(phi: Mltl<A>, n: nat) -> bool {
    exists|pi: Seq<Set<A>>| pi.len() >= n && #[trigger] semantics_mltl(pi, phi)
}

pub proof fn unsat_is_false<A>(phi: Mltl<A>)
    ensures
        !mltl_sat(phi) == semantic_equiv(phi, Mltl::False),
{
    if !mltl_sat(phi) {
        assert forall|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, phi) == semantics_mltl(pi, Mltl::<A>::False) by {
            if semantics_mltl(pi, phi) { assert(mltl_sat(phi)); }
        }
    }
    if mltl_sat(phi) {
        let pi = choose|pi: Seq<Set<A>>| #[trigger] semantics_mltl(pi, phi);
        assert(semantics_mltl(pi, phi) != semantics_mltl(pi, Mltl::<A>::False));
    }
}

// ---------------------------------------------------------------------------
// MLTL atoms
// ---------------------------------------------------------------------------

/// `atomic_props φ`: atoms of `φ` (same as `mltl.rs : atoms_mltl`, which
/// mirrors the datatype-generated `atoms_mltl`; see `atomic_props_eq_atoms_mltl`).
pub open spec fn atomic_props<A>(f: Mltl<A>) -> Set<A>
    decreases f,
{
    match f {
        Mltl::True | Mltl::False => Set::empty(),
        Mltl::Prop(p) => Set::empty().insert(p),
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => atomic_props(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) =>
            atomic_props(*phi).union(atomic_props(*psi)),
    }
}

pub proof fn atomic_props_eq_atoms_mltl<A>(f: Mltl<A>)
    ensures
        atomic_props(f) == atoms_mltl(f),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => atomic_props_eq_atoms_mltl(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) => {
            atomic_props_eq_atoms_mltl(*phi);
            atomic_props_eq_atoms_mltl(*psi);
        },
    }
}

/// `atomics_agree π π' AP t`: both traces have length ≥ t and agree on the
/// atoms in `AP` at every time before `t`.
pub open spec fn atomics_agree<A>(pi: Seq<Set<A>>, pi2: Seq<Set<A>>, ap: Set<A>, t: nat) -> bool {
    pi.len() >= t && pi2.len() >= t
        && forall|i: nat, p: A| i < t && ap.contains(p) ==> (#[trigger] pi[i as int].contains(p) <==> pi2[i as int].contains(p))
}

/// Helper: agreement restricts to a subset of atoms, a shorter horizon, and suffixes.
proof fn lemma_atomics_agree_drop<A>(pi: Seq<Set<A>>, pi2: Seq<Set<A>>, ap: Set<A>, ap2: Set<A>, t: nat, i: nat, t2: nat)
    requires
        atomics_agree(pi, pi2, ap, t),
        ap2.subset_of(ap),
        i + t2 <= t,
    ensures
        atomics_agree(drop(pi, i), drop(pi2, i), ap2, t2),
{
    assert forall|j: nat, p: A| j < t2 && ap2.contains(p) implies
        (#[trigger] drop(pi, i)[j as int].contains(p) <==> drop(pi2, i)[j as int].contains(p)) by {
        assert(drop(pi, i)[j as int] == pi[(i + j) as int]);
        assert(drop(pi2, i)[j as int] == pi2[(i + j) as int]);
        assert(pi[(i + j) as int].contains(p) <==> pi2[(i + j) as int].contains(p));
    }
}

/// `atomics_agree π π' (atomic_props φ) (complen_mltl φ) ⟹ intervals_welldef φ ⟹ (π ⊨ φ) = (π' ⊨ φ)`
pub proof fn atomics_agree_semantics<A>(pi: Seq<Set<A>>, pi2: Seq<Set<A>>, f: Mltl<A>)
    requires
        atomics_agree(pi, pi2, atomic_props(f), complen_mltl(f)),
        intervals_welldef(f),
    ensures
        semantics_mltl(pi, f) == semantics_mltl(pi2, f),
    decreases f,
{
    let t = complen_mltl(f);
    match f {
        Mltl::True | Mltl::False => {},
        Mltl::Prop(p) => {
            assert(pi[0].contains(p) <==> pi2[0].contains(p));
        },
        Mltl::Not(phi) => atomics_agree_semantics(pi, pi2, *phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => {
            lemma_atomics_agree_drop(pi, pi2, atomic_props(f), atomic_props(*phi), t, 0, complen_mltl(*phi));
            lemma_atomics_agree_drop(pi, pi2, atomic_props(f), atomic_props(*psi), t, 0, complen_mltl(*psi));
            lemma_drop_zero(pi);
            lemma_drop_zero(pi2);
            atomics_agree_semantics(pi, pi2, *phi);
            atomics_agree_semantics(pi, pi2, *psi);
        },
        Mltl::Future(a, b, phi) | Mltl::Global(a, b, phi) => {
            complen_geq_one(*phi);
            assert(pi.len() > b && pi2.len() > b);
            assert forall|i: nat| #![trigger drop(pi, i)] #![trigger drop(pi2, i)] i <= b implies
                semantics_mltl(drop(pi, i), *phi) == semantics_mltl(drop(pi2, i), *phi) by {
                lemma_atomics_agree_drop(pi, pi2, atomic_props(f), atomic_props(*phi), t, i, complen_mltl(*phi));
                atomics_agree_semantics(drop(pi, i), drop(pi2, i), *phi);
            }
            assert(semantics_mltl(pi, f) == semantics_mltl(pi2, f));
        },
        Mltl::Until(phi, a, b, psi) | Mltl::Release(phi, a, b, psi) => {
            complen_geq_one(*phi);
            complen_geq_one(*psi);
            assert(pi.len() > b && pi2.len() > b);
            assert forall|i: nat| #![trigger drop(pi, i)] #![trigger drop(pi2, i)] i <= b implies
                semantics_mltl(drop(pi, i), *psi) == semantics_mltl(drop(pi2, i), *psi) by {
                lemma_atomics_agree_drop(pi, pi2, atomic_props(f), atomic_props(*psi), t, i, complen_mltl(*psi));
                atomics_agree_semantics(drop(pi, i), drop(pi2, i), *psi);
            }
            assert forall|j: nat| #![trigger drop(pi, j)] #![trigger drop(pi2, j)] j < b implies
                semantics_mltl(drop(pi, j), *phi) == semantics_mltl(drop(pi2, j), *phi) by {
                lemma_atomics_agree_drop(pi, pi2, atomic_props(f), atomic_props(*phi), t, j, complen_mltl(*phi));
                atomics_agree_semantics(drop(pi, j), drop(pi2, j), *phi);
            }
            assert(semantics_mltl(pi, f) == semantics_mltl(pi2, f));
        },
    }
}

// ---------------------------------------------------------------------------
// Executable normal-form conversions (D20, D20): exec `convert_nnf` /
// `convert_bnf` return exactly the spec result, so every lemma about
// `convert_nnf_spec` / `convert_bnf_spec` applies to their output.
// ---------------------------------------------------------------------------

/// Executable `convert_nnf`: `result == convert_nnf_spec(*f)`.
pub fn convert_nnf(f: &Mltl<usize>) -> (r: Mltl<usize>)
    ensures
        r == convert_nnf_spec(*f),
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(p) => Mltl::Prop(*p),
        Mltl::Not(g) => convert_nnf_not(g),
        Mltl::And(phi, psi) => Mltl::And(Box::new(convert_nnf(phi)), Box::new(convert_nnf(psi))),
        Mltl::Or(phi, psi) => Mltl::Or(Box::new(convert_nnf(phi)), Box::new(convert_nnf(psi))),
        Mltl::Future(a, b, phi) => Mltl::Future(*a, *b, Box::new(convert_nnf(phi))),
        Mltl::Global(a, b, phi) => Mltl::Global(*a, *b, Box::new(convert_nnf(phi))),
        Mltl::Until(phi, a, b, psi) => Mltl::Until(Box::new(convert_nnf(phi)), *a, *b, Box::new(convert_nnf(psi))),
        Mltl::Release(phi, a, b, psi) =>
            Mltl::Release(Box::new(convert_nnf(phi)), *a, *b, Box::new(convert_nnf(psi))),
    }
}

/// `convert_nnf (Not g)` without building `Not g` first (avoids cloning `g`).
fn convert_nnf_not(g: &Mltl<usize>) -> (r: Mltl<usize>)
    ensures
        r == convert_nnf_spec(Mltl::Not(Box::new(*g))),
    decreases g,
{
    match g {
        Mltl::True => Mltl::False,
        Mltl::False => Mltl::True,
        Mltl::Prop(p) => Mltl::Not(Box::new(Mltl::Prop(*p))),
        Mltl::Not(phi) => convert_nnf(phi),
        Mltl::And(phi, psi) => Mltl::Or(Box::new(convert_nnf_not(phi)), Box::new(convert_nnf_not(psi))),
        Mltl::Or(phi, psi) => Mltl::And(Box::new(convert_nnf_not(phi)), Box::new(convert_nnf_not(psi))),
        Mltl::Future(a, b, phi) => Mltl::Global(*a, *b, Box::new(convert_nnf_not(phi))),
        Mltl::Global(a, b, phi) => Mltl::Future(*a, *b, Box::new(convert_nnf_not(phi))),
        Mltl::Until(phi, a, b, psi) =>
            Mltl::Release(Box::new(convert_nnf_not(phi)), *a, *b, Box::new(convert_nnf_not(psi))),
        Mltl::Release(phi, a, b, psi) =>
            Mltl::Until(Box::new(convert_nnf_not(phi)), *a, *b, Box::new(convert_nnf_not(psi))),
    }
}

/// Executable `convert_bnf`: `result == convert_bnf_spec(*f)`.
pub fn convert_bnf(f: &Mltl<usize>) -> (r: Mltl<usize>)
    ensures
        r == convert_bnf_spec(*f),
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::Not(Box::new(Mltl::True)),
        Mltl::Prop(p) => Mltl::Prop(*p),
        Mltl::Not(phi) => Mltl::Not(Box::new(convert_bnf(phi))),
        Mltl::And(phi, psi) => Mltl::And(Box::new(convert_bnf(phi)), Box::new(convert_bnf(psi))),
        Mltl::Or(phi, psi) => Mltl::Not(Box::new(Mltl::And(
            Box::new(Mltl::Not(Box::new(convert_bnf(phi)))),
            Box::new(Mltl::Not(Box::new(convert_bnf(psi)))),
        ))),
        Mltl::Future(a, b, phi) => Mltl::Until(Box::new(Mltl::True), *a, *b, Box::new(convert_bnf(phi))),
        Mltl::Global(a, b, phi) => Mltl::Not(Box::new(Mltl::Until(
            Box::new(Mltl::True), *a, *b, Box::new(Mltl::Not(Box::new(convert_bnf(phi)))),
        ))),
        Mltl::Until(phi, a, b, psi) => Mltl::Until(Box::new(convert_bnf(phi)), *a, *b, Box::new(convert_bnf(psi))),
        Mltl::Release(phi, a, b, psi) => Mltl::Not(Box::new(Mltl::Until(
            Box::new(Mltl::Not(Box::new(convert_bnf(phi)))), *a, *b,
            Box::new(Mltl::Not(Box::new(convert_bnf(psi)))),
        ))),
    }
}

} // verus!
