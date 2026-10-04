//! Formula progression: Theorems 2 and 3 and their corollaries.
//!
//! Mirrors `MLTL_Formula_Progression.thy`, subsection Proofs.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithm::*;

verus! {

// ---------------------------------------------------------------------------
// Theorem 2
// ---------------------------------------------------------------------------

/// Helper (not in Isabelle): one-step unrolling of `F[0,b]` when the trace
/// has a second state. Unlike `future_unrolling_mltl_semantics` it needs
/// no computation-length assumption.
proof fn future_step0<A>(pi: Seq<Set<A>>, b: usize, g: Mltl<A>)
    requires
        0 < b,
        pi.len() > 1,
    ensures
        semantics_mltl(pi, Mltl::Future(0, b, Box::new(g)))
            == (semantics_mltl(pi, g) || semantics_mltl(drop(pi, 1), Mltl::Future(0, (b - 1) as usize, Box::new(g)))),
{
    lemma_drop_zero(pi);
    semantic_shift_f(pi, 1, b, g);
    if semantics_mltl(pi, Mltl::Future(0, b, Box::new(g))) {
        let i = choose|i: nat| (0 <= i && i <= b) && semantics_mltl(drop(pi, i), g);
        if i > 0 {
            assert(semantics_mltl(pi, Mltl::Future(1, b, Box::new(g))));
        }
    }
    if semantics_mltl(pi, g) {
        assert(semantics_mltl(drop(pi, 0), g));
    }
    if semantics_mltl(pi, Mltl::Future(1, b, Box::new(g))) {
        let i = choose|i: nat| (1 <= i && i <= b) && semantics_mltl(drop(pi, i), g);
        assert(semantics_mltl(drop(pi, i), g));
    }
}

/// Helper (not in Isabelle): one-step unrolling of `φ U[0,b] ψ` when the
/// trace has a second state.
proof fn until_step0<A>(pi: Seq<Set<A>>, b: usize, phi: Mltl<A>, psi: Mltl<A>)
    requires
        0 < b,
        pi.len() > 1,
    ensures
        semantics_mltl(pi, Mltl::Until(Box::new(phi), 0, b, Box::new(psi))) == (semantics_mltl(pi, psi)
            || (semantics_mltl(pi, phi)
                && semantics_mltl(drop(pi, 1), Mltl::Until(Box::new(phi), 0, (b - 1) as usize, Box::new(psi))))),
{
    lemma_drop_zero(pi);
    semantic_shift_u(pi, 1, b, phi, psi);
    let lhs = semantics_mltl(pi, Mltl::Until(Box::new(phi), 0, b, Box::new(psi)));
    let rest = semantics_mltl(pi, Mltl::Until(Box::new(phi), 1, b, Box::new(psi)));
    if lhs {
        let i = choose|i: nat| (0 <= i && i <= b) && (semantics_mltl(drop(pi, i), psi)
            && forall|j: nat| (j >= 0 && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        if i > 0 {
            assert(semantics_mltl(drop(pi, 0), phi));
            assert(forall|j: nat| (j >= 1 && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
            assert(rest);
        }
    }
    if semantics_mltl(drop(pi, 0), psi) {
        assert(forall|j: nat| (j >= 0 && j < 0) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        assert(lhs);
    }
    if semantics_mltl(drop(pi, 0), phi) && rest {
        let i = choose|i: nat| (1 <= i && i <= b) && (semantics_mltl(drop(pi, i), psi)
            && forall|j: nat| (j >= 1 && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        assert(forall|j: nat| (j >= 0 && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        assert(lhs);
    }
}

/// Future case of `satisfiability_preservation_len1`, given the hypothesis
/// for the operand.
proof fn satisfiability_preservation_len1_future<A>(pi: Seq<Set<A>>, a: usize, b: usize, g: Mltl<A>)
    requires
        1 < pi.len(),
        a <= b,
        semantics_mltl(drop(pi, 1), formula_progression_len1_spec(g, pi[0])) == semantics_mltl(pi, g),
    ensures
        semantics_mltl(drop(pi, 1), formula_progression_len1_spec(Mltl::Future(a, b, Box::new(g)), pi[0]))
            == semantics_mltl(pi, Mltl::Future(a, b, Box::new(g))),
{
    if 0 < a {
        semantic_shift_f(pi, a, b, g);
        semantic_shift_f(drop(pi, 1), (a - 1) as usize, (b - 1) as usize, g);
        lemma_drop_drop(pi, 1, (a - 1) as nat);
    } else if a < b {
        future_step0(pi, b, g);
    } else {
        future_base_mltl_semantics(pi, 0, g);
        lemma_drop_zero(pi);
    }
}

/// Until case of `satisfiability_preservation_len1`, given the hypotheses
/// for the operands.
proof fn satisfiability_preservation_len1_until<A>(pi: Seq<Set<A>>, a: usize, b: usize, f1: Mltl<A>, f2: Mltl<A>)
    requires
        1 < pi.len(),
        a <= b,
        semantics_mltl(drop(pi, 1), formula_progression_len1_spec(f1, pi[0])) == semantics_mltl(pi, f1),
        semantics_mltl(drop(pi, 1), formula_progression_len1_spec(f2, pi[0])) == semantics_mltl(pi, f2),
    ensures
        semantics_mltl(drop(pi, 1), formula_progression_len1_spec(Mltl::Until(Box::new(f1), a, b, Box::new(f2)), pi[0]))
            == semantics_mltl(pi, Mltl::Until(Box::new(f1), a, b, Box::new(f2))),
{
    if 0 < a {
        semantic_shift_u(pi, a, b, f1, f2);
        semantic_shift_u(drop(pi, 1), (a - 1) as usize, (b - 1) as usize, f1, f2);
        lemma_drop_drop(pi, 1, (a - 1) as nat);
    } else if a < b {
        reveal_with_fuel(semantics_mltl, 2);
        until_step0(pi, b, f1, f2);
    } else {
        until_base_mltl_semantics(pi, 0, f1, f2);
        lemma_drop_zero(pi);
    }
}

/// Base case for Theorem 2, `satisfiability_preservation_len1`.
///
/// Isabelle inducts on `φ`; here the measure is `weight_operators`, so the
/// Release and Global cases apply the hypothesis to the rewritten formula
/// that `formula_progression_len1` recurses on, then use the dualities.
pub proof fn satisfiability_preservation_len1<A>(pi: Seq<Set<A>>, phi: Mltl<A>)
    requires
        1 < pi.len(),
        intervals_welldef(phi),
    ensures
        semantics_mltl(drop(pi, 1), formula_progression_len1_spec(phi, pi[0])) == semantics_mltl(pi, phi),
    decreases weight_operators(phi),
{
    match phi {
        Mltl::True => {},
        Mltl::False => {},
        Mltl::Prop(_) => {},
        Mltl::Not(g) => satisfiability_preservation_len1(pi, *g),
        Mltl::And(f1, f2) => {
            satisfiability_preservation_len1(pi, *f1);
            satisfiability_preservation_len1(pi, *f2);
        },
        Mltl::Or(f1, f2) => {
            satisfiability_preservation_len1(pi, *f1);
            satisfiability_preservation_len1(pi, *f2);
        },
        Mltl::Future(a, b, g) => {
            satisfiability_preservation_len1(pi, *g);
            satisfiability_preservation_len1_future(pi, a, b, *g);
        },
        Mltl::Until(f1, a, b, f2) => {
            satisfiability_preservation_len1(pi, *f1);
            satisfiability_preservation_len1(pi, *f2);
            satisfiability_preservation_len1_until(pi, a, b, *f1, *f2);
        },
        Mltl::Global(a, b, g) => {
            let fu = Mltl::Future(a, b, Box::new(Mltl::Not(g)));
            assert(weight_operators(fu) < weight_operators(phi) && intervals_welldef(fu)) by {
                reveal_with_fuel(weight_operators, 2);
                reveal_with_fuel(intervals_welldef, 2);
            }
            satisfiability_preservation_len1(pi, fu);
            globally_future_dual(a, b, *g);
            assert(semantics_mltl(pi, phi) == semantics_mltl(pi, Mltl::Not(Box::new(fu))));
        },
        Mltl::Release(f1, a, b, f2) => {
            let u = Mltl::Until(Box::new(Mltl::Not(f1)), a, b, Box::new(Mltl::Not(f2)));
            assert(weight_operators(u) < weight_operators(phi) && intervals_welldef(u)) by {
                reveal_with_fuel(weight_operators, 2);
                reveal_with_fuel(intervals_welldef, 2);
            }
            satisfiability_preservation_len1(pi, u);
            release_until_dual(a, b, *f1, *f2);
            assert(semantics_mltl(pi, phi) == semantics_mltl(pi, Mltl::Not(Box::new(u))));
        },
    }
}

/// Theorem 2, `satisfiability_preservation`.
pub proof fn satisfiability_preservation<A>(pi: Seq<Set<A>>, phi: Mltl<A>, k: nat)
    requires
        k >= 1,
        k < pi.len(),
        intervals_welldef(phi),
    ensures
        semantics_mltl(drop(pi, k), formula_progression_spec(phi, take(pi, k))) == semantics_mltl(pi, phi),
    decreases k,
{
    if k == 1 {
        satisfiability_preservation_len1(pi, phi);
        assert(take(pi, 1).len() == 1 && take(pi, 1)[0] == pi[0]);
    } else {
        let km = (k - 1) as nat;
        let g = formula_progression_spec(phi, take(pi, km));
        let rho = drop(pi, km);
        satisfiability_preservation(pi, phi, km);
        formula_progression_well_definedness_preserved(phi, take(pi, km));
        lemma_drop_len(pi, km);
        satisfiability_preservation_len1(rho, g);
        lemma_drop_drop(pi, km, 1);
        assert(rho[0] == pi[km as int]);
        formula_progression_snoc(phi, take(pi, km), pi[km as int]);
        assert(take(pi, km).push(pi[km as int]) =~= take(pi, k));
    }
}

/// Helper (not in Isabelle): Theorem 2 read the other way round. On a
/// non-empty continuation `ρ`, the progressed formula holds iff `π @ ρ`
/// satisfies `φ`.
pub proof fn formula_progression_semantics<A>(phi: Mltl<A>, pi: Seq<Set<A>>, rho: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        rho.len() != 0,
    ensures
        semantics_mltl(rho, formula_progression_spec(phi, pi)) == semantics_mltl(pi + rho, phi),
{
    if pi.len() == 0 {
        assert(pi + rho =~= rho);
    } else {
        let k = pi.len();
        satisfiability_preservation(pi + rho, phi, k);
        assert(take(pi + rho, k) =~= pi);
        assert(drop(pi + rho, k) =~= rho);
    }
}

/// `theorem2_cexa`: without `k < length π`, Theorem 2 fails —
/// progressing `G[0,3] p` over `[{1}]` gives a formula true on `[]` ...
pub proof fn theorem2_cexa()
    ensures
        semantics_mltl(
            drop(seq![Set::empty().insert(1nat)], 1),
            formula_progression_spec(
                Mltl::Global(0, 3, Box::new(Mltl::Prop(1nat))),
                take(seq![Set::empty().insert(1nat)], 1),
            ),
        ),
{
    let pi = seq![Set::empty().insert(1nat)];
    let p = Mltl::Prop(1nat);
    let g = Mltl::Global(0, 3, Box::new(p));
    let np = Mltl::Not(Box::new(p));
    let r = Mltl::Not(Box::new(Mltl::Or(
        Box::new(Mltl::Not(Box::new(Mltl::True))),
        Box::new(Mltl::Future(0, 2, Box::new(np))),
    )));
    assert(take(pi, 1) =~= pi);
    assert(drop(pi, 1) =~= Seq::<Set<nat>>::empty());
    assert(formula_progression_spec(g, pi) == formula_progression_len1_spec(g, pi[0]));
    assert(formula_progression_len1_spec(np, pi[0]) == Mltl::Not(Box::new(Mltl::True))) by {
        reveal_with_fuel(formula_progression_len1_spec, 2);
    }
    assert(formula_progression_len1_spec(g, pi[0]) == r) by {
        reveal_with_fuel(formula_progression_len1_spec, 3);
    }
    assert(semantics_mltl(Seq::<Set<nat>>::empty(), r)) by {
        reveal_with_fuel(semantics_mltl, 4);
    }
}

/// `theorem2_cexb`: ... while `[{1}]` does not satisfy `G[0,1] p`.
pub proof fn theorem2_cexb()
    ensures
        !semantics_mltl(seq![Set::empty().insert(1nat)], Mltl::Global(0, 1, Box::new(Mltl::Prop(1nat)))),
{
    let pi = seq![Set::empty().insert(1nat)];
    assert(drop(pi, 1) =~= Seq::<Set<nat>>::empty());
    assert(!semantics_mltl(drop(pi, 1), Mltl::Prop(1nat)));
}

// ---------------------------------------------------------------------------
// Theorem 3: properties of computation length
// ---------------------------------------------------------------------------

/// `complen_geq_1` (same as mltl-core's `complen_geq_one`).
pub proof fn complen_geq_1<A>(phi: Mltl<A>)
    ensures
        complen_mltl(phi) >= 1,
{
    complen_geq_one(phi);
}

/// Helper (not in Isabelle; strengthens `complen_bounded_by_1`): progressing
/// a formula of computation length 1 over `s` gives a formula whose truth
/// value is the same on every trace `ρ`, namely whether `[s]` satisfies `φ`.
pub proof fn complen_one_len1_value_at<A>(phi: Mltl<A>, s: Set<A>, rho: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        complen_mltl(phi) == 1,
    ensures
        semantics_mltl(rho, formula_progression_len1_spec(phi, s)) == semantics_mltl(seq![s], phi),
    decreases weight_operators(phi),
{
    let one = seq![s];
    lemma_drop_zero(one);
    match phi {
        Mltl::True => {},
        Mltl::False => {},
        Mltl::Prop(_) => {},
        Mltl::Not(g) => complen_one_len1_value_at(*g, s, rho),
        Mltl::And(f1, f2) => {
            complen_geq_one(*f1);
            complen_geq_one(*f2);
            complen_one_len1_value_at(*f1, s, rho);
            complen_one_len1_value_at(*f2, s, rho);
        },
        Mltl::Or(f1, f2) => {
            complen_geq_one(*f1);
            complen_geq_one(*f2);
            complen_one_len1_value_at(*f1, s, rho);
            complen_one_len1_value_at(*f2, s, rho);
        },
        Mltl::Future(a, b, g) => {
            complen_geq_one(*g);
            complen_one_len1_value_at(*g, s, rho);
            future_base_mltl_semantics(one, 0, *g);
        },
        Mltl::Until(f1, a, b, f2) => {
            complen_geq_one(*f2);
            complen_one_len1_value_at(*f2, s, rho);
            until_base_mltl_semantics(one, 0, *f1, *f2);
        },
        Mltl::Global(a, b, g) => {
            let fu = Mltl::Future(a, b, Box::new(Mltl::Not(g)));
            assert(weight_operators(fu) < weight_operators(phi) && intervals_welldef(fu)
                && complen_mltl(fu) == 1) by {
                reveal_with_fuel(weight_operators, 2);
                reveal_with_fuel(intervals_welldef, 2);
                reveal_with_fuel(complen_mltl, 2);
            }
            complen_one_len1_value_at(fu, s, rho);
            globally_future_dual(a, b, *g);
            assert(semantics_mltl(one, phi) == semantics_mltl(one, Mltl::Not(Box::new(fu))));
        },
        Mltl::Release(f1, a, b, f2) => {
            let u = Mltl::Until(Box::new(Mltl::Not(f1)), a, b, Box::new(Mltl::Not(f2)));
            assert(weight_operators(u) < weight_operators(phi) && intervals_welldef(u)
                && complen_mltl(u) == 1) by {
                reveal_with_fuel(weight_operators, 2);
                reveal_with_fuel(intervals_welldef, 2);
                reveal_with_fuel(complen_mltl, 2);
            }
            complen_one_len1_value_at(u, s, rho);
            release_until_dual(a, b, *f1, *f2);
            assert(semantics_mltl(one, phi) == semantics_mltl(one, Mltl::Not(Box::new(u))));
        },
    }
}

/// `complen_one_len1_value_at` for every trace.
pub proof fn complen_one_len1_value<A>(phi: Mltl<A>, s: Set<A>)
    requires
        intervals_welldef(phi),
        complen_mltl(phi) == 1,
    ensures
        forall|rho: Seq<Set<A>>| #[trigger] semantics_mltl(rho, formula_progression_len1_spec(phi, s))
            == semantics_mltl(seq![s], phi),
{
    assert forall|rho: Seq<Set<A>>| #[trigger] semantics_mltl(rho, formula_progression_len1_spec(phi, s))
        == semantics_mltl(seq![s], phi) by {
        complen_one_len1_value_at(phi, s, rho);
    }
}

/// `complen_bounded_by_1`: with computation length 1, one step of
/// progression gives a formula that is true everywhere or false everywhere.
pub proof fn complen_bounded_by_1<A>(phi: Mltl<A>, s: Set<A>)
    requires
        intervals_welldef(phi),
        1 >= complen_mltl(phi),
    ensures
        (forall|xi: Seq<Set<A>>| #[trigger] semantics_mltl(xi, formula_progression_len1_spec(phi, s)))
            || (forall|xi: Seq<Set<A>>| !#[trigger] semantics_mltl(xi, formula_progression_len1_spec(phi, s))),
{
    complen_geq_one(phi);
    complen_one_len1_value(phi, s);
}

/// `complen_temporal_props`: computation length 1 forces upper bound 0.
pub proof fn complen_temporal_props<A>(a: usize, b: usize, phi: Mltl<A>, phi1: Mltl<A>, phi2: Mltl<A>)
    ensures
        complen_mltl(Mltl::Future(a, b, Box::new(phi))) == 1 ==> b == 0,
        complen_mltl(Mltl::Global(a, b, Box::new(phi))) == 1 ==> b == 0,
        complen_mltl(Mltl::Until(Box::new(phi1), a, b, Box::new(phi2))) == 1 ==> b == 0,
        complen_mltl(Mltl::Release(Box::new(phi1), a, b, Box::new(phi2))) == 1 ==> b == 0,
{
    complen_geq_one(phi);
    complen_geq_one(phi2);
}

/// Helper (not in Isabelle; combines `formula_progression_decreases_complen_base`
/// and `complen_one_implies_one_base`): one step lowers the computation
/// length by one, down to 1.
pub proof fn complen_len1_bound<A>(phi: Mltl<A>, s: Set<A>)
    requires
        intervals_welldef(phi),
    ensures
        complen_mltl(formula_progression_len1_spec(phi, s)) <= max_nat(1, nat_sub(complen_mltl(phi), 1)),
    decreases weight_operators(phi),
{
    match phi {
        Mltl::True => {},
        Mltl::False => {},
        Mltl::Prop(_) => {},
        Mltl::Not(g) => complen_len1_bound(*g, s),
        Mltl::And(f1, f2) => {
            complen_len1_bound(*f1, s);
            complen_len1_bound(*f2, s);
        },
        Mltl::Or(f1, f2) => {
            complen_len1_bound(*f1, s);
            complen_len1_bound(*f2, s);
        },
        Mltl::Future(a, b, g) => {
            complen_geq_one(*g);
            complen_len1_bound(*g, s);
            reveal_with_fuel(complen_mltl, 2);
        },
        Mltl::Until(f1, a, b, f2) => {
            complen_geq_one(*f1);
            complen_geq_one(*f2);
            complen_len1_bound(*f1, s);
            complen_len1_bound(*f2, s);
            reveal_with_fuel(complen_mltl, 3);
        },
        Mltl::Global(a, b, g) => {
            let fu = Mltl::Future(a, b, Box::new(Mltl::Not(g)));
            assert(weight_operators(fu) < weight_operators(phi) && intervals_welldef(fu)
                && complen_mltl(fu) == complen_mltl(phi)) by {
                reveal_with_fuel(weight_operators, 2);
                reveal_with_fuel(intervals_welldef, 2);
                reveal_with_fuel(complen_mltl, 2);
            }
            complen_len1_bound(fu, s);
        },
        Mltl::Release(f1, a, b, f2) => {
            let u = Mltl::Until(Box::new(Mltl::Not(f1)), a, b, Box::new(Mltl::Not(f2)));
            assert(weight_operators(u) < weight_operators(phi) && intervals_welldef(u)
                && complen_mltl(u) == complen_mltl(phi)) by {
                reveal_with_fuel(weight_operators, 2);
                reveal_with_fuel(intervals_welldef, 2);
                reveal_with_fuel(complen_mltl, 2);
            }
            complen_len1_bound(u, s);
        },
    }
}

pub proof fn complen_one_implies_one_base<A>(phi: Mltl<A>, s: Set<A>)
    requires
        intervals_welldef(phi),
        complen_mltl(phi) == 1,
    ensures
        complen_mltl(formula_progression_len1_spec(phi, s)) == 1,
{
    complen_len1_bound(phi, s);
    complen_geq_one(formula_progression_len1_spec(phi, s));
}

/// Helper (not in Isabelle): progressing over `π` lowers the computation
/// length by `length π`, down to 1.
pub proof fn complen_progression_bound<A>(phi: Mltl<A>, tr: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        complen_mltl(formula_progression_spec(phi, tr)) <= max_nat(1, nat_sub(complen_mltl(phi), tr.len())),
    decreases tr.len(),
{
    complen_geq_one(phi);
    if tr.len() > 0 {
        let g = formula_progression_len1_spec(phi, tr[0]);
        complen_len1_bound(phi, tr[0]);
        formula_progression_well_definedness_preserved_len1(phi, tr[0]);
        complen_progression_bound(g, drop(tr, 1));
        lemma_drop_len(tr, 1);
    }
}

pub proof fn complen_one_implies_one<A>(phi: Mltl<A>, tr: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        complen_mltl(phi) == 1,
    ensures
        complen_mltl(formula_progression_spec(phi, tr)) == 1,
{
    complen_progression_bound(phi, tr);
    complen_geq_one(formula_progression_spec(phi, tr));
}

pub proof fn formula_progression_decreases_complen_base<A>(phi: Mltl<A>, s: Set<A>)
    requires
        intervals_welldef(phi),
    ensures
        complen_mltl(phi) == 1
            || complen_mltl(formula_progression_len1_spec(phi, s)) <= nat_sub(complen_mltl(phi), 1),
{
    complen_geq_one(phi);
    complen_len1_bound(phi, s);
}

/// Key helper lemma: progression usually decreases the computation length.
pub proof fn formula_progression_decreases_complen<A>(phi: Mltl<A>, tr: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
    ensures
        complen_mltl(phi) == 1 || complen_mltl(formula_progression_spec(phi, tr)) == 1
            || complen_mltl(formula_progression_spec(phi, tr)) <= nat_sub(complen_mltl(phi), tr.len()),
{
    complen_progression_bound(phi, tr);
    complen_geq_one(formula_progression_spec(phi, tr));
}

// ---------------------------------------------------------------------------
// Theorem 3
// ---------------------------------------------------------------------------

/// Helper (not in Isabelle): over a trace at least as long as the
/// computation length, progression yields a formula with the same truth
/// value on every trace, namely whether the trace satisfies `φ`. Theorem 3,
/// its False twin and the corollaries all follow.
pub proof fn formula_progression_value<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        forall|rho: Seq<Set<A>>| #[trigger] semantics_mltl(rho, formula_progression_spec(phi, pi))
            == semantics_mltl(pi, phi),
{
    complen_geq_one(phi);
    let k = (pi.len() - 1) as nat;
    let s = pi[k as int];
    let psi = formula_progression_spec(phi, take(pi, k));
    formula_progression_snoc(phi, take(pi, k), s);
    assert(take(pi, k).push(s) =~= pi);
    formula_progression_well_definedness_preserved(phi, take(pi, k));
    complen_progression_bound(phi, take(pi, k));
    complen_geq_one(psi);
    assert(drop(pi, k) =~= seq![s]);
    if k == 0 {
        assert(take(pi, 0).len() == 0);
        assert(seq![s] =~= pi);
    } else {
        satisfiability_preservation(pi, phi, k);
    }
    assert(semantics_mltl(seq![s], psi) == semantics_mltl(pi, phi));
    complen_one_len1_value(psi, s);
}

/// Helper: a formula with the same value `v` on every trace is equivalent
/// to True iff `v`, and to False iff not `v`.
proof fn constant_equiv<A>(x: Mltl<A>, v: bool)
    requires
        forall|rho: Seq<Set<A>>| #[trigger] semantics_mltl(rho, x) == v,
    ensures
        semantic_equiv(x, Mltl::True) == v,
        semantic_equiv(x, Mltl::False) == !v,
{
    let e = Seq::<Set<A>>::empty();
    assert(semantics_mltl(e, x) == v);
    assert(semantics_mltl(e, Mltl::<A>::True) && !semantics_mltl(e, Mltl::<A>::False));
}

pub proof fn formula_progression_correctness_len1_helper<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        pi.len() == 1,
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantic_equiv(formula_progression_len1_spec(phi, pi[0]), Mltl::True) == semantics_mltl(seq![pi[0]], phi),
{
    complen_geq_one(phi);
    complen_one_len1_value(phi, pi[0]);
    constant_equiv(formula_progression_len1_spec(phi, pi[0]), semantics_mltl(seq![pi[0]], phi));
}

pub proof fn formula_progression_correctness_len1<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        pi.len() == 1,
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantic_equiv(formula_progression_spec(phi, pi), Mltl::True) == semantics_mltl(pi, phi),
{
    formula_progression_correctness_len1_helper(phi, pi);
    assert(seq![pi[0]] =~= pi);
}

/// Theorem 3, `formula_progression_correctness`.
pub proof fn formula_progression_correctness<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantic_equiv(formula_progression_spec(phi, pi), Mltl::True) == semantics_mltl(pi, phi),
{
    formula_progression_value(phi, pi);
    constant_equiv(formula_progression_spec(phi, pi), semantics_mltl(pi, phi));
}

pub proof fn formula_progression_correctness_len1_helper_alt<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        pi.len() == 1,
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantic_equiv(formula_progression_len1_spec(phi, pi[0]), Mltl::False) == !semantics_mltl(seq![pi[0]], phi),
{
    complen_geq_one(phi);
    complen_one_len1_value(phi, pi[0]);
    constant_equiv(formula_progression_len1_spec(phi, pi[0]), semantics_mltl(seq![pi[0]], phi));
}

pub proof fn formula_progression_correctness_len1_alt<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        pi.len() == 1,
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantic_equiv(formula_progression_spec(phi, pi), Mltl::False) == !semantics_mltl(pi, phi),
{
    formula_progression_correctness_len1_helper_alt(phi, pi);
    assert(seq![pi[0]] =~= pi);
}

pub proof fn formula_progression_correctness_alt<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantic_equiv(formula_progression_spec(phi, pi), Mltl::False) == !semantics_mltl(pi, phi),
{
    formula_progression_value(phi, pi);
    constant_equiv(formula_progression_spec(phi, pi), semantics_mltl(pi, phi));
}

pub proof fn formula_progression_true_or_false<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantic_equiv(formula_progression_spec(phi, pi), Mltl::False)
            || semantic_equiv(formula_progression_spec(phi, pi), Mltl::True),
{
    formula_progression_correctness(phi, pi);
    formula_progression_correctness_alt(phi, pi);
}

/// Helper for the two append corollaries: extending a long-enough trace
/// does not change whether it satisfies `φ`.
proof fn formula_progression_extend<A>(phi: Mltl<A>, pi: Seq<Set<A>>, zeta: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantics_mltl(pi + zeta, phi) == semantics_mltl(pi, phi),
{
    complen_geq_one(phi);
    if zeta.len() == 0 {
        assert(pi + zeta =~= pi);
    } else {
        let k = pi.len();
        satisfiability_preservation(pi + zeta, phi, k);
        assert(take(pi + zeta, k) =~= pi);
        formula_progression_value(phi, pi);
        assert(semantics_mltl(drop(pi + zeta, k), formula_progression_spec(phi, pi)) == semantics_mltl(pi, phi));
    }
}

/// `formula_progression_append`
pub proof fn formula_progression_append<A>(phi: Mltl<A>, pi: Seq<Set<A>>, zeta: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        semantics_mltl(pi, phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantics_mltl(pi + zeta, phi),
{
    formula_progression_extend(phi, pi, zeta);
}

/// `formula_progression_append_converse`
pub proof fn formula_progression_append_converse<A>(phi: Mltl<A>, pi: Seq<Set<A>>, zeta: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        !semantics_mltl(pi, phi),
        pi.len() >= complen_mltl(phi),
    ensures
        !semantics_mltl(pi + zeta, phi),
{
    formula_progression_extend(phi, pi, zeta);
}

/// `complen_property`: states past the computation length never change
/// whether a trace satisfies `φ`.
pub proof fn complen_property<A>(phi: Mltl<A>, pi: Seq<Set<A>>)
    requires
        intervals_welldef(phi),
        pi.len() >= complen_mltl(phi),
    ensures
        semantics_mltl(pi, phi) == forall|zeta: Seq<Set<A>>| #[trigger] semantics_mltl(pi + zeta, phi),
{
    assert forall|zeta: Seq<Set<A>>| #[trigger] semantics_mltl(pi + zeta, phi) == semantics_mltl(pi, phi) by {
        formula_progression_extend(phi, pi, zeta);
    }
    assert(semantics_mltl(pi + Seq::empty(), phi) == semantics_mltl(pi, phi));
}

} // verus!
