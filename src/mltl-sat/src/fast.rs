//! The fast (definitional) MLTL to Boolean translation.
//!
//! Mirrors `REU/isabelle/Fast_MLTL_To_SAT.thy`. Boolean variables are pairs
//! `(ψ, t)`: "subformula ψ holds at time t". For each node of a BNF formula
//! and each time in an accumulated window `[alb, aub]` the translation emits
//! a biconditional defining that variable from its children's variables.
//! Correspondence: agent-docs/project/m7-sat.md.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use propositional::formula::*;

verus! {

/// A Boolean variable of the translation: `(subformula, time)`.
pub type Var<A> = (Mltl<A>, nat);

/// `mltl_size` (termination measure of `fast_mltl_to_sat`)
pub open spec fn mltl_size<A>(f: Mltl<A>) -> nat
    decreases f,
{
    match f {
        Mltl::True => 1,
        Mltl::False => 3,
        Mltl::Prop(_) => 1,
        Mltl::Not(g) => 1 + mltl_size(*g),
        Mltl::And(g, h) => 1 + mltl_size(*g) + mltl_size(*h),
        Mltl::Or(g, h) => 5 + mltl_size(*g) + mltl_size(*h),
        Mltl::Until(g, a, _, h) => 1 + mltl_size(*g) + mltl_size(*h) + a as nat,
        Mltl::Future(a, _, g) => 3 + mltl_size(*g) + a as nat,
        Mltl::Global(a, _, g) => 6 + mltl_size(*g) + a as nat,
        Mltl::Release(g, a, _, h) => 5 + mltl_size(*g) + mltl_size(*h) + a as nat,
    }
}

/// `unroll_until φ₁ φ₂ lb ub`: `φ₂@lb ∨ (φ₁@lb ∧ unroll_until φ₁ φ₂ (lb+1) ub)`,
/// ending in `φ₂@ub`; `⊥` if `lb > ub`.
pub open spec fn unroll_until<A>(p1: Mltl<A>, p2: Mltl<A>, lb: nat, ub: nat) -> Formula<Var<A>>
    decreases ub - lb,
{
    if lb > ub {
        Formula::Bot
    } else if lb == ub {
        Formula::Atom((p2, lb))
    } else {
        Formula::Or(
            Box::new(Formula::Atom((p2, lb))),
            Box::new(Formula::And(Box::new(Formula::Atom((p1, lb))), Box::new(unroll_until(p1, p2, lb + 1, ub)))),
        )
    }
}

/// The nodes that get associated clauses: `True`, `Not`, `And`, `Until`
/// (the remaining equation of `get_associated_clauses_at_node` returns `[]`).
pub open spec fn has_associated_clauses<A>(f: Mltl<A>) -> bool {
    match f {
        Mltl::True | Mltl::Not(_) | Mltl::And(_, _) | Mltl::Until(_, _, _, _) => true,
        _ => false,
    }
}

/// The clause `get_associated_clauses_at_node` emits for node `f` at time
/// `k` (the element written out in each of its four equations).
pub open spec fn associated_clause<A>(f: Mltl<A>, k: nat) -> Formula<Var<A>> {
    match f {
        Mltl::True => biimp(Formula::Atom((Mltl::True, k)), top()),
        Mltl::Not(g) => biimp(Formula::Atom((f, k)), Formula::Not(Box::new(Formula::Atom((*g, k))))),
        Mltl::And(g, h) => biimp(
            Formula::Atom((f, k)),
            Formula::And(Box::new(Formula::Atom((*g, k))), Box::new(Formula::Atom((*h, k)))),
        ),
        Mltl::Until(g, a, b, h) => biimp(Formula::Atom((f, k)), unroll_until(*g, *h, (a + k) as nat, (b + k) as nat)),
        _ => Formula::Bot,
    }
}

/// `get_associated_clauses_at_node φ alb aub`: the clauses of node `φ` at
/// times `aub, aub-1, …, alb` (in that order); `[]` if `alb > aub`.
pub open spec fn get_associated_clauses_at_node<A>(f: Mltl<A>, alb: nat, aub: nat) -> Seq<Formula<Var<A>>>
    decreases aub,
{
    if !has_associated_clauses(f) || alb > aub {
        Seq::empty()
    } else if alb == aub {
        seq![associated_clause(f, aub)]
    } else {
        seq![associated_clause(f, aub)] + get_associated_clauses_at_node(f, alb, (aub - 1) as nat)
    }
}

/// `fast_mltl_to_sat φ alb aub`: associated clauses of every node of `φ`,
/// over the windows of times at which each node is needed.
pub open spec fn fast_mltl_to_sat<A>(f: Mltl<A>, alb: nat, aub: nat) -> Seq<Formula<Var<A>>>
    decreases mltl_size(f), 0nat,
    via fast_mltl_to_sat_decreases::<A>
{
    match f {
        Mltl::True => get_associated_clauses_at_node(Mltl::True, alb, aub),
        Mltl::False => fast_mltl_to_sat(Mltl::Not(Box::new(Mltl::True)), alb, aub),
        Mltl::Prop(_) => Seq::empty(),
        Mltl::Not(g) => get_associated_clauses_at_node(f, alb, aub) + fast_mltl_to_sat(*g, alb, aub),
        Mltl::And(g, h) => get_associated_clauses_at_node(f, alb, aub) + fast_mltl_to_sat(*g, alb, aub)
            + fast_mltl_to_sat(*h, alb, aub),
        Mltl::Or(g, h) => fast_mltl_to_sat(
            Mltl::Not(Box::new(Mltl::And(Box::new(Mltl::Not(g)), Box::new(Mltl::Not(h))))),
            alb,
            aub,
        ),
        Mltl::Until(g, a, b, h) => get_associated_clauses_at_node(f, alb, aub) + (if a == b {
            Seq::empty()
        } else {
            fast_mltl_to_sat(*g, (alb + a) as nat, nat_sub((aub + b) as nat, 1))
        }) + fast_mltl_to_sat(*h, (alb + a) as nat, (aub + b) as nat),
        Mltl::Future(a, b, g) => fast_mltl_to_sat(Mltl::Until(Box::new(Mltl::True), a, b, g), alb, aub),
        Mltl::Global(a, b, g) => fast_mltl_to_sat(
            Mltl::Not(Box::new(Mltl::Future(a, b, Box::new(Mltl::Not(g))))),
            alb,
            aub,
        ),
        Mltl::Release(g, a, b, h) => fast_mltl_to_sat(
            Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(g)), a, b, Box::new(Mltl::Not(h))))),
            alb,
            aub,
        ),
    }
}

#[via_fn]
proof fn fast_mltl_to_sat_decreases<A>(f: Mltl<A>, alb: nat, aub: nat) {
    reveal_with_fuel(mltl_size, 4);
    match f {
        Mltl::Or(g, h) => {
            assert(mltl_size(Mltl::Not(Box::new(Mltl::And(Box::new(Mltl::Not(g)), Box::new(Mltl::Not(h))))))
                < mltl_size(f));
        },
        Mltl::Global(a, b, g) => {
            assert(mltl_size(Mltl::Not(Box::new(Mltl::Future(a, b, Box::new(Mltl::Not(g)))))) < mltl_size(f));
        },
        Mltl::Release(g, a, b, h) => {
            assert(mltl_size(Mltl::Not(Box::new(Mltl::Until(Box::new(Mltl::Not(g)), a, b, Box::new(Mltl::Not(h))))))
                < mltl_size(f));
        },
        _ => {},
    }
}

/// `fast_mltl_to_sat_root φ = Atom (bnf φ, 0) # fast_mltl_to_sat (bnf φ) 0 0`
/// with `bnf φ = convert_bnf φ`.
pub open spec fn fast_mltl_to_sat_root<A>(f: Mltl<A>) -> Seq<Formula<Var<A>>> {
    let g = convert_bnf_spec(f);
    seq![Formula::Atom((g, 0nat))] + fast_mltl_to_sat(g, 0, 0)
}

// ---------------------------------------------------------------------------
// Satisfaction of clause lists
// ---------------------------------------------------------------------------

/// `∀c ∈ set cs. 𝒜 ⊨ c`
pub open spec fn models_all<V>(v: spec_fn(V) -> bool, cs: Seq<Formula<V>>) -> bool {
    forall|i: int| 0 <= i < cs.len() ==> formula_semantics(v, #[trigger] cs[i])
}

/// The canonical valuation of a trace: `λp. drop (snd p) π ⊨ fst p`.
pub open spec fn trace_valuation<A>(pi: Seq<Set<A>>) -> spec_fn(Var<A>) -> bool {
    |p: Var<A>| semantics_mltl(drop(pi, p.1), p.0)
}

pub proof fn models_all_append<V>(v: spec_fn(V) -> bool, xs: Seq<Formula<V>>, ys: Seq<Formula<V>>)
    ensures
        models_all(v, xs + ys) == (models_all(v, xs) && models_all(v, ys)),
{
    if models_all(v, xs + ys) {
        assert forall|i: int| 0 <= i < xs.len() implies formula_semantics(v, #[trigger] xs[i]) by {
            assert((xs + ys)[i] == xs[i]);
        }
        assert forall|i: int| 0 <= i < ys.len() implies formula_semantics(v, #[trigger] ys[i]) by {
            assert((xs + ys)[xs.len() + i] == ys[i]);
        }
    }
    if models_all(v, xs) && models_all(v, ys) {
        assert forall|i: int| 0 <= i < (xs + ys).len() implies formula_semantics(v, #[trigger] (xs + ys)[i]) by {
            if i < xs.len() {
                assert((xs + ys)[i] == xs[i]);
            } else {
                assert((xs + ys)[i] == ys[i - xs.len()]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Associated clauses (get_associated_clauses_at_node_*_k)
// ---------------------------------------------------------------------------

/// Shape of `get_associated_clauses_at_node`: element `i` is the node's
/// clause at time `aub - i` (gives `get_associated_clauses_at_node_True_k`,
/// `…_Not_k`, `…_And_k`, `…_Until_k`).
pub proof fn get_associated_clauses_at_node_shape<A>(f: Mltl<A>, alb: nat, aub: nat)
    ensures
        get_associated_clauses_at_node(f, alb, aub) == if has_associated_clauses(f) && alb <= aub {
            Seq::new((aub - alb + 1) as nat, |i: int| associated_clause(f, (aub - i) as nat))
        } else {
            Seq::empty()
        },
    decreases aub,
{
    if has_associated_clauses(f) && alb < aub {
        get_associated_clauses_at_node_shape(f, alb, (aub - 1) as nat);
        assert(get_associated_clauses_at_node(f, alb, aub) =~= Seq::new(
            (aub - alb + 1) as nat,
            |i: int| associated_clause(f, (aub - i) as nat),
        ));
    } else if has_associated_clauses(f) && alb == aub {
        assert(get_associated_clauses_at_node(f, alb, aub) =~= Seq::new(
            (aub - alb + 1) as nat,
            |i: int| associated_clause(f, (aub - i) as nat),
        ));
    }
}

/// All clauses of a node hold iff its clause holds at every time of the window.
pub proof fn models_associated_clauses<A>(v: spec_fn(Var<A>) -> bool, f: Mltl<A>, alb: nat, aub: nat)
    requires
        has_associated_clauses(f),
    ensures
        models_all(v, get_associated_clauses_at_node(f, alb, aub)) == (forall|k: nat|
            alb <= k <= aub ==> formula_semantics(v, #[trigger] associated_clause(f, k))),
{
    get_associated_clauses_at_node_shape(f, alb, aub);
    let cs = get_associated_clauses_at_node(f, alb, aub);
    if models_all(v, cs) {
        assert forall|k: nat| alb <= k <= aub implies formula_semantics(v, #[trigger] associated_clause(f, k)) by {
            assert(cs[aub - k] == associated_clause(f, k));
        }
    }
    if forall|k: nat| alb <= k <= aub ==> formula_semantics(v, #[trigger] associated_clause(f, k)) {
        assert forall|i: int| 0 <= i < cs.len() implies formula_semantics(v, #[trigger] cs[i]) by {
            assert(cs[i] == associated_clause(f, (aub - i) as nat));
        }
    }
}

// ---------------------------------------------------------------------------
// Until semantics
// ---------------------------------------------------------------------------

/// `unroll_until_semantics` and `unroll_until_semantics_converse`
pub proof fn unroll_until_semantics<A>(v: spec_fn(Var<A>) -> bool, p1: Mltl<A>, p2: Mltl<A>, lb: nat, ub: nat)
    requires
        lb <= ub,
    ensures
        formula_semantics(v, unroll_until(p1, p2, lb, ub)) == (exists|i: nat|
            lb <= i <= ub && #[trigger] v((p2, i)) && forall|j: nat| lb <= j < i ==> #[trigger] v((p1, j))),
    decreases ub - lb,
{
    reveal_with_fuel(formula_semantics, 3);
    if lb == ub {
        if formula_semantics(v, unroll_until(p1, p2, lb, ub)) {
            assert(v((p2, lb)));
        }
    } else {
        unroll_until_semantics(v, p1, p2, lb + 1, ub);
        let rhs = exists|i: nat| lb <= i <= ub && #[trigger] v((p2, i)) && forall|j: nat| lb <= j < i ==> #[trigger] v((p1, j));
        if formula_semantics(v, unroll_until(p1, p2, lb, ub)) {
            if !v((p2, lb)) {
                let i = choose|i: nat|
                    lb + 1 <= i <= ub && #[trigger] v((p2, i)) && forall|j: nat| lb + 1 <= j < i ==> #[trigger] v((p1, j));
                assert forall|j: nat| lb <= j < i implies #[trigger] v((p1, j)) by {
                    if j == lb {
                        assert(v((p1, lb)));
                    }
                }
            }
            assert(rhs);
        }
        if rhs {
            let i = choose|i: nat| lb <= i <= ub && #[trigger] v((p2, i)) && forall|j: nat| lb <= j < i ==> #[trigger] v((p1, j));
            if i != lb {
                assert(v((p1, lb)));
                assert(exists|i: nat|
                    lb + 1 <= i <= ub && #[trigger] v((p2, i)) && forall|j: nat| lb + 1 <= j < i ==> #[trigger] v((p1, j)));
            }
        }
    }
}

/// The right-hand side of `semantics_U`.
pub open spec fn until_at<A>(pi: Seq<Set<A>>, k: nat, phi: Mltl<A>, a: nat, b: nat, psi: Mltl<A>) -> bool {
    a <= b && pi.len() > a + k && exists|j: nat|
        a + k <= j <= b + k && semantics_mltl(#[trigger] drop(pi, j), psi) && forall|m: nat|
            a + k <= m < j ==> semantics_mltl(#[trigger] drop(pi, m), phi)
}

proof fn semantics_U_fwd<A>(pi: Seq<Set<A>>, k: nat, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>)
    requires
        semantics_mltl(drop(pi, k), Mltl::Until(Box::new(phi), a, b, Box::new(psi))),
    ensures
        until_at(pi, k, phi, a as nat, b as nat, psi),
{
    let pk = drop(pi, k);
    lemma_drop_len(pi, k);
    let i = choose|i: nat| (a <= i && i <= b) && (semantics_mltl(drop(pk, i), psi)
        && forall|j: nat| (j >= a && j < i) ==> semantics_mltl(drop(pk, j), phi));
    lemma_drop_drop(pi, k, i);
    assert(semantics_mltl(drop(pi, k + i), psi));
    assert forall|m: nat| a + k <= m < k + i implies semantics_mltl(#[trigger] drop(pi, m), phi) by {
        lemma_drop_drop(pi, k, (m - k) as nat);
        assert(semantics_mltl(drop(pk, (m - k) as nat), phi));
    }
}

proof fn semantics_U_bwd<A>(pi: Seq<Set<A>>, k: nat, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>)
    requires
        until_at(pi, k, phi, a as nat, b as nat, psi),
    ensures
        semantics_mltl(drop(pi, k), Mltl::Until(Box::new(phi), a, b, Box::new(psi))),
{
    let pk = drop(pi, k);
    lemma_drop_len(pi, k);
    let j = choose|j: nat| a + k <= j <= b + k && semantics_mltl(#[trigger] drop(pi, j), psi) && forall|m: nat|
        a + k <= m < j ==> semantics_mltl(#[trigger] drop(pi, m), phi);
    let i = (j - k) as nat;
    lemma_drop_drop(pi, k, i);
    assert(semantics_mltl(drop(pk, i), psi));
    assert forall|jj: nat| (jj >= a && jj < i) implies semantics_mltl(drop(pk, jj), phi) by {
        lemma_drop_drop(pi, k, jj);
        assert(semantics_mltl(drop(pi, k + jj), phi));
    }
}

/// `semantics_U`: until on a suffix, with absolute times.
pub proof fn semantics_U<A>(pi: Seq<Set<A>>, k: nat, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>)
    ensures
        semantics_mltl(drop(pi, k), Mltl::Until(Box::new(phi), a, b, Box::new(psi)))
            == until_at(pi, k, phi, a as nat, b as nat, psi),
{
    if semantics_mltl(drop(pi, k), Mltl::Until(Box::new(phi), a, b, Box::new(psi))) {
        semantics_U_fwd(pi, k, phi, a, b, psi);
    }
    if until_at(pi, k, phi, a as nat, b as nat, psi) {
        semantics_U_bwd(pi, k, phi, a, b, psi);
    }
}

// ---------------------------------------------------------------------------
// A satisfying trace induces a satisfying assignment
// ---------------------------------------------------------------------------

/// `unroll_until` under the canonical valuation of a trace.
pub proof fn unroll_until_trace<A>(pi: Seq<Set<A>>, p1: Mltl<A>, p2: Mltl<A>, lb: nat, ub: nat)
    requires
        lb <= ub,
    ensures
        formula_semantics(trace_valuation(pi), unroll_until(p1, p2, lb, ub)) == (exists|j: nat|
            lb <= j <= ub && semantics_mltl(#[trigger] drop(pi, j), p2) && forall|m: nat|
                lb <= m < j ==> semantics_mltl(#[trigger] drop(pi, m), p1)),
{
    let v = trace_valuation(pi);
    unroll_until_semantics(v, p1, p2, lb, ub);
    let rhs = exists|j: nat|
        lb <= j <= ub && semantics_mltl(#[trigger] drop(pi, j), p2) && forall|m: nat|
            lb <= m < j ==> semantics_mltl(#[trigger] drop(pi, m), p1);
    if formula_semantics(v, unroll_until(p1, p2, lb, ub)) {
        let i = choose|i: nat| lb <= i <= ub && #[trigger] v((p2, i)) && forall|j: nat| lb <= j < i ==> #[trigger] v((p1, j));
        assert(semantics_mltl(drop(pi, i), p2));
        assert forall|m: nat| lb <= m < i implies semantics_mltl(#[trigger] drop(pi, m), p1) by {
            assert(v((p1, m)));
        }
        assert(rhs);
    }
    if rhs {
        let j = choose|j: nat| lb <= j <= ub && semantics_mltl(#[trigger] drop(pi, j), p2) && forall|m: nat|
            lb <= m < j ==> semantics_mltl(#[trigger] drop(pi, m), p1);
        assert(v((p2, j)));
        assert forall|m: nat| lb <= m < j implies #[trigger] v((p1, m)) by {
            assert(semantics_mltl(drop(pi, m), p1));
        }
    }
}

/// The node clauses of a BNF node hold under the canonical valuation, at
/// every time `k` with `k + complen ≤ length π`.
proof fn trace_agrees_associated_clause<A>(pi: Seq<Set<A>>, f: Mltl<A>, k: nat)
    requires
        has_associated_clauses(f),
        intervals_welldef(f),
        k + complen_mltl(f) <= pi.len(),
    ensures
        formula_semantics(trace_valuation(pi), associated_clause(f, k)),
{
    let v = trace_valuation(pi);
    reveal_with_fuel(formula_semantics, 3);
    match f {
        Mltl::True => {
            biimp_semantics(v, Formula::Atom((Mltl::<A>::True, k)), top());
        },
        Mltl::Not(g) => {
            biimp_semantics(v, Formula::Atom((f, k)), Formula::Not(Box::new(Formula::Atom((*g, k)))));
        },
        Mltl::And(g, h) => {
            biimp_semantics(
                v,
                Formula::Atom((f, k)),
                Formula::And(Box::new(Formula::Atom((*g, k))), Box::new(Formula::Atom((*h, k)))),
            );
        },
        Mltl::Until(g, a, b, h) => {
            let lb = (a + k) as nat;
            let ub = (b + k) as nat;
            biimp_semantics(v, Formula::Atom((f, k)), unroll_until(*g, *h, lb, ub));
            complen_geq_one(*h);
            assert(pi.len() > a + k);
            semantics_U(pi, k, *g, a, b, *h);
            unroll_until_trace(pi, *g, *h, lb, ub);
            assert(v((f, k)) == semantics_mltl(drop(pi, k), Mltl::Until(Box::new(*g), a, b, Box::new(*h))));
        },
        _ => {},
    }
}

/// `trace_agrees_assign`: the canonical valuation of a long enough trace
/// satisfies every clause of `fast_mltl_to_sat φ alb aub`.
pub proof fn trace_agrees_assign<A>(pi: Seq<Set<A>>, f: Mltl<A>, alb: nat, aub: nat, n: nat)
    requires
        is_bnf(f),
        intervals_welldef(f),
        alb <= aub,
        aub + complen_mltl(f) <= n,
        pi.len() >= n,
    ensures
        models_all(trace_valuation(pi), fast_mltl_to_sat(f, alb, aub)),
    decreases f,
{
    let v = trace_valuation(pi);
    if has_associated_clauses(f) {
        models_associated_clauses(v, f, alb, aub);
        assert forall|k: nat| alb <= k <= aub implies formula_semantics(v, #[trigger] associated_clause(f, k)) by {
            trace_agrees_associated_clause(pi, f, k);
        }
    }
    match f {
        Mltl::True => {},
        Mltl::Prop(_) => {},
        Mltl::Not(g) => {
            trace_agrees_assign(pi, *g, alb, aub, n);
            models_all_append(v, get_associated_clauses_at_node(f, alb, aub), fast_mltl_to_sat(*g, alb, aub));
        },
        Mltl::And(g, h) => {
            trace_agrees_assign(pi, *g, alb, aub, n);
            trace_agrees_assign(pi, *h, alb, aub, n);
            let gc = get_associated_clauses_at_node(f, alb, aub);
            models_all_append(v, gc, fast_mltl_to_sat(*g, alb, aub));
            models_all_append(v, gc + fast_mltl_to_sat(*g, alb, aub), fast_mltl_to_sat(*h, alb, aub));
        },
        Mltl::Until(g, a, b, h) => {
            let gc = get_associated_clauses_at_node(f, alb, aub);
            let mid: Seq<Formula<Var<A>>> = if a == b {
                Seq::empty()
            } else {
                fast_mltl_to_sat(*g, (alb + a) as nat, nat_sub((aub + b) as nat, 1))
            };
            if a != b {
                complen_geq_one(*g);
                trace_agrees_assign(pi, *g, (alb + a) as nat, nat_sub((aub + b) as nat, 1), n);
            }
            trace_agrees_assign(pi, *h, (alb + a) as nat, (aub + b) as nat, n);
            models_all_append(v, gc, mid);
            models_all_append(v, gc + mid, fast_mltl_to_sat(*h, (alb + a) as nat, (aub + b) as nat));
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// A satisfying assignment induces a satisfying trace
// ---------------------------------------------------------------------------

/// `val_to_trace (λx. 𝒜 (Prop (fst x), snd x)) N`, restricted to the atoms
/// `ap`: Isabelle's states `{p. 𝒜 (Prop p, t)}` may be infinite, ours are
/// finite (D16), so they keep only atoms in `ap` (callers pass a superset of
/// the formula's atoms).
pub open spec fn val_to_trace<A>(v: spec_fn(Var<A>) -> bool, n: nat, ap: Set<A>) -> Seq<Set<A>> {
    Seq::new(n, |t: int| ap.filter(|p: A| v((Mltl::Prop(p), t as nat))))
}

/// `unroll_until` under a valuation that agrees with a trace on the
/// variables it mentions.
pub proof fn unroll_until_agree<A>(
    v: spec_fn(Var<A>) -> bool,
    pi: Seq<Set<A>>,
    p1: Mltl<A>,
    p2: Mltl<A>,
    lb: nat,
    ub: nat,
)
    requires
        lb <= ub,
        forall|j: nat| lb <= j <= ub ==> #[trigger] v((p2, j)) == semantics_mltl(drop(pi, j), p2),
        forall|j: nat| lb <= j < ub ==> #[trigger] v((p1, j)) == semantics_mltl(drop(pi, j), p1),
    ensures
        formula_semantics(v, unroll_until(p1, p2, lb, ub)) == (exists|j: nat|
            lb <= j <= ub && semantics_mltl(#[trigger] drop(pi, j), p2) && forall|m: nat|
                lb <= m < j ==> semantics_mltl(#[trigger] drop(pi, m), p1)),
{
    unroll_until_semantics(v, p1, p2, lb, ub);
    let rhs = exists|j: nat|
        lb <= j <= ub && semantics_mltl(#[trigger] drop(pi, j), p2) && forall|m: nat|
            lb <= m < j ==> semantics_mltl(#[trigger] drop(pi, m), p1);
    if formula_semantics(v, unroll_until(p1, p2, lb, ub)) {
        let i = choose|i: nat| lb <= i <= ub && #[trigger] v((p2, i)) && forall|j: nat| lb <= j < i ==> #[trigger] v((p1, j));
        assert(semantics_mltl(drop(pi, i), p2));
        assert forall|m: nat| lb <= m < i implies semantics_mltl(#[trigger] drop(pi, m), p1) by {
            assert(v((p1, m)));
        }
        assert(rhs);
    }
    if rhs {
        let j = choose|j: nat| lb <= j <= ub && semantics_mltl(#[trigger] drop(pi, j), p2) && forall|m: nat|
            lb <= m < j ==> semantics_mltl(#[trigger] drop(pi, m), p1);
        assert(v((p2, j)));
        assert forall|m: nat| lb <= m < j implies #[trigger] v((p1, m)) by {
            assert(semantics_mltl(drop(pi, m), p1));
        }
    }
}

/// `assign_agrees_trace`, at one time `k`: an assignment satisfying every
/// clause of `fast_mltl_to_sat φ alb aub` gives each `(φ, k)` the truth value
/// of `φ` at `k` on the trace it induces.
pub proof fn assign_agrees_trace<A>(
    v: spec_fn(Var<A>) -> bool,
    f: Mltl<A>,
    alb: nat,
    aub: nat,
    n: nat,
    ap: Set<A>,
    k: nat,
)
    requires
        is_bnf(f),
        intervals_welldef(f),
        alb <= k <= aub,
        aub + complen_mltl(f) <= n,
        models_all(v, fast_mltl_to_sat(f, alb, aub)),
        atoms_mltl(f).subset_of(ap),
    ensures
        v((f, k)) == semantics_mltl(drop(val_to_trace(v, n, ap), k), f),
    decreases f,
{
    let pi = val_to_trace(v, n, ap);
    lemma_drop_len(pi, k);
    if has_associated_clauses(f) {
        models_associated_clauses(v, f, alb, aub);
    }
    reveal_with_fuel(formula_semantics, 3);
    match f {
        Mltl::True => {
            biimp_semantics(v, Formula::Atom((Mltl::<A>::True, k)), top());
            assert(formula_semantics(v, associated_clause(f, k)));
        },
        Mltl::Prop(p) => {
            assert(drop(pi, k)[0] == pi[k as int]);
            assert(ap.contains(p));
            assert(pi[k as int].contains(p) == v((Mltl::Prop(p), k)));
        },
        Mltl::Not(g) => {
            let gc = get_associated_clauses_at_node(f, alb, aub);
            models_all_append(v, gc, fast_mltl_to_sat(*g, alb, aub));
            assert(formula_semantics(v, associated_clause(f, k)));
            biimp_semantics(v, Formula::Atom((f, k)), Formula::Not(Box::new(Formula::Atom((*g, k)))));
            assign_agrees_trace(v, *g, alb, aub, n, ap, k);
        },
        Mltl::And(g, h) => {
            let gc = get_associated_clauses_at_node(f, alb, aub);
            models_all_append(v, gc + fast_mltl_to_sat(*g, alb, aub), fast_mltl_to_sat(*h, alb, aub));
            models_all_append(v, gc, fast_mltl_to_sat(*g, alb, aub));
            assert(formula_semantics(v, associated_clause(f, k)));
            biimp_semantics(
                v,
                Formula::Atom((f, k)),
                Formula::And(Box::new(Formula::Atom((*g, k))), Box::new(Formula::Atom((*h, k)))),
            );
            assign_agrees_trace(v, *g, alb, aub, n, ap, k);
            assign_agrees_trace(v, *h, alb, aub, n, ap, k);
        },
        Mltl::Until(g, a, b, h) => {
            let gc = get_associated_clauses_at_node(f, alb, aub);
            let mid: Seq<Formula<Var<A>>> = if a == b {
                Seq::empty()
            } else {
                fast_mltl_to_sat(*g, (alb + a) as nat, nat_sub((aub + b) as nat, 1))
            };
            let hc = fast_mltl_to_sat(*h, (alb + a) as nat, (aub + b) as nat);
            models_all_append(v, gc + mid, hc);
            models_all_append(v, gc, mid);
            assert(formula_semantics(v, associated_clause(f, k)));
            let lb = (a + k) as nat;
            let ub = (b + k) as nat;
            biimp_semantics(v, Formula::Atom((f, k)), unroll_until(*g, *h, lb, ub));
            complen_geq_one(*g);
            complen_geq_one(*h);
            assert forall|j: nat| lb <= j <= ub implies #[trigger] v((*h, j)) == semantics_mltl(drop(pi, j), *h) by {
                assign_agrees_trace(v, *h, (alb + a) as nat, (aub + b) as nat, n, ap, j);
            }
            assert forall|j: nat| lb <= j < ub implies #[trigger] v((*g, j)) == semantics_mltl(drop(pi, j), *g) by {
                assign_agrees_trace(v, *g, (alb + a) as nat, nat_sub((aub + b) as nat, 1), n, ap, j);
            }
            unroll_until_agree(v, pi, *g, *h, lb, ub);
            semantics_U(pi, k, *g, a, b, *h);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Soundness
// ---------------------------------------------------------------------------

pub proof fn models_set_to_set<V>(v: spec_fn(V) -> bool, cs: Seq<Formula<V>>)
    ensures
        models_set(v, cs.to_set()) == models_all(v, cs),
{
    if models_set(v, cs.to_set()) {
        assert forall|i: int| 0 <= i < cs.len() implies formula_semantics(v, #[trigger] cs[i]) by {
            assert(cs.to_set().contains(cs[i]));
        }
    }
    if models_all(v, cs) {
        assert forall|g: Formula<V>| #[trigger] cs.to_set().contains(g) implies formula_semantics(v, g) by {
            let i = choose|i: int| 0 <= i < cs.len() && cs[i] == g;
        }
    }
}

/// `soundness_fast_mltl_to_sat_root_complen`:
/// `MLTL_SAT_LEN φ (complen φ) ⟷ sat (set (fast_mltl_to_sat_root φ))`.
/// (Isabelle proves it through `soundness_fast_mltl_to_sat_root_helper`, a
/// second induction; here it follows directly from `trace_agrees_assign` and
/// `assign_agrees_trace`.)
pub proof fn soundness_fast_mltl_to_sat_root_complen<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        mltl_sat_len(f, complen_mltl(f)) == sat(fast_mltl_to_sat_root(f).to_set()),
{
    let g = convert_bnf_spec(f);
    convert_bnf_is_bnf(f);
    convert_bnf_welldef(f);
    convert_bnf_complen(f);
    convert_bnf_equiv(f);
    let n = complen_mltl(f);
    let root = fast_mltl_to_sat_root(f);
    let rest = fast_mltl_to_sat(g, 0, 0);
    assert(root == seq![Formula::Atom((g, 0nat))] + rest);
    if mltl_sat_len(f, n) {
        let pi = choose|pi: Seq<Set<A>>| pi.len() >= n && #[trigger] semantics_mltl(pi, f);
        let v = trace_valuation(pi);
        assert(semantics_mltl(pi, g));
        lemma_drop_zero(pi);
        assert(v((g, 0nat)));
        trace_agrees_assign(pi, g, 0, 0, n);
        assert(models_all(v, seq![Formula::Atom((g, 0nat))]));
        models_all_append(v, seq![Formula::Atom((g, 0nat))], rest);
        models_set_to_set(v, root);
        assert(models_set(v, root.to_set()));
    }
    if sat(root.to_set()) {
        let v = choose|v: spec_fn(Var<A>) -> bool| #[trigger] models_set(v, root.to_set());
        models_set_to_set(v, root);
        models_all_append(v, seq![Formula::Atom((g, 0nat))], rest);
        assert(formula_semantics(v, seq![Formula::Atom((g, 0nat))][0]));
        let ap = atoms_mltl(g);
        assign_agrees_trace(v, g, 0, 0, n, ap, 0);
        let pi = val_to_trace(v, n, ap);
        lemma_drop_zero(pi);
        assert(semantics_mltl(pi, g));
        assert(semantics_mltl(pi, f));
        assert(pi.len() >= n);
    }
}

} // verus!
