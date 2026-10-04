//! The language-partitioning algorithm.
//!
//! Mirrors `MLTL_Language_Partition_Algorithm.thy`, section "Decomposition
//! Function". New nodes get `[]` as data (Isabelle: no data off temporal
//! nodes). Isabelle's `nat` positions become `usize` bounds by `as usize`;
//! for valid compositions every such value is at most the input bound `b`
//! (`composition::interval_times_facts`), so the casts are exact.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use crate::ext::*;
use crate::composition::*;

verus! {

// ---------------------------------------------------------------------------
// List helpers
// ---------------------------------------------------------------------------

/// `pairs L1 L2`: all pairs, in the order of `L1`, then `L2`.
pub open spec fn pairs<T>(l1: Seq<T>, l2: Seq<T>) -> Seq<(T, T)>
    decreases l1.len(),
{
    if l1.len() == 0 {
        Seq::empty()
    } else {
        l2.map_values(|x: T| (l1[0], x)) + pairs(l1.drop_first(), l2)
    }
}

/// Isabelle `concat`.
pub open spec fn concat<T>(xss: Seq<Seq<T>>) -> Seq<T>
    decreases xss.len(),
{
    if xss.len() == 0 {
        Seq::empty()
    } else {
        concat(xss.drop_last()) + xss.last()
    }
}

/// `And_mltl_list D_φ D_ψ = map (λx. And_mltl_ext (fst x) (snd x)) (pairs D_φ D_ψ)`
pub open spec fn And_mltl_list_spec<A>(d_phi: Seq<MltlExt<A>>, d_psi: Seq<MltlExt<A>>) -> Seq<MltlExt<A>> {
    pairs(d_phi, d_psi).map_values(|x: (MltlExt<A>, MltlExt<A>)| and_mltl_ext(x.0, x.1))
}

/// `Global_mltl_list D_φ a b L = map (λx. Global_mltl_ext a b L x) D_φ`
pub open spec fn Global_mltl_list_spec<A>(d_phi: Seq<MltlExt<A>>, a: usize, b: usize, l: Seq<usize>) -> Seq<MltlExt<A>> {
    d_phi.map_values(|x: MltlExt<A>| global_mltl_ext(a, b, l, x))
}

/// `Future_mltl_list D_φ a b L = map (λx. Future_mltl_ext a b L x) D_φ`
pub open spec fn Future_mltl_list_spec<A>(d_phi: Seq<MltlExt<A>>, a: usize, b: usize, l: Seq<usize>) -> Seq<MltlExt<A>> {
    d_phi.map_values(|x: MltlExt<A>| future_mltl_ext(a, b, l, x))
}

/// `Until_mltl_list φ D_ψ a b L = map (λx. Until_mltl_ext φ a b L x) D_ψ`
pub open spec fn Until_mltl_list_spec<A>(phi: MltlExt<A>, d_psi: Seq<MltlExt<A>>, a: usize, b: usize, l: Seq<usize>) -> Seq<MltlExt<A>> {
    d_psi.map_values(|x: MltlExt<A>| until_mltl_ext(phi, a, b, l, x))
}

/// `Release_mltl_list D_φ ψ a b L = map (λx. Release_mltl_ext x a b L ψ) D_φ`
pub open spec fn Release_mltl_list<A>(d_phi: Seq<MltlExt<A>>, psi: MltlExt<A>, a: usize, b: usize, l: Seq<usize>) -> Seq<MltlExt<A>> {
    d_phi.map_values(|x: MltlExt<A>| release_mltl_ext(x, a, b, l, psi))
}

/// `Mighty_Release_mltl_ext x ψ a b L = (x R_c[a,b] <L> ψ) And_c (F_c[a,b] <L> x)`
pub open spec fn Mighty_Release_mltl_ext<A>(x: MltlExt<A>, psi: MltlExt<A>, a: usize, b: usize, l: Seq<usize>) -> MltlExt<A> {
    and_mltl_ext(release_mltl_ext(x, a, b, l, psi), future_mltl_ext(a, b, l, x))
}

/// `Mighty_Release_mltl_list D_φ ψ a b L = map (λx. Mighty_Release_mltl_ext x ψ a b L) D_φ`
pub open spec fn Mighty_Release_mltl_list_spec<A>(d_phi: Seq<MltlExt<A>>, psi: MltlExt<A>, a: usize, b: usize, l: Seq<usize>) -> Seq<MltlExt<A>> {
    d_phi.map_values(|x: MltlExt<A>| Mighty_Release_mltl_ext(x, psi, a, b, l))
}

/// `Global_mltl_decomp D_φ a len L`: every way to pick, for each time
/// `a, …, a+len`, one formula of `D_φ` to hold there (`G[t,t] x`), joined by
/// `And` from the left.
pub open spec fn Global_mltl_decomp_spec<A>(d_phi: Seq<MltlExt<A>>, a: usize, len: nat, l: Seq<usize>) -> Seq<MltlExt<A>>
    decreases len,
{
    if len == 0 {
        Global_mltl_list_spec(d_phi, a, a, seq![1usize])
    } else {
        And_mltl_list_spec(
            Global_mltl_decomp_spec(d_phi, a, (len - 1) as nat, l),
            Global_mltl_list_spec(d_phi, (a + len) as usize, (a + len) as usize, seq![1usize]),
        )
    }
}

// ---------------------------------------------------------------------------
// LP_mltl_aux, LP_mltl
// ---------------------------------------------------------------------------

/// Block `i ≥ 1` of the `F` case: `φ` false before block `i`, and some
/// `x ∈ D_φ` holds within it. (Isabelle: the `λi. …` under `concat (map …)`.)
pub open spec fn LP_future_piece<A>(d_phi: Seq<MltlExt<A>>, phi: MltlExt<A>, s: Seq<nat>, i: int) -> Seq<MltlExt<A>> {
    And_mltl_list_spec(
        seq![global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], not_mltl_ext(phi))],
        Future_mltl_list_spec(d_phi, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]),
    )
}

/// Block `i ≥ 1` of the `U` case.
pub open spec fn LP_until_piece<A>(phi: MltlExt<A>, d_psi: Seq<MltlExt<A>>, psi: MltlExt<A>, s: Seq<nat>, i: int) -> Seq<MltlExt<A>> {
    And_mltl_list_spec(
        seq![global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(phi, not_mltl_ext(psi)))],
        Until_mltl_list_spec(phi, d_psi, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]),
    )
}

/// Block `i ≥ 1` of the `R` case.
pub open spec fn LP_release_piece<A>(d_phi: Seq<MltlExt<A>>, phi: MltlExt<A>, psi: MltlExt<A>, s: Seq<nat>, i: int) -> Seq<MltlExt<A>> {
    And_mltl_list_spec(
        seq![global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(not_mltl_ext(phi), psi))],
        Mighty_Release_mltl_list_spec(d_phi, psi, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]),
    )
}

/// `LP_mltl_aux φ k`: partition `φ` (in NNF) into formulas with pairwise
/// disjoint languages, recursing `k` levels deep. Case for case as Isabelle;
/// `concat (map f [1 ..< length L])` is `concat (Seq::new(length L - 1, |j| f (j+1)))`.
pub open spec fn LP_mltl_aux_spec<A>(phi: MltlExt<A>, k: nat) -> Seq<MltlExt<A>>
    decreases k,
{
    if k == 0 {
        seq![phi]
    } else {
        let k1 = (k - 1) as nat;
        match phi {
            MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => seq![phi],
            MltlParseTree::Not(_, x) => if *x is Prop { seq![phi] } else { Seq::empty() },
            MltlParseTree::And(_, x, y) => {
                let d_x = LP_mltl_aux_spec(convert_nnf_ext_spec(*x), k1);
                let d_y = LP_mltl_aux_spec(convert_nnf_ext_spec(*y), k1);
                And_mltl_list_spec(d_x, d_y)
            },
            MltlParseTree::Or(_, x, y) => {
                let d_x = LP_mltl_aux_spec(convert_nnf_ext_spec(*x), k1);
                let d_y = LP_mltl_aux_spec(convert_nnf_ext_spec(*y), k1);
                And_mltl_list_spec(d_x, d_y) + And_mltl_list_spec(seq![not_mltl_ext(*x)], d_y)
                    + And_mltl_list_spec(d_x, seq![not_mltl_ext(*y)])
            },
            MltlParseTree::Global(l, a, b, x) => {
                let d_x = LP_mltl_aux_spec(convert_nnf_ext_spec(*x), k1);
                if d_x.len() <= 1 {
                    seq![phi]
                } else {
                    Global_mltl_decomp_spec(d_x, a, nat_sub(b as nat, a as nat), l)
                }
            },
            MltlParseTree::Future(l, a, b, x) => {
                let d_x = LP_mltl_aux_spec(convert_nnf_ext_spec(*x), k1);
                let s = interval_times(a as nat, l);
                Future_mltl_list_spec(d_x, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize])
                    + concat(Seq::new(nat_sub(l.len(), 1), |j: int| LP_future_piece(d_x, *x, s, j + 1)))
            },
            MltlParseTree::Until(l, x, a, b, y) => {
                let d_y = LP_mltl_aux_spec(convert_nnf_ext_spec(*y), k1);
                let s = interval_times(a as nat, l);
                Until_mltl_list_spec(*x, d_y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize])
                    + concat(Seq::new(nat_sub(l.len(), 1), |j: int| LP_until_piece(*x, d_y, *y, s, j + 1)))
            },
            MltlParseTree::Release(l, x, a, b, y) => {
                let d_x = LP_mltl_aux_spec(convert_nnf_ext_spec(*x), k1);
                let s = interval_times(a as nat, l);
                seq![global_mltl_ext(a, b, l, and_mltl_ext(not_mltl_ext(*x), *y))]
                    + Mighty_Release_mltl_list_spec(d_x, *y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize])
                    + concat(Seq::new(nat_sub(l.len(), 1), |j: int| LP_release_piece(d_x, *x, *y, s, j + 1)))
            },
        }
    }
}

/// `LP_mltl φ k = map to_mltl (map convert_nnf_ext (LP_mltl_aux (convert_nnf_ext φ) k))`
pub open spec fn LP_mltl_spec<A>(phi: MltlExt<A>, k: nat) -> Seq<Mltl<A>> {
    LP_mltl_aux_spec(convert_nnf_ext_spec(phi), k).map_values(|x: MltlExt<A>| convert_nnf_ext_spec(x)).map_values(
        |x: MltlExt<A>| to_mltl(x),
    )
}

/// `Ands_mltl_ext X`: the conjunction of `X`, nested to the left (Proof.thy,
/// "Helper Lemmas"); `[] ↦ True_c`.
pub open spec fn Ands_mltl_ext<A>(x: Seq<MltlExt<A>>) -> MltlExt<A>
    decreases x.len(),
{
    if x.len() == 0 {
        true_mltl_ext()
    } else if x.len() == 1 {
        x[0]
    } else {
        and_mltl_ext(Ands_mltl_ext(x.drop_last()), x.last())
    }
}

} // verus!
