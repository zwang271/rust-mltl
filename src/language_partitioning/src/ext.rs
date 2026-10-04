//! Extended MLTL formulas: formulas with an interval composition on every
//! temporal operator.
//!
//! Mirrors `MLTL_Language_Partition_Algorithm.thy`, section "Extended MLTL
//! Data Structure with Interval Compositions", and the section "Properties of
//! convert nnf ext" of `MLTL_Language_Partition_Proof.thy`.
//!
//! Isabelle's `'a mltl_ext` is here the mltl-core parse tree with a
//! `Seq<usize>` at every node (`MltlExt<A>`). Temporal nodes hold the
//! composition `L`; other nodes hold data the algorithm never reads (it
//! creates them with `[]`). Correspondence: agent-docs/correspondence/language-partitioning.md.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use mltl_core::parse_tree::*;

verus! {

broadcast use vstd::set::group_set_lemmas;

/// `'a mltl_ext`: a parse tree whose data is a list of naturals. On
/// `F`/`G`/`U`/`R` nodes it is the composition `L` of `F_c[a,b] <L> φ` etc.
pub type MltlExt<A> = MltlParseTree<A, Seq<usize>>;

// ---------------------------------------------------------------------------
// Constructors (Isabelle: the constructors of mltl_ext)
// ---------------------------------------------------------------------------

/// `True_c`
pub open spec fn true_mltl_ext<A>() -> MltlExt<A> {
    MltlParseTree::True(Seq::empty())
}

/// `False_c`
pub open spec fn false_mltl_ext<A>() -> MltlExt<A> {
    MltlParseTree::False(Seq::empty())
}

/// `Prop_c (p)`
pub open spec fn prop_mltl_ext<A>(p: A) -> MltlExt<A> {
    MltlParseTree::Prop(Seq::empty(), p)
}

/// `Not_c φ`
pub open spec fn not_mltl_ext<A>(phi: MltlExt<A>) -> MltlExt<A> {
    MltlParseTree::Not(Seq::empty(), Box::new(phi))
}

/// `φ And_c ψ`
pub open spec fn and_mltl_ext<A>(phi: MltlExt<A>, psi: MltlExt<A>) -> MltlExt<A> {
    MltlParseTree::And(Seq::empty(), Box::new(phi), Box::new(psi))
}

/// `φ Or_c ψ`
pub open spec fn or_mltl_ext<A>(phi: MltlExt<A>, psi: MltlExt<A>) -> MltlExt<A> {
    MltlParseTree::Or(Seq::empty(), Box::new(phi), Box::new(psi))
}

/// `F_c [a,b] <L> φ`
pub open spec fn future_mltl_ext<A>(a: usize, b: usize, l: Seq<usize>, phi: MltlExt<A>) -> MltlExt<A> {
    MltlParseTree::Future(l, a, b, Box::new(phi))
}

/// `G_c [a,b] <L> φ`
pub open spec fn global_mltl_ext<A>(a: usize, b: usize, l: Seq<usize>, phi: MltlExt<A>) -> MltlExt<A> {
    MltlParseTree::Global(l, a, b, Box::new(phi))
}

/// `φ U_c [a,b] <L> ψ`
pub open spec fn until_mltl_ext<A>(phi: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, psi: MltlExt<A>) -> MltlExt<A> {
    MltlParseTree::Until(l, Box::new(phi), a, b, Box::new(psi))
}

/// `φ R_c [a,b] <L> ψ`
pub open spec fn release_mltl_ext<A>(phi: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, psi: MltlExt<A>) -> MltlExt<A> {
    MltlParseTree::Release(l, Box::new(phi), a, b, Box::new(psi))
}

// ---------------------------------------------------------------------------
// to_mltl, semantics, languages
// ---------------------------------------------------------------------------

/// `to_mltl φ`: drop the compositions (`mltl_parse_tree_to_mltl`).
pub open spec fn to_mltl<A>(phi: MltlExt<A>) -> Mltl<A> {
    mltl_parse_tree_to_mltl_spec(phi)
}

/// `π ⊨_c φ ≡ π ⊨_m to_mltl φ`
pub open spec fn semantics_mltl_ext<A>(pi: Seq<Set<A>>, phi: MltlExt<A>) -> bool {
    semantics_mltl(pi, to_mltl(phi))
}

/// `φ ≡_c ψ ≡ to_mltl φ ≡_m to_mltl ψ`
pub open spec fn semantic_equiv_ext<A>(phi: MltlExt<A>, psi: MltlExt<A>) -> bool {
    semantic_equiv(to_mltl(phi), to_mltl(psi))
}

/// `language_mltl_r φ r = {π. π ⊨_m φ ∧ length π ≥ r}`. A set of traces is
/// infinite in general, hence `ISet`.
pub open spec fn language_mltl_r<A>(phi: Mltl<A>, r: nat) -> ISet<Seq<Set<A>>> {
    ISet::new(|pi: Seq<Set<A>>| semantics_mltl(pi, phi) && pi.len() >= r)
}

// ---------------------------------------------------------------------------
// convert_nnf_ext
// ---------------------------------------------------------------------------

/// `convert_nnf_ext φ`: `convert_nnf` on extended formulas; compositions
/// move with their operator.
///
/// Data at the other nodes (absent in Isabelle): a rewritten node keeps the
/// data of the node it replaces (`¬(φ ∧_d ψ) → (¬φ) ∨_d (¬ψ)`), and pushed-in
/// negations keep the data of the outer `Not`. On formulas built from
/// Isabelle's constructors (`[]` off temporal nodes) this is exactly
/// Isabelle's function.
pub open spec fn convert_nnf_ext_spec<A>(f: MltlExt<A>) -> MltlExt<A>
    decreases depth_mltl(to_mltl(f)),
    via convert_nnf_ext_decreases::<A>
{
    match f {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => f,
        MltlParseTree::And(d, phi, psi) =>
            MltlParseTree::And(d, Box::new(convert_nnf_ext_spec(*phi)), Box::new(convert_nnf_ext_spec(*psi))),
        MltlParseTree::Or(d, phi, psi) =>
            MltlParseTree::Or(d, Box::new(convert_nnf_ext_spec(*phi)), Box::new(convert_nnf_ext_spec(*psi))),
        MltlParseTree::Future(l, a, b, phi) => MltlParseTree::Future(l, a, b, Box::new(convert_nnf_ext_spec(*phi))),
        MltlParseTree::Global(l, a, b, phi) => MltlParseTree::Global(l, a, b, Box::new(convert_nnf_ext_spec(*phi))),
        MltlParseTree::Until(l, phi, a, b, psi) =>
            MltlParseTree::Until(l, Box::new(convert_nnf_ext_spec(*phi)), a, b, Box::new(convert_nnf_ext_spec(*psi))),
        MltlParseTree::Release(l, phi, a, b, psi) =>
            MltlParseTree::Release(l, Box::new(convert_nnf_ext_spec(*phi)), a, b, Box::new(convert_nnf_ext_spec(*psi))),
        // Rewriting with logical duals
        MltlParseTree::Not(dn, g) => match *g {
            MltlParseTree::True(d) => MltlParseTree::False(d),
            MltlParseTree::False(d) => MltlParseTree::True(d),
            MltlParseTree::Prop(_, _) => f,
            MltlParseTree::Not(_, phi) => convert_nnf_ext_spec(*phi),
            MltlParseTree::And(d, phi, psi) => MltlParseTree::Or(
                d,
                Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, phi))),
                Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, psi))),
            ),
            MltlParseTree::Or(d, phi, psi) => MltlParseTree::And(
                d,
                Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, phi))),
                Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, psi))),
            ),
            MltlParseTree::Future(l, a, b, phi) =>
                MltlParseTree::Global(l, a, b, Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, phi)))),
            MltlParseTree::Global(l, a, b, phi) =>
                MltlParseTree::Future(l, a, b, Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, phi)))),
            MltlParseTree::Until(l, phi, a, b, psi) => MltlParseTree::Release(
                l,
                Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, phi))),
                a,
                b,
                Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, psi))),
            ),
            MltlParseTree::Release(l, phi, a, b, psi) => MltlParseTree::Until(
                l,
                Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, phi))),
                a,
                b,
                Box::new(convert_nnf_ext_spec(MltlParseTree::Not(dn, psi))),
            ),
        },
    }
}

#[via_fn]
proof fn convert_nnf_ext_decreases<A>(f: MltlExt<A>) {
    reveal_with_fuel(depth_mltl, 3);
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
    match f {
        MltlParseTree::Not(dn, g) => match *g {
            MltlParseTree::And(_, phi, psi) | MltlParseTree::Or(_, phi, psi)
            | MltlParseTree::Until(_, phi, _, _, psi) | MltlParseTree::Release(_, phi, _, _, psi) => {
                assert(to_mltl(MltlParseTree::Not(dn, phi)) == Mltl::Not(Box::new(to_mltl(*phi))));
                assert(to_mltl(MltlParseTree::Not(dn, psi)) == Mltl::Not(Box::new(to_mltl(*psi))));
            },
            MltlParseTree::Future(_, _, _, phi) | MltlParseTree::Global(_, _, _, phi) => {
                assert(to_mltl(MltlParseTree::Not(dn, phi)) == Mltl::Not(Box::new(to_mltl(*phi))));
            },
            _ => {},
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Properties of convert_nnf_ext  (Proof.thy, first section)
// ---------------------------------------------------------------------------

/// `to_mltl (convert_nnf_ext φ) = convert_nnf (to_mltl φ)`
pub proof fn convert_nnf_and_convert_nnf_ext<A>(phi: MltlExt<A>)
    ensures
        to_mltl(convert_nnf_ext_spec(phi)) == convert_nnf_spec(to_mltl(phi)),
    decreases depth_mltl(to_mltl(phi)),
{
    reveal_with_fuel(depth_mltl, 3);
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
    match phi {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
        MltlParseTree::Not(dn, g) => match *g {
            MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
            MltlParseTree::Not(_, x) => convert_nnf_and_convert_nnf_ext(*x),
            MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
            | MltlParseTree::Release(_, x, _, _, y) => {
                convert_nnf_and_convert_nnf_ext(MltlParseTree::Not(dn, x));
                convert_nnf_and_convert_nnf_ext(MltlParseTree::Not(dn, y));
            },
            MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) => {
                convert_nnf_and_convert_nnf_ext(MltlParseTree::Not(dn, x));
            },
        },
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
        | MltlParseTree::Release(_, x, _, _, y) => {
            convert_nnf_and_convert_nnf_ext(*x);
            convert_nnf_and_convert_nnf_ext(*y);
        },
        MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) => {
            convert_nnf_and_convert_nnf_ext(*x);
        },
    }
}

/// `convert_nnf (to_mltl φ) = to_mltl (convert_nnf_ext φ)`
pub proof fn convert_nnf_ext_to_mltl_commute<A>(phi: MltlExt<A>)
    ensures
        convert_nnf_spec(to_mltl(phi)) == to_mltl(convert_nnf_ext_spec(phi)),
{
    convert_nnf_and_convert_nnf_ext(phi);
}

/// `intervals_welldef (to_mltl φ) ⟹ convert_nnf_ext φ ≡_c φ`
pub proof fn convert_nnf_ext_preserves_semantics<A>(phi: MltlExt<A>)
    requires
        intervals_welldef(to_mltl(phi)),
    ensures
        semantic_equiv_ext(convert_nnf_ext_spec(phi), phi),
{
    convert_nnf_and_convert_nnf_ext(phi);
    assert forall|pi: Seq<Set<A>>|
        #[trigger] semantics_mltl(pi, to_mltl(convert_nnf_ext_spec(phi))) == semantics_mltl(pi, to_mltl(phi)) by {
        convert_nnf_preserves_semantics(pi, to_mltl(phi));
    }
}

/// Pointwise form of `convert_nnf_ext_preserves_semantics`.
pub proof fn convert_nnf_ext_semantics_at<A>(pi: Seq<Set<A>>, phi: MltlExt<A>)
    requires
        intervals_welldef(to_mltl(phi)),
    ensures
        semantics_mltl_ext(pi, convert_nnf_ext_spec(phi)) == semantics_mltl_ext(pi, phi),
{
    convert_nnf_and_convert_nnf_ext(phi);
    convert_nnf_preserves_semantics(pi, to_mltl(phi));
}

/// `convert_nnf_ext φ = convert_nnf_ext (convert_nnf_ext φ)`
pub proof fn convert_nnf_ext_convert_nnf_ext<A>(phi: MltlExt<A>)
    ensures
        convert_nnf_ext_spec(phi) == convert_nnf_ext_spec(convert_nnf_ext_spec(phi)),
    decreases depth_mltl(to_mltl(phi)),
{
    reveal_with_fuel(depth_mltl, 3);
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
    reveal_with_fuel(convert_nnf_ext_spec, 2);
    match phi {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
        MltlParseTree::Not(dn, g) => match *g {
            MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
            MltlParseTree::Not(_, x) => convert_nnf_ext_convert_nnf_ext(*x),
            MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
            | MltlParseTree::Release(_, x, _, _, y) => {
                convert_nnf_ext_convert_nnf_ext(MltlParseTree::Not(dn, x));
                convert_nnf_ext_convert_nnf_ext(MltlParseTree::Not(dn, y));
            },
            MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) => {
                convert_nnf_ext_convert_nnf_ext(MltlParseTree::Not(dn, x));
            },
        },
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
        | MltlParseTree::Release(_, x, _, _, y) => {
            convert_nnf_ext_convert_nnf_ext(*x);
            convert_nnf_ext_convert_nnf_ext(*y);
        },
        MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) => {
            convert_nnf_ext_convert_nnf_ext(*x);
        },
    }
}

/// `to_mltl φ = True_m ⟹ φ = True_c` (here: up to the unused data).
pub proof fn to_mltl_true_bijective<A>(phi: MltlExt<A>)
    requires
        to_mltl(phi) == Mltl::<A>::True,
    ensures
        phi is True,
{
}

/// `to_mltl φ = False_m ⟹ φ = False_c` (up to the unused data).
pub proof fn to_mltl_false_bijective<A>(phi: MltlExt<A>)
    requires
        to_mltl(phi) == Mltl::<A>::False,
    ensures
        phi is False,
{
}

/// `to_mltl φ = Prop_m p ⟹ φ = Prop_c p` (up to the unused data).
pub proof fn to_mltl_prop_bijective<A>(phi: MltlExt<A>, p: A)
    requires
        to_mltl(phi) == Mltl::Prop(p),
    ensures
        phi is Prop && phi->Prop_1 == p,
{
}

/// `to_mltl φ = Not_m (Prop_m p) ⟹ φ = Not_c (Prop_c p)` (up to the unused data).
pub proof fn to_mltl_not_prop_bijective<A>(phi: MltlExt<A>, p: A)
    requires
        to_mltl(phi) == Mltl::Not(Box::new(Mltl::Prop(p))),
    ensures
        phi is Not && *phi->Not_1 is Prop && phi->Not_1->Prop_1 == p,
{
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 2);
}

/// Not in Isabelle (which reads it off `∃φ_init. φ = convert_nnf_ext φ_init`
/// case by case): in NNF, `Not` is applied to atoms only.
pub proof fn convert_nnf_ext_not_is_prop<A>(init: MltlExt<A>)
    ensures
        convert_nnf_ext_spec(init) is Not ==> *convert_nnf_ext_spec(init)->Not_1 is Prop,
{
    convert_nnf_and_convert_nnf_ext(init);
    convert_nnf_is_nnf(to_mltl(init));
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 2);
    reveal_with_fuel(is_nnf, 2);
}

// ---------------------------------------------------------------------------
// wpd_mltl  (Proof.thy, section "MLTL Decomposition Top Level Correctness")
// ---------------------------------------------------------------------------

/// `wpd_mltl φ`: the trace length the partition needs (worst-case
/// propagation delay plus one).
pub open spec fn wpd_mltl<A>(f: Mltl<A>) -> nat
    decreases f,
{
    match f {
        Mltl::False | Mltl::True | Mltl::Prop(_) => 1,
        Mltl::Not(phi) => wpd_mltl(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) => max_nat(wpd_mltl(*phi), wpd_mltl(*psi)),
        Mltl::Global(_, b, phi) | Mltl::Future(_, b, phi) => b as nat + wpd_mltl(*phi),
        Mltl::Release(phi, _, b, psi) | Mltl::Until(phi, _, b, psi) =>
            b as nat + max_nat(wpd_mltl(*phi), wpd_mltl(*psi)),
    }
}

/// `wpd_mltl φ ≥ 1`
pub proof fn wpd_geq_one<A>(phi: Mltl<A>)
    ensures
        wpd_mltl(phi) >= 1,
    decreases phi,
{
    match phi {
        Mltl::False | Mltl::True | Mltl::Prop(_) => {},
        Mltl::Not(x) | Mltl::Global(_, _, x) | Mltl::Future(_, _, x) => wpd_geq_one(*x),
        Mltl::And(x, y) | Mltl::Or(x, y) | Mltl::Release(x, _, _, y) | Mltl::Until(x, _, _, y) => {
            wpd_geq_one(*x);
            wpd_geq_one(*y);
        },
    }
}

/// `wpd_mltl (convert_nnf φ) = wpd_mltl φ`
pub proof fn wpd_convert_nnf<A>(phi: Mltl<A>)
    ensures
        wpd_mltl(convert_nnf_spec(phi)) == wpd_mltl(phi),
    decreases depth_mltl(phi),
{
    reveal_with_fuel(depth_mltl, 2);
    reveal_with_fuel(wpd_mltl, 2);
    match phi {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => match *g {
            Mltl::True | Mltl::False | Mltl::Prop(_) => {},
            Mltl::Not(x) => wpd_convert_nnf(*x),
            Mltl::And(x, y) | Mltl::Or(x, y) | Mltl::Until(x, _, _, y) | Mltl::Release(x, _, _, y) => {
                wpd_convert_nnf(Mltl::Not(x));
                wpd_convert_nnf(Mltl::Not(y));
            },
            Mltl::Future(_, _, x) | Mltl::Global(_, _, x) => wpd_convert_nnf(Mltl::Not(x)),
        },
        Mltl::And(x, y) | Mltl::Or(x, y) | Mltl::Until(x, _, _, y) | Mltl::Release(x, _, _, y) => {
            wpd_convert_nnf(*x);
            wpd_convert_nnf(*y);
        },
        Mltl::Future(_, _, x) | Mltl::Global(_, _, x) => wpd_convert_nnf(*x),
    }
}

/// `wpd_mltl (to_mltl (convert_nnf_ext φ)) = wpd_mltl (to_mltl φ)`
pub proof fn convert_nnf_ext_preserves_wpd<A>(phi: MltlExt<A>)
    ensures
        wpd_mltl(to_mltl(convert_nnf_ext_spec(phi))) == wpd_mltl(to_mltl(phi)),
{
    convert_nnf_and_convert_nnf_ext(phi);
    wpd_convert_nnf(to_mltl(phi));
}

/// `intervals_welldef F ⟹ intervals_welldef (convert_nnf F)`
pub proof fn nnf_intervals_welldef<A>(f: Mltl<A>)
    requires
        intervals_welldef(f),
    ensures
        intervals_welldef(convert_nnf_spec(f)),
    decreases depth_mltl(f),
{
    reveal_with_fuel(depth_mltl, 2);
    reveal_with_fuel(intervals_welldef, 2);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => match *g {
            Mltl::True | Mltl::False | Mltl::Prop(_) => {},
            Mltl::Not(x) => nnf_intervals_welldef(*x),
            Mltl::And(x, y) | Mltl::Or(x, y) | Mltl::Until(x, _, _, y) | Mltl::Release(x, _, _, y) => {
                nnf_intervals_welldef(Mltl::Not(x));
                nnf_intervals_welldef(Mltl::Not(y));
            },
            Mltl::Future(_, _, x) | Mltl::Global(_, _, x) => nnf_intervals_welldef(Mltl::Not(x)),
        },
        Mltl::And(x, y) | Mltl::Or(x, y) | Mltl::Until(x, _, _, y) | Mltl::Release(x, _, _, y) => {
            nnf_intervals_welldef(*x);
            nnf_intervals_welldef(*y);
        },
        Mltl::Future(_, _, x) | Mltl::Global(_, _, x) => nnf_intervals_welldef(*x),
    }
}

/// Not in Isabelle: `convert_nnf_ext` keeps intervals well defined.
pub proof fn convert_nnf_ext_welldef<A>(phi: MltlExt<A>)
    requires
        intervals_welldef(to_mltl(phi)),
    ensures
        intervals_welldef(to_mltl(convert_nnf_ext_spec(phi))),
{
    convert_nnf_and_convert_nnf_ext(phi);
    nnf_intervals_welldef(to_mltl(phi));
}

} // verus!
