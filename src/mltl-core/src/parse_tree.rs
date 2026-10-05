//! MLTL parse trees: formulas that carry auxiliary data at every node.
//!
//! Mirrors the section "MLTL Parse Tree Datatype with Auxiliary Storage" of
//! the unpublished `MLTL_Properties_Extended.thy` (REU 2026). Language
//! partitioning instantiates the data with interval compositions; R2U2 will
//! use it for monitor state.
//! Correspondence table: agent-docs/correspondence/mission-time-ltl.md.
use vstd::prelude::*;
use crate::mltl::*;

verus! {

// ---------------------------------------------------------------------------
// Syntax  (Isabelle: datatype ('a, 'b) mltl_parse_tree)
// ---------------------------------------------------------------------------

/// An MLTL formula over atoms `A` with a value of type `B` at every node.
///
/// Variant and argument order match the Isabelle constructors (`Prop_e`,
/// `True_e`, ...): the data comes first, e.g. `Until(d, φ, a, b, ψ)` is
/// `Until_e d φ a b ψ`. Bounds are `usize`, as in `Mltl` (D15).
#[derive(Debug)]
pub enum MltlParseTree<A, B> {
    /// `Prop_e d p`
    Prop(B, A),
    /// `True_e d`
    True(B),
    /// `False_e d`
    False(B),
    /// `Not_e d φ`
    Not(B, Box<MltlParseTree<A, B>>),
    /// `And_e d φ ψ`
    And(B, Box<MltlParseTree<A, B>>, Box<MltlParseTree<A, B>>),
    /// `Or_e d φ ψ`
    Or(B, Box<MltlParseTree<A, B>>, Box<MltlParseTree<A, B>>),
    /// `Future_e d a b φ`
    Future(B, usize, usize, Box<MltlParseTree<A, B>>),
    /// `Global_e d a b φ`
    Global(B, usize, usize, Box<MltlParseTree<A, B>>),
    /// `Until_e d φ a b ψ`
    Until(B, Box<MltlParseTree<A, B>>, usize, usize, Box<MltlParseTree<A, B>>),
    /// `Release_e d φ a b ψ`
    Release(B, Box<MltlParseTree<A, B>>, usize, usize, Box<MltlParseTree<A, B>>),
}

/// `mltl_parse_tree_to_mltl T`: forget the data.
pub open spec fn mltl_parse_tree_to_mltl_spec<A, B>(t: MltlParseTree<A, B>) -> Mltl<A>
    decreases t,
{
    match t {
        MltlParseTree::True(_) => Mltl::True,
        MltlParseTree::False(_) => Mltl::False,
        MltlParseTree::Prop(_, p) => Mltl::Prop(p),
        MltlParseTree::Not(_, phi) => Mltl::Not(Box::new(mltl_parse_tree_to_mltl_spec(*phi))),
        MltlParseTree::And(_, phi, psi) => Mltl::And(
            Box::new(mltl_parse_tree_to_mltl_spec(*phi)),
            Box::new(mltl_parse_tree_to_mltl_spec(*psi)),
        ),
        MltlParseTree::Or(_, phi, psi) => Mltl::Or(
            Box::new(mltl_parse_tree_to_mltl_spec(*phi)),
            Box::new(mltl_parse_tree_to_mltl_spec(*psi)),
        ),
        MltlParseTree::Future(_, a, b, phi) => Mltl::Future(a, b, Box::new(mltl_parse_tree_to_mltl_spec(*phi))),
        MltlParseTree::Global(_, a, b, phi) => Mltl::Global(a, b, Box::new(mltl_parse_tree_to_mltl_spec(*phi))),
        MltlParseTree::Until(_, phi, a, b, psi) => Mltl::Until(
            Box::new(mltl_parse_tree_to_mltl_spec(*phi)),
            a,
            b,
            Box::new(mltl_parse_tree_to_mltl_spec(*psi)),
        ),
        MltlParseTree::Release(_, phi, a, b, psi) => Mltl::Release(
            Box::new(mltl_parse_tree_to_mltl_spec(*phi)),
            a,
            b,
            Box::new(mltl_parse_tree_to_mltl_spec(*psi)),
        ),
    }
}

/// `get_aux_data T`: the data at the root.
pub open spec fn get_aux_data<A, B>(t: MltlParseTree<A, B>) -> B {
    match t {
        MltlParseTree::True(d) | MltlParseTree::False(d) | MltlParseTree::Prop(d, _)
        | MltlParseTree::Not(d, _) | MltlParseTree::And(d, _, _) | MltlParseTree::Or(d, _, _)
        | MltlParseTree::Future(d, _, _, _) | MltlParseTree::Global(d, _, _, _)
        | MltlParseTree::Until(d, _, _, _, _) | MltlParseTree::Release(d, _, _, _, _) => d,
    }
}

/// `get_child_trees T`: the direct subtrees; a leaf returns itself.
pub open spec fn get_child_trees<A, B>(t: MltlParseTree<A, B>) -> Seq<MltlParseTree<A, B>> {
    match t {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => seq![t],
        MltlParseTree::Not(_, phi) | MltlParseTree::Future(_, _, _, phi)
        | MltlParseTree::Global(_, _, _, phi) => seq![*phi],
        MltlParseTree::And(_, phi, psi) | MltlParseTree::Or(_, phi, psi)
        | MltlParseTree::Until(_, phi, _, _, psi) | MltlParseTree::Release(_, phi, _, _, psi) =>
            seq![*phi, *psi],
    }
}

/// `update_aux_data T d`: replace the data at the root.
pub open spec fn update_aux_data<A, B>(t: MltlParseTree<A, B>, d: B) -> MltlParseTree<A, B> {
    match t {
        MltlParseTree::True(_) => MltlParseTree::True(d),
        MltlParseTree::False(_) => MltlParseTree::False(d),
        MltlParseTree::Prop(_, p) => MltlParseTree::Prop(d, p),
        MltlParseTree::Not(_, c) => MltlParseTree::Not(d, c),
        MltlParseTree::And(_, l, r) => MltlParseTree::And(d, l, r),
        MltlParseTree::Or(_, l, r) => MltlParseTree::Or(d, l, r),
        MltlParseTree::Future(_, a, b, c) => MltlParseTree::Future(d, a, b, c),
        MltlParseTree::Global(_, a, b, c) => MltlParseTree::Global(d, a, b, c),
        MltlParseTree::Until(_, l, a, b, r) => MltlParseTree::Until(d, l, a, b, r),
        MltlParseTree::Release(_, l, a, b, r) => MltlParseTree::Release(d, l, a, b, r),
    }
}

/// `map_aux_data T f`: apply `f` to the data at every node.
pub open spec fn map_aux_data<A, B, C>(t: MltlParseTree<A, B>, f: spec_fn(B) -> C) -> MltlParseTree<A, C>
    decreases t,
{
    match t {
        MltlParseTree::True(d) => MltlParseTree::True(f(d)),
        MltlParseTree::False(d) => MltlParseTree::False(f(d)),
        MltlParseTree::Prop(d, p) => MltlParseTree::Prop(f(d), p),
        MltlParseTree::Not(d, phi) => MltlParseTree::Not(f(d), Box::new(map_aux_data(*phi, f))),
        MltlParseTree::And(d, phi, psi) =>
            MltlParseTree::And(f(d), Box::new(map_aux_data(*phi, f)), Box::new(map_aux_data(*psi, f))),
        MltlParseTree::Or(d, phi, psi) =>
            MltlParseTree::Or(f(d), Box::new(map_aux_data(*phi, f)), Box::new(map_aux_data(*psi, f))),
        MltlParseTree::Future(d, a, b, phi) => MltlParseTree::Future(f(d), a, b, Box::new(map_aux_data(*phi, f))),
        MltlParseTree::Global(d, a, b, phi) => MltlParseTree::Global(f(d), a, b, Box::new(map_aux_data(*phi, f))),
        MltlParseTree::Until(d, phi, a, b, psi) =>
            MltlParseTree::Until(f(d), Box::new(map_aux_data(*phi, f)), a, b, Box::new(map_aux_data(*psi, f))),
        MltlParseTree::Release(d, phi, a, b, psi) =>
            MltlParseTree::Release(f(d), Box::new(map_aux_data(*phi, f)), a, b, Box::new(map_aux_data(*psi, f))),
    }
}

/// Isabelle's generated `size` on parse trees: one per node, as `size_mltl`
/// (the data, of a type variable, counts 0).
pub open spec fn size_parse_tree<A, B>(t: MltlParseTree<A, B>) -> nat
    decreases t,
{
    match t {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => 1,
        MltlParseTree::Not(_, g) | MltlParseTree::Future(_, _, _, g) | MltlParseTree::Global(_, _, _, g) =>
            1 + size_parse_tree(*g),
        MltlParseTree::And(_, g, h) | MltlParseTree::Or(_, g, h) | MltlParseTree::Until(_, g, _, _, h)
        | MltlParseTree::Release(_, g, _, _, h) => 1 + size_parse_tree(*g) + size_parse_tree(*h),
    }
}

// ---------------------------------------------------------------------------
// Lemmas  (subsection "MLTL Parse Tree Lemmas")
// ---------------------------------------------------------------------------

/// `size T = size (mltl_parse_tree_to_mltl T)`
pub proof fn mltl_parse_tree_preserves_size<A, B>(t: MltlParseTree<A, B>)
    ensures
        size_parse_tree(t) == size_mltl(mltl_parse_tree_to_mltl_spec(t)),
    decreases t,
{
    match t {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
        MltlParseTree::Not(_, g) | MltlParseTree::Future(_, _, _, g) | MltlParseTree::Global(_, _, _, g) =>
            mltl_parse_tree_preserves_size(*g),
        MltlParseTree::And(_, g, h) | MltlParseTree::Or(_, g, h) | MltlParseTree::Until(_, g, _, _, h)
        | MltlParseTree::Release(_, g, _, _, h) => {
            mltl_parse_tree_preserves_size(*g);
            mltl_parse_tree_preserves_size(*h);
        },
    }
}

/// `True_m = mltl_parse_tree_to_mltl T ⟹ ∃data. T = True_e data`
pub proof fn mltl_parse_tree_true_inv<A, B>(t: MltlParseTree<A, B>)
    requires
        Mltl::True == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is True,
{
}

/// `False_m = mltl_parse_tree_to_mltl T ⟹ ∃data. T = False_e data`
pub proof fn mltl_parse_tree_false_inv<A, B>(t: MltlParseTree<A, B>)
    requires
        Mltl::False == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is False,
{
}

/// `Prop_m p = mltl_parse_tree_to_mltl T ⟹ ∃data. T = Prop_e data p`
pub proof fn mltl_parse_tree_prop_inv<A, B>(t: MltlParseTree<A, B>, p: A)
    requires
        Mltl::Prop(p) == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is Prop && t->Prop_1 == p,
{
}

/// `Not_m φ = mltl_parse_tree_to_mltl T ⟹ ∃data φT. T = Not_e data φT ∧ φ = mltl_parse_tree_to_mltl φT`
pub proof fn mltl_parse_tree_not_inv<A, B>(t: MltlParseTree<A, B>, phi: Mltl<A>)
    requires
        Mltl::Not(Box::new(phi)) == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is Not && phi == mltl_parse_tree_to_mltl_spec(*t->Not_1),
{
}

/// `φ And_m ψ = mltl_parse_tree_to_mltl T ⟹ ∃data φT ψT. T = And_e data φT ψT ∧ …`
pub proof fn mltl_parse_tree_and_inv<A, B>(t: MltlParseTree<A, B>, phi: Mltl<A>, psi: Mltl<A>)
    requires
        Mltl::And(Box::new(phi), Box::new(psi)) == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is And && phi == mltl_parse_tree_to_mltl_spec(*t->And_1)
            && psi == mltl_parse_tree_to_mltl_spec(*t->And_2),
{
}

/// `φ Or_m ψ = mltl_parse_tree_to_mltl T ⟹ ∃data φT ψT. T = Or_e data φT ψT ∧ …`
pub proof fn mltl_parse_tree_or_inv<A, B>(t: MltlParseTree<A, B>, phi: Mltl<A>, psi: Mltl<A>)
    requires
        Mltl::Or(Box::new(phi), Box::new(psi)) == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is Or && phi == mltl_parse_tree_to_mltl_spec(*t->Or_1)
            && psi == mltl_parse_tree_to_mltl_spec(*t->Or_2),
{
}

/// `G_m[a,b] φ = mltl_parse_tree_to_mltl T ⟹ ∃data φT. T = Global_e data a b φT ∧ …`
pub proof fn mltl_parse_tree_global_inv<A, B>(t: MltlParseTree<A, B>, a: usize, b: usize, phi: Mltl<A>)
    requires
        Mltl::Global(a, b, Box::new(phi)) == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is Global && t->Global_1 == a && t->Global_2 == b
            && phi == mltl_parse_tree_to_mltl_spec(*t->Global_3),
{
}

/// `F_m[a,b] φ = mltl_parse_tree_to_mltl T ⟹ ∃data φT. T = Future_e data a b φT ∧ …`
pub proof fn mltl_parse_tree_future_inv<A, B>(t: MltlParseTree<A, B>, a: usize, b: usize, phi: Mltl<A>)
    requires
        Mltl::Future(a, b, Box::new(phi)) == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is Future && t->Future_1 == a && t->Future_2 == b
            && phi == mltl_parse_tree_to_mltl_spec(*t->Future_3),
{
}

/// `φ U_m[a,b] ψ = mltl_parse_tree_to_mltl T ⟹ ∃data φT ψT. T = Until_e data φT a b ψT ∧ …`
pub proof fn mltl_parse_tree_until_inv<A, B>(t: MltlParseTree<A, B>, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>)
    requires
        Mltl::Until(Box::new(phi), a, b, Box::new(psi)) == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is Until && t->Until_2 == a && t->Until_3 == b
            && phi == mltl_parse_tree_to_mltl_spec(*t->Until_1)
            && psi == mltl_parse_tree_to_mltl_spec(*t->Until_4),
{
}

/// `φ R_m[a,b] ψ = mltl_parse_tree_to_mltl T ⟹ ∃data φT ψT. T = Release_e data φT a b ψT ∧ …`
pub proof fn mltl_parse_tree_release_inv<A, B>(t: MltlParseTree<A, B>, phi: Mltl<A>, a: usize, b: usize, psi: Mltl<A>)
    requires
        Mltl::Release(Box::new(phi), a, b, Box::new(psi)) == mltl_parse_tree_to_mltl_spec(t),
    ensures
        t is Release && t->Release_2 == a && t->Release_3 == b
            && phi == mltl_parse_tree_to_mltl_spec(*t->Release_1)
            && psi == mltl_parse_tree_to_mltl_spec(*t->Release_4),
{
}

/// Not in Isabelle: changing the data does not change the formula.
pub proof fn mltl_parse_tree_to_mltl_map_aux_data<A, B, C>(t: MltlParseTree<A, B>, f: spec_fn(B) -> C)
    ensures
        mltl_parse_tree_to_mltl_spec(map_aux_data(t, f)) == mltl_parse_tree_to_mltl_spec(t),
    decreases t,
{
    match t {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
        MltlParseTree::Not(_, g) | MltlParseTree::Future(_, _, _, g) | MltlParseTree::Global(_, _, _, g) =>
            mltl_parse_tree_to_mltl_map_aux_data(*g, f),
        MltlParseTree::And(_, g, h) | MltlParseTree::Or(_, g, h) | MltlParseTree::Until(_, g, _, _, h)
        | MltlParseTree::Release(_, g, _, _, h) => {
            mltl_parse_tree_to_mltl_map_aux_data(*g, f);
            mltl_parse_tree_to_mltl_map_aux_data(*h, f);
        },
    }
}

// ---------------------------------------------------------------------------
// Executable (usize atoms, D19; any data type)
// ---------------------------------------------------------------------------

/// Executable `mltl_parse_tree_to_mltl`.
pub fn mltl_parse_tree_to_mltl<B>(t: &MltlParseTree<usize, B>) -> (r: Mltl<usize>)
    ensures
        r == mltl_parse_tree_to_mltl_spec(*t),
    decreases t,
{
    match t {
        MltlParseTree::True(_) => Mltl::True,
        MltlParseTree::False(_) => Mltl::False,
        MltlParseTree::Prop(_, p) => Mltl::Prop(*p),
        MltlParseTree::Not(_, g) => Mltl::Not(Box::new(mltl_parse_tree_to_mltl(g))),
        MltlParseTree::And(_, g, h) =>
            Mltl::And(Box::new(mltl_parse_tree_to_mltl(g)), Box::new(mltl_parse_tree_to_mltl(h))),
        MltlParseTree::Or(_, g, h) =>
            Mltl::Or(Box::new(mltl_parse_tree_to_mltl(g)), Box::new(mltl_parse_tree_to_mltl(h))),
        MltlParseTree::Future(_, a, b, g) => Mltl::Future(*a, *b, Box::new(mltl_parse_tree_to_mltl(g))),
        MltlParseTree::Global(_, a, b, g) => Mltl::Global(*a, *b, Box::new(mltl_parse_tree_to_mltl(g))),
        MltlParseTree::Until(_, g, a, b, h) =>
            Mltl::Until(Box::new(mltl_parse_tree_to_mltl(g)), *a, *b, Box::new(mltl_parse_tree_to_mltl(h))),
        MltlParseTree::Release(_, g, a, b, h) =>
            Mltl::Release(Box::new(mltl_parse_tree_to_mltl(g)), *a, *b, Box::new(mltl_parse_tree_to_mltl(h))),
    }
}

} // verus!
