//! The union theorem: on traces of length at least `wpd`, a formula holds
//! exactly when some formula of its partition holds.
//!
//! Mirrors `MLTL_Language_Partition_Proof.thy`, subsection "Union Theorem".
//! Isabelle proves the two directions separately, by induction on `k` with a
//! case split over all operators (~1700 lines). Here one induction proves
//! the equivalence; each operator case combines a lifting lemma with a
//! partition lemma from `blocks.rs`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use mltl_core::parse_tree::*;
use crate::ext::*;
use crate::composition::*;
use crate::algorithm::*;
use crate::lists::*;
use crate::blocks::*;
use crate::structure::*;

verus! {

pub proof fn agrees_on_sub<A>(d: Seq<MltlExt<A>>, x: MltlExt<A>, pi: Seq<Set<A>>, lo: nat, hi: nat, lo2: nat, hi2: nat)
    requires
        agrees_on(d, x, pi, lo, hi),
        lo <= lo2,
        hi2 <= hi,
    ensures
        agrees_on(d, x, pi, lo2, hi2),
{
}

/// `LP_mltl_aux φ k` holds exactly when `φ` does, on long enough traces
/// (Isabelle: `LP_mltl_aux_language_union`, the conjunction of
/// `LP_mltl_aux_language_union_forward` and `_converse`).
pub proof fn LP_mltl_aux_language_union<A>(phi: MltlExt<A>, k: nat, pi: Seq<Set<A>>)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        pi.len() >= wpd_mltl(to_mltl(phi)),
        is_composition_MLTL(phi),
    ensures
        semantics_mltl_ext(pi, phi) == sat_some(LP_mltl_aux_spec(phi, k), pi),
    decreases k, 0nat,
{
    let init = choose|init: MltlExt<A>| phi == convert_nnf_ext_spec(init);
    convert_nnf_ext_not_is_prop(init);
    lemma_drop_zero(pi);
    if k == 0 || phi is True || phi is False || phi is Prop || phi is Not {
        sat_some_single(phi, pi);
    } else {
        let k1 = (k - 1) as nat;
        match phi {
            MltlParseTree::And(_, x, y) => {
                let dx = lp_child_agrees(*x, k1, pi, 0, 0);
                let dy = lp_child_agrees(*y, k1, pi, 0, 0);
                And_mltl_list_sat(dx, dy, pi);
            },
            MltlParseTree::Or(_, x, y) => {
                let dx = lp_child_agrees(*x, k1, pi, 0, 0);
                let dy = lp_child_agrees(*y, k1, pi, 0, 0);
                let x_ = not_mltl_ext(*x);
                let y_ = not_mltl_ext(*y);
                sat_some_single(x_, pi);
                sat_some_single(y_, pi);
                And_mltl_list_sat(dx, dy, pi);
                And_mltl_list_sat(seq![x_], dy, pi);
                And_mltl_list_sat(dx, seq![y_], pi);
                sat_some_append(And_mltl_list_spec(dx, dy), And_mltl_list_spec(seq![x_], dy), pi);
                sat_some_append(And_mltl_list_spec(dx, dy) + And_mltl_list_spec(seq![x_], dy), And_mltl_list_spec(dx, seq![y_]), pi);
            },
            MltlParseTree::Global(l, a, b, x) => {
                wpd_geq_one(to_mltl(*x));
                let dx = lp_child_agrees(*x, k1, pi, a as nat, b as nat);
                if dx.len() <= 1 {
                    sat_some_single(phi, pi);
                } else {
                    Global_mltl_decomp_sat(dx, a, nat_sub(b as nat, a as nat), l, *x, pi);
                }
            },
            MltlParseTree::Future(l, a, b, x) => {
                wpd_geq_one(to_mltl(*x));
                let dx = lp_child_agrees(*x, k1, pi, a as nat, b as nat);
                lp_future_union(l, a, b, *x, dx, pi);
                assert(LP_mltl_aux_spec(phi, k) == lp_future_list(l, a, b, *x, dx));
            },
            MltlParseTree::Until(l, x, a, b, y) => {
                wpd_geq_one(to_mltl(*y));
                let dy = lp_child_agrees(*y, k1, pi, a as nat, b as nat);
                lp_until_union(l, *x, a, b, *y, dy, pi);
                assert(LP_mltl_aux_spec(phi, k) == lp_until_list(l, *x, a, b, *y, dy));
            },
            MltlParseTree::Release(l, x, a, b, y) => {
                wpd_geq_one(to_mltl(*x));
                let dx = lp_child_agrees(*x, k1, pi, a as nat, b as nat);
                lp_release_union(l, *x, a, b, *y, dx, pi);
                assert(LP_mltl_aux_spec(phi, k) == lp_release_list(l, *x, a, b, *y, dx));
            },
            _ => {},
        }
    }
}

/// The induction hypothesis for a child `x`: on every suffix `drop π t`,
/// `lo ≤ t ≤ hi`, `LP_mltl_aux (convert_nnf_ext x) k` holds exactly when `x` does.
pub proof fn lp_child_agrees<A>(x: MltlExt<A>, k: nat, pi: Seq<Set<A>>, lo: nat, hi: nat) -> (d: Seq<MltlExt<A>>)
    requires
        intervals_welldef(to_mltl(x)),
        is_composition_MLTL(x),
        pi.len() >= hi + wpd_mltl(to_mltl(x)),
    ensures
        d == LP_mltl_aux_spec(convert_nnf_ext_spec(x), k),
        agrees_on(d, x, pi, lo, hi),
    decreases k, 1nat,
{
    let d = LP_mltl_aux_spec(convert_nnf_ext_spec(x), k);
    convert_nnf_ext_welldef(x);
    is_composition_convert_nnf_ext(x);
    convert_nnf_ext_preserves_wpd(x);
    assert forall|t: nat| lo <= t <= hi implies
        sat_some(d, #[trigger] drop(pi, t)) == semantics_mltl_ext(drop(pi, t), x) by {
        lemma_drop_len(pi, t);
        LP_mltl_aux_language_union(convert_nnf_ext_spec(x), k, drop(pi, t));
        convert_nnf_ext_semantics_at(drop(pi, t), x);
    }
    d
}

// ---------------------------------------------------------------------------
// The F, U, R cases
// ---------------------------------------------------------------------------

/// Some formula of `head ++ concat pieces` holds exactly when one of the
/// blocks `blk 0` (the head) or `blk (j+1)` (piece `j`) does.
pub proof fn head_concat_sat<A>(head: Seq<MltlExt<A>>, pieces: Seq<Seq<MltlExt<A>>>, pi: Seq<Set<A>>, blk: spec_fn(int) -> bool)
    requires
        sat_some(head, pi) == blk(0),
        forall|j: int| 0 <= j < pieces.len() ==> #[trigger] sat_some(pieces[j], pi) == blk(j + 1),
    ensures
        sat_some(head + concat(pieces), pi) == exists|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i),
{
    sat_some_append(head, concat(pieces), pi);
    sat_some_concat(pieces, pi);
    if exists|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i) {
        let i = choose|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i);
        if i > 0 {
            assert(sat_some(pieces[i - 1], pi));
        }
    }
    if exists|j: int| 0 <= j < pieces.len() && #[trigger] sat_some(pieces[j], pi) {
        let j = choose|j: int| 0 <= j < pieces.len() && #[trigger] sat_some(pieces[j], pi);
        assert(blk(j + 1));
    }
}

pub proof fn future_piece_sat<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, x: MltlExt<A>, dx: Seq<MltlExt<A>>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, s),
        0 <= i < l.len(),
        agrees_on(dx, x, pi, a as nat, b as nat),
        pi.len() > b,
    ensures
        i == 0 ==> sat_some(Future_mltl_list_spec(dx, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]), pi)
            == semantics_mltl_ext(pi, future_block(x, s, 0)),
        i > 0 ==> sat_some(LP_future_piece(dx, x, s, i), pi) == semantics_mltl_ext(pi, future_block(x, s, i)),
{
    block_bounds(a, b, l, s, i);
    let lo = s[i] as usize;
    let hi = (s[i + 1] - 1) as usize;
    let w = seq![(s[i + 1] - s[i]) as usize];
    Future_mltl_list_sat(dx, lo, hi, w, x, pi);
    if i > 0 {
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], not_mltl_ext(x));
        sat_some_single(g, pi);
        And_mltl_list_sat(seq![g], Future_mltl_list_spec(dx, lo, hi, w), pi);
        and_ext_semantics(g, future_mltl_ext(lo, hi, w, x), pi);
    }
}

pub proof fn until_piece_sat<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, x: MltlExt<A>, y: MltlExt<A>, dy: Seq<MltlExt<A>>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, s),
        0 <= i < l.len(),
        agrees_on(dy, y, pi, a as nat, b as nat),
        pi.len() > b,
    ensures
        i == 0 ==> sat_some(Until_mltl_list_spec(x, dy, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]), pi)
            == semantics_mltl_ext(pi, until_block(x, y, s, 0)),
        i > 0 ==> sat_some(LP_until_piece(x, dy, y, s, i), pi) == semantics_mltl_ext(pi, until_block(x, y, s, i)),
{
    block_bounds(a, b, l, s, i);
    let lo = s[i] as usize;
    let hi = (s[i + 1] - 1) as usize;
    let w = seq![(s[i + 1] - s[i]) as usize];
    Until_mltl_list_sat(x, dy, lo, hi, w, y, pi);
    if i > 0 {
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(x, not_mltl_ext(y)));
        sat_some_single(g, pi);
        And_mltl_list_sat(seq![g], Until_mltl_list_spec(x, dy, lo, hi, w), pi);
        and_ext_semantics(g, until_mltl_ext(x, lo, hi, w, y), pi);
    }
}

pub proof fn release_piece_sat<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, x: MltlExt<A>, y: MltlExt<A>, dx: Seq<MltlExt<A>>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, s),
        0 <= i < l.len(),
        agrees_on(dx, x, pi, a as nat, b as nat),
        pi.len() > b,
    ensures
        i == 0 ==> sat_some(Mighty_Release_mltl_list_spec(dx, y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]), pi)
            == semantics_mltl_ext(pi, release_block(x, y, s, 0)),
        i > 0 ==> sat_some(LP_release_piece(dx, x, y, s, i), pi) == semantics_mltl_ext(pi, release_block(x, y, s, i)),
{
    block_bounds(a, b, l, s, i);
    let lo = s[i] as usize;
    let hi = (s[i + 1] - 1) as usize;
    let w = seq![(s[i + 1] - s[i]) as usize];
    Mighty_Release_mltl_list_sat(dx, y, lo, hi, w, x, pi);
    if i > 0 {
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(not_mltl_ext(x), y));
        sat_some_single(g, pi);
        And_mltl_list_sat(seq![g], Mighty_Release_mltl_list_spec(dx, y, lo, hi, w), pi);
        and_ext_semantics(g, Mighty_Release_mltl_ext(x, y, lo, hi, w), pi);
    }
}

proof fn lp_future_union<A>(l: Seq<usize>, a: usize, b: usize, x: MltlExt<A>, dx: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        agrees_on(dx, x, pi, a as nat, b as nat),
        pi.len() > b,
    ensures
        sat_some(lp_future_list(l, a, b, x, dx), pi) == semantics_mltl_ext(pi, future_mltl_ext(a, b, l, x)),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let head = Future_mltl_list_spec(dx, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_future_piece(dx, x, s, j + 1));
    let blk = |i: int| semantics_mltl_ext(pi, future_block(x, s, i));
    future_piece_sat(a, b, l, s, x, dx, pi, 0);
    assert forall|j: int| 0 <= j < pieces.len() implies #[trigger] sat_some(pieces[j], pi) == blk(j + 1) by {
        future_piece_sat(a, b, l, s, x, dx, pi, j + 1);
    }
    head_concat_sat(head, pieces, pi, blk);
    future_partition(a, b, l, x, pi);
    assert(pieces.len() + 1 == l.len());
    if exists|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i) {
        let i = choose|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i);
        assert(semantics_mltl_ext(pi, future_block(x, s, i)));
    }
    if exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] future_block(x, s, i)) {
        let i = choose|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] future_block(x, s, i));
        assert(blk(i));
    }
}

proof fn lp_until_union<A>(l: Seq<usize>, x: MltlExt<A>, a: usize, b: usize, y: MltlExt<A>, dy: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        agrees_on(dy, y, pi, a as nat, b as nat),
        pi.len() > b,
    ensures
        sat_some(lp_until_list(l, x, a, b, y, dy), pi) == semantics_mltl_ext(pi, until_mltl_ext(x, a, b, l, y)),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let head = Until_mltl_list_spec(x, dy, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_until_piece(x, dy, y, s, j + 1));
    let blk = |i: int| semantics_mltl_ext(pi, until_block(x, y, s, i));
    until_piece_sat(a, b, l, s, x, y, dy, pi, 0);
    assert forall|j: int| 0 <= j < pieces.len() implies #[trigger] sat_some(pieces[j], pi) == blk(j + 1) by {
        until_piece_sat(a, b, l, s, x, y, dy, pi, j + 1);
    }
    head_concat_sat(head, pieces, pi, blk);
    until_partition(x, a, b, l, y, pi);
    assert(pieces.len() + 1 == l.len());
    if exists|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i) {
        let i = choose|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i);
        assert(semantics_mltl_ext(pi, until_block(x, y, s, i)));
    }
    if exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] until_block(x, y, s, i)) {
        let i = choose|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] until_block(x, y, s, i));
        assert(blk(i));
    }
}

proof fn lp_release_union<A>(l: Seq<usize>, x: MltlExt<A>, a: usize, b: usize, y: MltlExt<A>, dx: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        agrees_on(dx, x, pi, a as nat, b as nat),
        pi.len() > b,
    ensures
        sat_some(lp_release_list(l, x, a, b, y, dx), pi) == semantics_mltl_ext(pi, release_mltl_ext(x, a, b, l, y)),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let e0 = global_mltl_ext(a, b, l, and_mltl_ext(not_mltl_ext(x), y));
    let head = Mighty_Release_mltl_list_spec(dx, y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_release_piece(dx, x, y, s, j + 1));
    let blk = |i: int| semantics_mltl_ext(pi, release_block(x, y, s, i));
    release_piece_sat(a, b, l, s, x, y, dx, pi, 0);
    assert forall|j: int| 0 <= j < pieces.len() implies #[trigger] sat_some(pieces[j], pi) == blk(j + 1) by {
        release_piece_sat(a, b, l, s, x, y, dx, pi, j + 1);
    }
    head_concat_sat(head, pieces, pi, blk);
    sat_some_single(e0, pi);
    sat_some_append(seq![e0], head + concat(pieces), pi);
    assert(seq![e0] + head + concat(pieces) == seq![e0] + (head + concat(pieces)));
    release_partition(x, a, b, l, y, pi);
    assert(pieces.len() + 1 == l.len());
    if exists|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i) {
        let i = choose|i: int| 0 <= i < pieces.len() + 1 && #[trigger] blk(i);
        assert(semantics_mltl_ext(pi, release_block(x, y, s, i)));
    }
    if exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] release_block(x, y, s, i)) {
        let i = choose|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] release_block(x, y, s, i));
        assert(blk(i));
    }
}

// ---------------------------------------------------------------------------
// The theorems as Isabelle states them
// ---------------------------------------------------------------------------

/// `intervals_welldef (to_mltl φ) ⟹ ∃φ_init. φ = convert_nnf_ext φ_init ⟹ is_composition_MLTL φ ⟹
/// D = LP_mltl_aux φ k ⟹ π ⊨_c φ ⟹ length π ≥ wpd_mltl (to_mltl φ) ⟹ ∃ψ ∈ set D. π ⊨_c ψ`
pub proof fn LP_mltl_aux_language_union_forward<A>(phi: MltlExt<A>, k: nat, pi: Seq<Set<A>>)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        is_composition_MLTL(phi),
        semantics_mltl_ext(pi, phi),
        pi.len() >= wpd_mltl(to_mltl(phi)),
    ensures
        exists|psi: MltlExt<A>| LP_mltl_aux_spec(phi, k).contains(psi) && semantics_mltl_ext(pi, psi),
{
    LP_mltl_aux_language_union(phi, k, pi);
}

/// `… ⟹ length π ≥ wpd_mltl (to_mltl φ) ⟹ ψ ∈ set (LP_mltl_aux φ k) ⟹ π ⊨_c ψ ⟹ π ⊨_c φ`
pub proof fn LP_mltl_aux_language_union_converse<A>(phi: MltlExt<A>, k: nat, pi: Seq<Set<A>>, psi: MltlExt<A>)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        is_composition_MLTL(phi),
        pi.len() >= wpd_mltl(to_mltl(phi)),
        LP_mltl_aux_spec(phi, k).contains(psi),
        semantics_mltl_ext(pi, psi),
    ensures
        semantics_mltl_ext(pi, phi),
{
    LP_mltl_aux_language_union(phi, k, pi);
}

/// Theorem `LP_mltl_language_union_explicit`: for `length π ≥ wpd_mltl (to_mltl φ)`,
/// `π ⊨_c φ ⟷ (∃ψ ∈ set (LP_mltl φ k). π ⊨_m ψ)`.
pub proof fn LP_mltl_language_union_explicit<A>(phi: MltlExt<A>, k: nat, pi: Seq<Set<A>>)
    requires
        intervals_welldef(to_mltl(phi)),
        is_composition_MLTL(phi),
        pi.len() >= wpd_mltl(to_mltl(phi)),
    ensures
        semantics_mltl_ext(pi, phi)
            == exists|psi: Mltl<A>| LP_mltl_spec(phi, k).contains(psi) && semantics_mltl(pi, psi),
{
    let phi_n = convert_nnf_ext_spec(phi);
    let d = LP_mltl_aux_spec(phi_n, k);
    convert_nnf_ext_welldef(phi);
    is_composition_convert_nnf_ext(phi);
    convert_nnf_ext_preserves_wpd(phi);
    convert_nnf_ext_semantics_at(pi, phi);
    LP_mltl_aux_language_union(phi_n, k, pi);
    LP_mltl_aux_welldef_wpd(phi_n, k);
    if semantics_mltl_ext(pi, phi) {
        let x = choose|x: MltlExt<A>| d.contains(x) && semantics_mltl_ext(pi, x);
        LP_mltl_element(phi, k, to_mltl(convert_nnf_ext_spec(x)));
        convert_nnf_ext_semantics_at(pi, x);
        assert(LP_mltl_spec(phi, k).contains(to_mltl(convert_nnf_ext_spec(x))));
    }
    if exists|psi: Mltl<A>| LP_mltl_spec(phi, k).contains(psi) && semantics_mltl(pi, psi) {
        let psi = choose|psi: Mltl<A>| LP_mltl_spec(phi, k).contains(psi) && semantics_mltl(pi, psi);
        LP_mltl_element(phi, k, psi);
        let x = choose|x: MltlExt<A>| d.contains(x) && psi == to_mltl(convert_nnf_ext_spec(x));
        convert_nnf_ext_semantics_at(pi, x);
        assert(sat_some(d, pi));
    }
}

/// Theorem `LP_mltl_language_union`: with `r = wpd_mltl (to_mltl φ)`,
/// `language_mltl_r (to_mltl φ) r = (⋃ψ ∈ set (LP_mltl φ k). language_mltl_r ψ r)`.
pub proof fn LP_mltl_language_union<A>(phi: MltlExt<A>, k: nat, r: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        is_composition_MLTL(phi),
        r == wpd_mltl(to_mltl(phi)),
    ensures
        language_mltl_r(to_mltl(phi), r) == ISet::new(|pi: Seq<Set<A>>|
            exists|psi: Mltl<A>| LP_mltl_spec(phi, k).contains(psi) && language_mltl_r(psi, r).contains(pi)),
{
    let u = ISet::new(|pi: Seq<Set<A>>|
        exists|psi: Mltl<A>| LP_mltl_spec(phi, k).contains(psi) && language_mltl_r(psi, r).contains(pi));
    assert forall|pi: Seq<Set<A>>| language_mltl_r(to_mltl(phi), r).contains(pi) == u.contains(pi) by {
        if pi.len() >= r {
            LP_mltl_language_union_explicit(phi, k, pi);
            if exists|psi: Mltl<A>| LP_mltl_spec(phi, k).contains(psi) && semantics_mltl(pi, psi) {
                let psi = choose|psi: Mltl<A>| LP_mltl_spec(phi, k).contains(psi) && semantics_mltl(pi, psi);
                assert(language_mltl_r(psi, r).contains(pi));
            }
        }
    }
    assert(language_mltl_r(to_mltl(phi), r) =~= u);
}

} // verus!
