//! The disjointness theorems: on traces of length at least `wpd`, no two
//! different formulas of the partition hold together.
//!
//! Mirrors `MLTL_Language_Partition_Proof.thy`, subsections "Disjointedness
//! Theorem" and "Disjointedness Theorem (special case of k=1)". One
//! induction covers both: the case `k ≤ 1` (any compositions; every
//! recursive list then has one element) and the case of all-ones
//! compositions (any depth; every block is a single time step).
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
use crate::union::*;

verus! {

// ---------------------------------------------------------------------------
// Builders over a single time step
// ---------------------------------------------------------------------------

/// The lists built from `D` are disjoint if `D` has one element, or if the
/// interval is the single step `t` and `D` is disjoint at `t`.
pub open spec fn point_or_single<A>(d: Seq<MltlExt<A>>, lo: usize, hi: usize, pi: Seq<Set<A>>) -> bool {
    d.len() <= 1 || (lo == hi && pi.len() > lo && disjoint_on(d, drop(pi, lo as nat)))
}

pub proof fn Future_mltl_list_disjoint<A>(d: Seq<MltlExt<A>>, lo: usize, hi: usize, w: Seq<usize>, pi: Seq<Set<A>>)
    requires
        point_or_single(d, lo, hi, pi),
    ensures
        disjoint_on(Future_mltl_list_spec(d, lo, hi, w), pi),
{
    let fl = Future_mltl_list_spec(d, lo, hi, w);
    if d.len() <= 1 {
        disjoint_len_le1(fl, pi);
    } else {
        assert forall|p1: MltlExt<A>, p2: MltlExt<A>|
            fl.contains(p1) && fl.contains(p2) && p1 != p2 && semantics_mltl_ext(pi, p1)
            implies !semantics_mltl_ext(pi, p2) by {
            Future_mltl_list_member(d, lo, hi, w, p1);
            Future_mltl_list_member(d, lo, hi, w, p2);
            let y1 = choose|y: MltlExt<A>| d.contains(y) && p1 == future_mltl_ext(lo, hi, w, y);
            let y2 = choose|y: MltlExt<A>| d.contains(y) && p2 == future_mltl_ext(lo, hi, w, y);
            temporal_semantics(lo, hi, w, y1, y1, pi);
            temporal_semantics(lo, hi, w, y2, y2, pi);
            let t1 = choose|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(y1));
            assert(semantics_mltl_ext(drop(pi, lo as nat), y1));
            if semantics_mltl_ext(pi, p2) {
                let t2 = choose|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(y2));
                assert(semantics_mltl_ext(drop(pi, lo as nat), y2));
            }
        }
    }
}

pub proof fn Until_mltl_list_disjoint<A>(phi: MltlExt<A>, d: Seq<MltlExt<A>>, lo: usize, hi: usize, w: Seq<usize>, pi: Seq<Set<A>>)
    requires
        point_or_single(d, lo, hi, pi),
    ensures
        disjoint_on(Until_mltl_list_spec(phi, d, lo, hi, w), pi),
{
    let ul = Until_mltl_list_spec(phi, d, lo, hi, w);
    if d.len() <= 1 {
        disjoint_len_le1(ul, pi);
    } else {
        assert forall|p1: MltlExt<A>, p2: MltlExt<A>|
            ul.contains(p1) && ul.contains(p2) && p1 != p2 && semantics_mltl_ext(pi, p1)
            implies !semantics_mltl_ext(pi, p2) by {
            Until_mltl_list_member(phi, d, lo, hi, w, p1);
            Until_mltl_list_member(phi, d, lo, hi, w, p2);
            let y1 = choose|y: MltlExt<A>| d.contains(y) && p1 == until_mltl_ext(phi, lo, hi, w, y);
            let y2 = choose|y: MltlExt<A>| d.contains(y) && p2 == until_mltl_ext(phi, lo, hi, w, y);
            temporal_semantics(lo, hi, w, phi, y1, pi);
            temporal_semantics(lo, hi, w, phi, y2, pi);
            let t1 = choose|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(y1))
                && forall|j: nat| lo <= j < t ==> semantics_mltl(#[trigger] drop(pi, j), to_mltl(phi));
            assert(semantics_mltl_ext(drop(pi, lo as nat), y1));
            if semantics_mltl_ext(pi, p2) {
                let t2 = choose|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(y2))
                    && forall|j: nat| lo <= j < t ==> semantics_mltl(#[trigger] drop(pi, j), to_mltl(phi));
                assert(semantics_mltl_ext(drop(pi, lo as nat), y2));
            }
        }
    }
}

pub proof fn Mighty_Release_mltl_list_disjoint<A>(d: Seq<MltlExt<A>>, psi: MltlExt<A>, lo: usize, hi: usize, w: Seq<usize>, pi: Seq<Set<A>>)
    requires
        point_or_single(d, lo, hi, pi),
    ensures
        disjoint_on(Mighty_Release_mltl_list_spec(d, psi, lo, hi, w), pi),
{
    let ml = Mighty_Release_mltl_list_spec(d, psi, lo, hi, w);
    if d.len() <= 1 {
        disjoint_len_le1(ml, pi);
    } else {
        assert forall|p1: MltlExt<A>, p2: MltlExt<A>|
            ml.contains(p1) && ml.contains(p2) && p1 != p2 && semantics_mltl_ext(pi, p1)
            implies !semantics_mltl_ext(pi, p2) by {
            Mighty_Release_mltl_list_member(d, psi, lo, hi, w, p1);
            Mighty_Release_mltl_list_member(d, psi, lo, hi, w, p2);
            let y1 = choose|y: MltlExt<A>| d.contains(y) && p1 == Mighty_Release_mltl_ext(y, psi, lo, hi, w);
            let y2 = choose|y: MltlExt<A>| d.contains(y) && p2 == Mighty_Release_mltl_ext(y, psi, lo, hi, w);
            temporal_semantics(lo, hi, w, y1, psi, pi);
            temporal_semantics(lo, hi, w, y2, psi, pi);
            let t1 = choose|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(y1));
            assert(semantics_mltl_ext(drop(pi, lo as nat), y1));
            if semantics_mltl_ext(pi, p2) {
                let t2 = choose|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(y2));
                assert(semantics_mltl_ext(drop(pi, lo as nat), y2));
            }
        }
    }
}

pub proof fn Global_mltl_list_point_disjoint<A>(d: Seq<MltlExt<A>>, t: usize, w: Seq<usize>, pi: Seq<Set<A>>)
    requires
        pi.len() > t,
        disjoint_on(d, drop(pi, t as nat)),
    ensures
        disjoint_on(Global_mltl_list_spec(d, t, t, w), pi),
{
    let gl = Global_mltl_list_spec(d, t, t, w);
    assert forall|p1: MltlExt<A>, p2: MltlExt<A>|
        gl.contains(p1) && gl.contains(p2) && p1 != p2 && semantics_mltl_ext(pi, p1)
        implies !semantics_mltl_ext(pi, p2) by {
        Global_mltl_list_member(d, t, t, w, p1);
        Global_mltl_list_member(d, t, t, w, p2);
        let y1 = choose|y: MltlExt<A>| d.contains(y) && p1 == global_mltl_ext(t, t, w, y);
        let y2 = choose|y: MltlExt<A>| d.contains(y) && p2 == global_mltl_ext(t, t, w, y);
        global_point_semantics(t, w, y1, pi);
        global_point_semantics(t, w, y2, pi);
    }
}

pub proof fn Global_mltl_decomp_disjoint<A>(d: Seq<MltlExt<A>>, a: usize, len: nat, l: Seq<usize>, pi: Seq<Set<A>>)
    requires
        a + len <= usize::MAX,
        pi.len() > a + len,
        forall|t: nat| a <= t <= a + len ==> disjoint_on(d, #[trigger] drop(pi, t)),
    ensures
        disjoint_on(Global_mltl_decomp_spec(d, a, len, l), pi),
    decreases len,
{
    let t = (a + len) as usize;
    assert(disjoint_on(d, drop(pi, t as nat)));
    Global_mltl_list_point_disjoint(d, t, seq![1usize], pi);
    if len > 0 {
        Global_mltl_decomp_disjoint(d, a, (len - 1) as nat, l, pi);
        And_mltl_list_disjoint(Global_mltl_decomp_spec(d, a, (len - 1) as nat, l), Global_mltl_list_spec(d, t, t, seq![1usize]), pi);
    }
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

/// Disjoint blocks of which no two hold together form a disjoint list.
pub proof fn head_concat_disjoint<A>(head: Seq<MltlExt<A>>, pieces: Seq<Seq<MltlExt<A>>>, pi: Seq<Set<A>>, blk: spec_fn(int) -> bool)
    requires
        disjoint_on(head, pi),
        forall|j: int| 0 <= j < pieces.len() ==> disjoint_on(#[trigger] pieces[j], pi),
        sat_some(head, pi) == blk(0),
        forall|j: int| 0 <= j < pieces.len() ==> #[trigger] sat_some(pieces[j], pi) == blk(j + 1),
        forall|i: int, j: int| #![trigger blk(i), blk(j)] 0 <= i < j <= pieces.len() ==> !(blk(i) && blk(j)),
    ensures
        disjoint_on(head + concat(pieces), pi),
{
    assert forall|i: int, j: int| #![trigger pieces[i], pieces[j]]
        0 <= i < pieces.len() && 0 <= j < pieces.len() && i != j implies
        !(sat_some(pieces[i], pi) && sat_some(pieces[j], pi)) by {
        if i < j {
            assert(!(blk(i + 1) && blk(j + 1)));
        } else {
            assert(!(blk(j + 1) && blk(i + 1)));
        }
    }
    disjoint_concat(pieces, pi);
    sat_some_concat(pieces, pi);
    if sat_some(head, pi) && sat_some(concat(pieces), pi) {
        let j = choose|j: int| 0 <= j < pieces.len() && #[trigger] sat_some(pieces[j], pi);
        assert(!(blk(0) && blk(j + 1)));
    }
    disjoint_append(head, concat(pieces), pi);
}

/// All-ones compositions make every block a single step.
pub proof fn allones_blocks(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>)
    requires
        blocks_ok(a, b, l, s),
        is_composition_allones(nat_sub(b as nat, a as nat) + 1, l),
    ensures
        forall|i: int| 0 <= i < l.len() ==> #[trigger] s[i + 1] - 1 == s[i],
{
    assert forall|i: int| 0 <= i < l.len() implies #[trigger] s[i + 1] - 1 == s[i] by {
        assert(l[i] == 1);
    }
}

/// What the children must satisfy for the blocks to be disjoint.
pub open spec fn child_disjoint<A>(d: Seq<MltlExt<A>>, a: usize, b: usize, l: Seq<usize>, pi: Seq<Set<A>>) -> bool {
    d.len() <= 1 || (is_composition_allones(nat_sub(b as nat, a as nat) + 1, l)
        && forall|t: nat| a <= t <= b ==> disjoint_on(d, #[trigger] drop(pi, t)))
}

/// The child list is disjoint at the step `s_i` that forms block `i`.
proof fn block_point_or_single<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, d: Seq<MltlExt<A>>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, s),
        0 <= i < l.len(),
        pi.len() > b,
        child_disjoint(d, a, b, l, pi),
    ensures
        point_or_single(d, s[i] as usize, (s[i + 1] - 1) as usize, pi),
{
    block_bounds(a, b, l, s, i);
    if d.len() > 1 {
        allones_blocks(a, b, l, s);
        assert(disjoint_on(d, drop(pi, s[i] as nat)));
    }
}

#[verifier::spinoff_prover]
proof fn lp_future_disjoint<A>(l: Seq<usize>, a: usize, b: usize, x: MltlExt<A>, dx: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        agrees_on(dx, x, pi, a as nat, b as nat),
        pi.len() > b,
        child_disjoint(dx, a, b, l, pi),
    ensures
        disjoint_on(lp_future_list(l, a, b, x, dx), pi),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let head = Future_mltl_list_spec(dx, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_future_piece(dx, x, s, j + 1));
    let blk = |i: int| semantics_mltl_ext(pi, future_block(x, s, i));
    future_piece_sat(a, b, l, s, x, dx, pi, 0);
    block_point_or_single(a, b, l, s, dx, pi, 0);
    Future_mltl_list_disjoint(dx, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize], pi);
    assert forall|j: int| #![trigger pieces[j]] 0 <= j < pieces.len() implies sat_some(pieces[j], pi) == blk(j + 1)
        && disjoint_on(pieces[j], pi) by {
        let i = j + 1;
        future_piece_sat(a, b, l, s, x, dx, pi, i);
        block_point_or_single(a, b, l, s, dx, pi, i);
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], not_mltl_ext(x));
        let f = Future_mltl_list_spec(dx, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]);
        Future_mltl_list_disjoint(dx, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize], pi);
        disjoint_len_le1(seq![g], pi);
        And_mltl_list_disjoint(seq![g], f, pi);
    }
    assert forall|i: int, j: int| #![trigger blk(i), blk(j)] 0 <= i < j <= pieces.len() implies !(blk(i) && blk(j)) by {
        future_blocks_exclusive(a, b, l, x, pi, i, j);
    }
    head_concat_disjoint(head, pieces, pi, blk);
}

#[verifier::spinoff_prover]
proof fn lp_until_disjoint<A>(l: Seq<usize>, x: MltlExt<A>, a: usize, b: usize, y: MltlExt<A>, dy: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        agrees_on(dy, y, pi, a as nat, b as nat),
        pi.len() > b,
        child_disjoint(dy, a, b, l, pi),
    ensures
        disjoint_on(lp_until_list(l, x, a, b, y, dy), pi),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let head = Until_mltl_list_spec(x, dy, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_until_piece(x, dy, y, s, j + 1));
    let blk = |i: int| semantics_mltl_ext(pi, until_block(x, y, s, i));
    until_piece_sat(a, b, l, s, x, y, dy, pi, 0);
    block_point_or_single(a, b, l, s, dy, pi, 0);
    Until_mltl_list_disjoint(x, dy, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize], pi);
    assert forall|j: int| #![trigger pieces[j]] 0 <= j < pieces.len() implies sat_some(pieces[j], pi) == blk(j + 1)
        && disjoint_on(pieces[j], pi) by {
        let i = j + 1;
        until_piece_sat(a, b, l, s, x, y, dy, pi, i);
        block_point_or_single(a, b, l, s, dy, pi, i);
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(x, not_mltl_ext(y)));
        let f = Until_mltl_list_spec(x, dy, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]);
        Until_mltl_list_disjoint(x, dy, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize], pi);
        disjoint_len_le1(seq![g], pi);
        And_mltl_list_disjoint(seq![g], f, pi);
    }
    assert forall|i: int, j: int| #![trigger blk(i), blk(j)] 0 <= i < j <= pieces.len() implies !(blk(i) && blk(j)) by {
        until_blocks_exclusive(x, a, b, l, y, pi, i, j);
    }
    head_concat_disjoint(head, pieces, pi, blk);
}

#[verifier::spinoff_prover]
proof fn lp_release_disjoint<A>(l: Seq<usize>, x: MltlExt<A>, a: usize, b: usize, y: MltlExt<A>, dx: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        agrees_on(dx, x, pi, a as nat, b as nat),
        pi.len() > b,
        child_disjoint(dx, a, b, l, pi),
    ensures
        disjoint_on(lp_release_list(l, x, a, b, y, dx), pi),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let e0 = global_mltl_ext(a, b, l, and_mltl_ext(not_mltl_ext(x), y));
    let head = Mighty_Release_mltl_list_spec(dx, y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_release_piece(dx, x, y, s, j + 1));
    let blk = |i: int| semantics_mltl_ext(pi, release_block(x, y, s, i));
    release_piece_sat(a, b, l, s, x, y, dx, pi, 0);
    block_point_or_single(a, b, l, s, dx, pi, 0);
    Mighty_Release_mltl_list_disjoint(dx, y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize], pi);
    assert forall|j: int| #![trigger pieces[j]] 0 <= j < pieces.len() implies sat_some(pieces[j], pi) == blk(j + 1)
        && disjoint_on(pieces[j], pi) by {
        release_piece_sat(a, b, l, s, x, y, dx, pi, j + 1);
        release_piece_disjoint(a, b, l, s, x, y, dx, pi, j + 1);
    }
    assert forall|i: int, j: int| #![trigger blk(i), blk(j)] 0 <= i < j <= pieces.len() implies !(blk(i) && blk(j)) by {
        release_blocks_exclusive(x, a, b, l, y, pi, i, j);
    }
    head_concat_disjoint(head, pieces, pi, blk);
    head_concat_sat(head, pieces, pi, blk);
    let e0_sem = semantics_mltl_ext(pi, e0);
    assert forall|i: int| 0 <= i < pieces.len() + 1 implies !(e0_sem && #[trigger] blk(i)) by {
        release_blocks_exclusive(x, a, b, l, y, pi, -1, i);
    }
    single_head_disjoint(e0, head + concat(pieces), pi, blk, (pieces.len() + 1) as nat);
    assert(seq![e0] + head + concat(pieces) == seq![e0] + (head + concat(pieces)));
}

proof fn release_piece_disjoint<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, x: MltlExt<A>, y: MltlExt<A>, dx: Seq<MltlExt<A>>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, s),
        1 <= i < l.len(),
        pi.len() > b,
        child_disjoint(dx, a, b, l, pi),
    ensures
        disjoint_on(LP_release_piece(dx, x, y, s, i), pi),
{
    block_point_or_single(a, b, l, s, dx, pi, i);
    let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(not_mltl_ext(x), y));
    let f = Mighty_Release_mltl_list_spec(dx, y, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]);
    Mighty_Release_mltl_list_disjoint(dx, y, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize], pi);
    disjoint_len_le1(seq![g], pi);
    And_mltl_list_disjoint(seq![g], f, pi);
}

/// A single formula excluding every block of a disjoint list keeps it disjoint.
pub proof fn single_head_disjoint<A>(e0: MltlExt<A>, rest: Seq<MltlExt<A>>, pi: Seq<Set<A>>, blk: spec_fn(int) -> bool, m: nat)
    requires
        disjoint_on(rest, pi),
        sat_some(rest, pi) == exists|i: int| 0 <= i < m && #[trigger] blk(i),
        forall|i: int| 0 <= i < m ==> !(semantics_mltl_ext(pi, e0) && #[trigger] blk(i)),
    ensures
        disjoint_on(seq![e0] + rest, pi),
{
    sat_some_single(e0, pi);
    disjoint_len_le1(seq![e0], pi);
    if sat_some(seq![e0], pi) && sat_some(rest, pi) {
        let i = choose|i: int| 0 <= i < m && #[trigger] blk(i);
    }
    disjoint_append(seq![e0], rest, pi);
}

// ---------------------------------------------------------------------------
// Main induction
// ---------------------------------------------------------------------------

/// The compositions allow disjointness at depth `k`: all ones, or `k ≤ 1`.
pub open spec fn disjoint_ok<A>(phi: MltlExt<A>, k: nat) -> bool {
    is_composition_MLTL_allones(phi) || (k <= 1 && is_composition_MLTL(phi))
}

/// No two different formulas of `LP_mltl_aux φ k` hold together on a long
/// enough trace. Covers `LP_mltl_language_disjoint_aux_helper` (all ones)
/// and `LP_mltl_language_disjoint_aux_helper_k1` (`k = 1`).
pub proof fn LP_mltl_aux_disjoint<A>(phi: MltlExt<A>, k: nat, pi: Seq<Set<A>>)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        pi.len() >= wpd_mltl(to_mltl(phi)),
        disjoint_ok(phi, k),
    ensures
        disjoint_on(LP_mltl_aux_spec(phi, k), pi),
    decreases k, 0nat,
{
    let init = choose|init: MltlExt<A>| phi == convert_nnf_ext_spec(init);
    convert_nnf_ext_not_is_prop(init);
    lemma_drop_zero(pi);
    if is_composition_MLTL_allones(phi) {
        allones_implies_is_composition_MLTL(phi);
    }
    if k == 0 || phi is True || phi is False || phi is Prop || phi is Not {
        disjoint_len_le1(seq![phi], pi);
    } else {
        let k1 = (k - 1) as nat;
        match phi {
            MltlParseTree::And(_, x, y) => {
                let dx = lp_child_disjoint(*x, k1, pi, 0, 0);
                let dy = lp_child_disjoint(*y, k1, pi, 0, 0);
                And_mltl_list_disjoint(dx, dy, pi);
            },
            MltlParseTree::Or(_, x, y) => {
                let dx = lp_child_disjoint(*x, k1, pi, 0, 0);
                let dy = lp_child_disjoint(*y, k1, pi, 0, 0);
                lp_or_disjoint(*x, *y, dx, dy, pi);
            },
            MltlParseTree::Global(l, a, b, x) => {
                wpd_geq_one(to_mltl(*x));
                let dx = lp_child_disjoint(*x, k1, pi, a as nat, b as nat);
                if dx.len() <= 1 {
                    disjoint_len_le1(seq![phi], pi);
                } else {
                    Global_mltl_decomp_disjoint(dx, a, nat_sub(b as nat, a as nat), l, pi);
                }
            },
            MltlParseTree::Future(l, a, b, x) => {
                wpd_geq_one(to_mltl(*x));
                let dx = lp_child_disjoint(*x, k1, pi, a as nat, b as nat);
                lp_future_disjoint(l, a, b, *x, dx, pi);
                assert(LP_mltl_aux_spec(phi, k) == lp_future_list(l, a, b, *x, dx));
            },
            MltlParseTree::Until(l, x, a, b, y) => {
                wpd_geq_one(to_mltl(*y));
                let dy = lp_child_disjoint(*y, k1, pi, a as nat, b as nat);
                lp_until_disjoint(l, *x, a, b, *y, dy, pi);
                assert(LP_mltl_aux_spec(phi, k) == lp_until_list(l, *x, a, b, *y, dy));
            },
            MltlParseTree::Release(l, x, a, b, y) => {
                wpd_geq_one(to_mltl(*x));
                let dx = lp_child_disjoint(*x, k1, pi, a as nat, b as nat);
                lp_release_disjoint(l, *x, a, b, *y, dx, pi);
                assert(LP_mltl_aux_spec(phi, k) == lp_release_list(l, *x, a, b, *y, dx));
            },
            _ => {},
        }
    }
}

/// The induction hypothesis for a child `x`, at depth `k`: the union
/// property and disjointness at each `drop π t`, `lo ≤ t ≤ hi`; at depth 0
/// the list is `[convert_nnf_ext x]`.
proof fn lp_child_disjoint<A>(x: MltlExt<A>, k: nat, pi: Seq<Set<A>>, lo: nat, hi: nat) -> (d: Seq<MltlExt<A>>)
    requires
        intervals_welldef(to_mltl(x)),
        is_composition_MLTL_allones(x) || (k == 0 && is_composition_MLTL(x)),
        pi.len() >= hi + wpd_mltl(to_mltl(x)),
    ensures
        d == LP_mltl_aux_spec(convert_nnf_ext_spec(x), k),
        agrees_on(d, x, pi, lo, hi),
        forall|t: nat| lo <= t <= hi ==> disjoint_on(d, #[trigger] drop(pi, t)),
        k == 0 ==> d.len() == 1,
        d.len() > 1 ==> is_composition_MLTL_allones(x),
    decreases k, 1nat,
{
    if is_composition_MLTL_allones(x) {
        allones_implies_is_composition_MLTL(x);
        is_composition_allones_convert_nnf_ext(x);
    }
    let d = lp_child_agrees(x, k, pi, lo, hi);
    convert_nnf_ext_welldef(x);
    is_composition_convert_nnf_ext(x);
    convert_nnf_ext_preserves_wpd(x);
    assert forall|t: nat| lo <= t <= hi implies disjoint_on(d, #[trigger] drop(pi, t)) by {
        lemma_drop_len(pi, t);
        LP_mltl_aux_disjoint(convert_nnf_ext_spec(x), k, drop(pi, t));
    }
    d
}

proof fn lp_or_disjoint<A>(x: MltlExt<A>, y: MltlExt<A>, dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        agrees_on(dx, x, pi, 0, 0),
        agrees_on(dy, y, pi, 0, 0),
        disjoint_on(dx, drop(pi, 0)),
        disjoint_on(dy, drop(pi, 0)),
        drop(pi, 0) == pi,
    ensures
        disjoint_on(lp_or_list(x, y, dx, dy), pi),
{
    let x_ = not_mltl_ext(x);
    let y_ = not_mltl_ext(y);
    let p1 = And_mltl_list_spec(dx, dy);
    let p2 = And_mltl_list_spec(seq![x_], dy);
    let p3 = And_mltl_list_spec(dx, seq![y_]);
    assert(sat_some(dx, pi) == semantics_mltl_ext(pi, x));
    assert(sat_some(dy, pi) == semantics_mltl_ext(pi, y));
    disjoint_len_le1(seq![x_], pi);
    disjoint_len_le1(seq![y_], pi);
    sat_some_single(x_, pi);
    sat_some_single(y_, pi);
    And_mltl_list_disjoint(dx, dy, pi);
    And_mltl_list_disjoint(seq![x_], dy, pi);
    And_mltl_list_disjoint(dx, seq![y_], pi);
    And_mltl_list_sat(dx, dy, pi);
    And_mltl_list_sat(seq![x_], dy, pi);
    And_mltl_list_sat(dx, seq![y_], pi);
    disjoint_append(p1, p2, pi);
    sat_some_append(p1, p2, pi);
    disjoint_append(p1 + p2, p3, pi);
}

// ---------------------------------------------------------------------------
// The theorems as Isabelle states them
// ---------------------------------------------------------------------------

/// `intervals_welldef (to_mltl φ) ⟹ ∃φ_init. φ = convert_nnf_ext φ_init ⟹
/// is_composition_MLTL_allones φ ⟹ length π ≥ wpd_mltl (to_mltl φ) ⟹ D = set (LP_mltl_aux φ k) ⟹
/// ψ1 ∈ D ∧ ψ2 ∈ D ∧ ψ1 ≠ ψ2 ⟹ π ⊨_c ψ1 ⟹ π ⊨_c ψ2 ⟹ False`
pub proof fn LP_mltl_language_disjoint_aux_helper<A>(phi: MltlExt<A>, k: nat, pi: Seq<Set<A>>, psi1: MltlExt<A>, psi2: MltlExt<A>)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        is_composition_MLTL_allones(phi),
        pi.len() >= wpd_mltl(to_mltl(phi)),
        LP_mltl_aux_spec(phi, k).contains(psi1) && LP_mltl_aux_spec(phi, k).contains(psi2) && psi1 != psi2,
        semantics_mltl_ext(pi, psi1),
        semantics_mltl_ext(pi, psi2),
    ensures
        false,
{
    LP_mltl_aux_disjoint(phi, k, pi);
}

/// `LP_mltl_language_disjoint_aux_helper` for `k = 1` and any compositions.
pub proof fn LP_mltl_language_disjoint_aux_helper_k1<A>(phi: MltlExt<A>, pi: Seq<Set<A>>, psi1: MltlExt<A>, psi2: MltlExt<A>)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        is_composition_MLTL(phi),
        pi.len() >= wpd_mltl(to_mltl(phi)),
        LP_mltl_aux_spec(phi, 1).contains(psi1) && LP_mltl_aux_spec(phi, 1).contains(psi2) && psi1 != psi2,
        semantics_mltl_ext(pi, psi1),
        semantics_mltl_ext(pi, psi2),
    ensures
        false,
{
    LP_mltl_aux_disjoint(phi, 1, pi);
}

/// Language form of `LP_mltl_aux_disjoint`, for both admissible cases.
proof fn lp_aux_languages_disjoint<A>(phi: MltlExt<A>, k: nat, psi1: MltlExt<A>, psi2: MltlExt<A>, r: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        disjoint_ok(phi, k),
        LP_mltl_aux_spec(phi, k).contains(psi1) && LP_mltl_aux_spec(phi, k).contains(psi2) && psi1 != psi2,
        r >= wpd_mltl(to_mltl(phi)),
    ensures
        language_mltl_r(to_mltl(psi1), r).intersect(language_mltl_r(to_mltl(psi2), r)) == ISet::<Seq<Set<A>>>::empty(),
{
    assert forall|pi: Seq<Set<A>>| !language_mltl_r(to_mltl(psi1), r).intersect(language_mltl_r(to_mltl(psi2), r)).contains(pi) by {
        if language_mltl_r(to_mltl(psi1), r).contains(pi) && language_mltl_r(to_mltl(psi2), r).contains(pi) {
            LP_mltl_aux_disjoint(phi, k, pi);
            assert(semantics_mltl_ext(pi, psi1));
        }
    }
    assert(language_mltl_r(to_mltl(psi1), r).intersect(language_mltl_r(to_mltl(psi2), r)) =~= ISet::<Seq<Set<A>>>::empty());
}

/// `… ⟹ is_composition_MLTL_allones φ ⟹ D = set (LP_mltl_aux φ k) ⟹ ψ1 ∈ D ∧ ψ2 ∈ D ∧ ψ1 ≠ ψ2 ⟹
/// r ≥ wpd_mltl (to_mltl φ) ⟹ language_mltl_r (to_mltl ψ1) r ∩ language_mltl_r (to_mltl ψ2) r = {}`
pub proof fn LP_mltl_language_disjoint_aux<A>(phi: MltlExt<A>, psi1: MltlExt<A>, psi2: MltlExt<A>, k: nat, r: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        is_composition_MLTL_allones(phi),
        LP_mltl_aux_spec(phi, k).contains(psi1) && LP_mltl_aux_spec(phi, k).contains(psi2) && psi1 != psi2,
        r >= wpd_mltl(to_mltl(phi)),
    ensures
        language_mltl_r(to_mltl(psi1), r).intersect(language_mltl_r(to_mltl(psi2), r)) == ISet::<Seq<Set<A>>>::empty(),
{
    lp_aux_languages_disjoint(phi, k, psi1, psi2, r);
}

/// `LP_mltl_language_disjoint_aux` for `k = 1` and any compositions.
pub proof fn LP_mltl_language_disjoint_aux_k1<A>(phi: MltlExt<A>, psi1: MltlExt<A>, psi2: MltlExt<A>, r: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        is_composition_MLTL(phi),
        LP_mltl_aux_spec(phi, 1).contains(psi1) && LP_mltl_aux_spec(phi, 1).contains(psi2) && psi1 != psi2,
        r >= wpd_mltl(to_mltl(phi)),
    ensures
        language_mltl_r(to_mltl(psi1), r).intersect(language_mltl_r(to_mltl(psi2), r)) == ISet::<Seq<Set<A>>>::empty(),
{
    lp_aux_languages_disjoint(phi, 1, psi1, psi2, r);
}

/// `LP_mltl` version for both admissible cases.
proof fn lp_languages_disjoint<A>(phi: MltlExt<A>, k: nat, psi1: Mltl<A>, psi2: Mltl<A>, r: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        disjoint_ok(phi, k),
        LP_mltl_spec(phi, k).contains(psi1) && LP_mltl_spec(phi, k).contains(psi2) && psi1 != psi2,
        r >= wpd_mltl(to_mltl(phi)),
    ensures
        language_mltl_r(psi1, r).intersect(language_mltl_r(psi2, r)) == ISet::<Seq<Set<A>>>::empty(),
{
    let phi_n = convert_nnf_ext_spec(phi);
    let d = LP_mltl_aux_spec(phi_n, k);
    convert_nnf_ext_welldef(phi);
    convert_nnf_ext_preserves_wpd(phi);
    if is_composition_MLTL_allones(phi) {
        is_composition_allones_convert_nnf_ext(phi);
        allones_implies_is_composition_MLTL(phi);
    }
    is_composition_convert_nnf_ext(phi);
    LP_mltl_aux_welldef_wpd(phi_n, k);
    LP_mltl_element(phi, k, psi1);
    LP_mltl_element(phi, k, psi2);
    let x1 = choose|x: MltlExt<A>| d.contains(x) && psi1 == to_mltl(convert_nnf_ext_spec(x));
    let x2 = choose|x: MltlExt<A>| d.contains(x) && psi2 == to_mltl(convert_nnf_ext_spec(x));
    assert forall|pi: Seq<Set<A>>| !language_mltl_r(psi1, r).intersect(language_mltl_r(psi2, r)).contains(pi) by {
        if language_mltl_r(psi1, r).contains(pi) && language_mltl_r(psi2, r).contains(pi) {
            convert_nnf_ext_semantics_at(pi, x1);
            convert_nnf_ext_semantics_at(pi, x2);
            LP_mltl_aux_disjoint(phi_n, k, pi);
            assert(semantics_mltl_ext(pi, x1) && semantics_mltl_ext(pi, x2) && x1 != x2);
        }
    }
    assert(language_mltl_r(psi1, r).intersect(language_mltl_r(psi2, r)) =~= ISet::<Seq<Set<A>>>::empty());
}

/// Theorem `LP_mltl_language_disjoint`: with all-ones compositions, different
/// formulas of `LP_mltl φ k` have disjoint languages (traces of length `≥ r ≥ wpd`).
pub proof fn LP_mltl_language_disjoint<A>(phi: MltlExt<A>, psi1: Mltl<A>, psi2: Mltl<A>, k: nat, r: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        is_composition_MLTL_allones(phi),
        LP_mltl_spec(phi, k).contains(psi1) && LP_mltl_spec(phi, k).contains(psi2) && psi1 != psi2,
        r >= wpd_mltl(to_mltl(phi)),
    ensures
        language_mltl_r(psi1, r).intersect(language_mltl_r(psi2, r)) == ISet::<Seq<Set<A>>>::empty(),
{
    lp_languages_disjoint(phi, k, psi1, psi2, r);
}

/// Theorem `LP_mltl_language_disjoint_k1`: with any compositions, different
/// formulas of `LP_mltl φ 1` have disjoint languages.
pub proof fn LP_mltl_language_disjoint_k1<A>(phi: MltlExt<A>, psi1: Mltl<A>, psi2: Mltl<A>, r: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        is_composition_MLTL(phi),
        LP_mltl_spec(phi, 1).contains(psi1) && LP_mltl_spec(phi, 1).contains(psi2) && psi1 != psi2,
        r >= wpd_mltl(to_mltl(phi)),
    ensures
        language_mltl_r(psi1, r).intersect(language_mltl_r(psi2, r)) == ISet::<Seq<Set<A>>>::empty(),
{
    lp_languages_disjoint(phi, 1, psi1, psi2, r);
}

} // verus!
