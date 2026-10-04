//! Syntactic facts about the output of `LP_mltl_aux`: well-defined
//! intervals, the `wpd` bound, non-emptiness, NNF, and `Ands_mltl_ext`.
//!
//! Mirrors `MLTL_Language_Partition_Proof.thy`, sections "MLTL Decomposition
//! Lemmas" and "Helper Lemmas" (`LP_mltl_aux_intervals_welldef`,
//! `LP_mltl_aux_wpd`, `LP_mltl_aux_nonempty`, `in_Global_mltl_decomp*`, …).
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use mltl_core::parse_tree::*;
use crate::ext::*;
use crate::composition::*;
use crate::algorithm::*;
use crate::lists::*;
use crate::blocks::*;

verus! {

/// Every formula of `D` has well-defined intervals.
pub open spec fn all_welldef<A>(d: Seq<MltlExt<A>>) -> bool {
    forall|psi: MltlExt<A>| d.contains(psi) ==> intervals_welldef(#[trigger] to_mltl(psi))
}

/// Every formula of `D` has `wpd ≤ n`.
pub open spec fn all_wpd_le<A>(d: Seq<MltlExt<A>>, n: nat) -> bool {
    forall|psi: MltlExt<A>| d.contains(psi) ==> wpd_mltl(#[trigger] to_mltl(psi)) <= n
}

/// Every formula of `D` has well-defined intervals and `wpd ≤ n`.
pub open spec fn all_ok<A>(d: Seq<MltlExt<A>>, n: nat) -> bool {
    all_welldef(d) && all_wpd_le(d, n)
}

// ---------------------------------------------------------------------------
// Builders keep intervals well defined and wpd bounded
// ---------------------------------------------------------------------------

pub proof fn ok_mono<A>(d: Seq<MltlExt<A>>, n: nat, m: nat)
    requires
        all_ok(d, n),
        n <= m,
    ensures
        all_ok(d, m),
{
}

pub proof fn ok_single<A>(phi: MltlExt<A>)
    requires
        intervals_welldef(to_mltl(phi)),
    ensures
        all_ok(seq![phi], wpd_mltl(to_mltl(phi))),
{
    assert forall|psi: MltlExt<A>| seq![phi].contains(psi) implies psi == phi by {
        let i = choose|i: int| 0 <= i < 1 && seq![phi][i] == psi;
    }
}

pub proof fn ok_append<A>(d: Seq<MltlExt<A>>, e: Seq<MltlExt<A>>, n: nat)
    requires
        all_ok(d, n),
        all_ok(e, n),
    ensures
        all_ok(d + e, n),
{
    assert forall|psi: MltlExt<A>| (d + e).contains(psi) implies d.contains(psi) || e.contains(psi) by {
        list_concat_set_union(d, e, psi);
    }
}

pub proof fn ok_concat<A>(xss: Seq<Seq<MltlExt<A>>>, n: nat)
    requires
        forall|j: int| 0 <= j < xss.len() ==> all_ok(#[trigger] xss[j], n),
    ensures
        all_ok(concat(xss), n),
{
    assert forall|psi: MltlExt<A>| #[trigger] concat(xss).contains(psi) implies
        exists|j: int| 0 <= j < xss.len() && #[trigger] xss[j].contains(psi) by {
        concat_member(xss, psi);
    }
}

pub proof fn ok_and_list<A>(d: Seq<MltlExt<A>>, e: Seq<MltlExt<A>>, n: nat, m: nat)
    requires
        all_ok(d, n),
        all_ok(e, m),
    ensures
        all_ok(And_mltl_list_spec(d, e), max_nat(n, m)),
{
    assert forall|psi: MltlExt<A>| And_mltl_list_spec(d, e).contains(psi) implies
        intervals_welldef(#[trigger] to_mltl(psi)) && wpd_mltl(to_mltl(psi)) <= max_nat(n, m) by {
        let r = And_mltl_list_member_forward(d, e, psi);
        assert(to_mltl(r.0) == to_mltl(r.0) && wpd_mltl(to_mltl(r.0)) <= n && wpd_mltl(to_mltl(r.1)) <= m);
    }
}

pub proof fn ok_global_list<A>(d: Seq<MltlExt<A>>, lo: usize, hi: usize, w: Seq<usize>, n: nat)
    requires
        all_ok(d, n),
        lo <= hi,
    ensures
        all_ok(Global_mltl_list_spec(d, lo, hi, w), (hi + n) as nat),
{
    assert forall|psi: MltlExt<A>| Global_mltl_list_spec(d, lo, hi, w).contains(psi) implies
        intervals_welldef(#[trigger] to_mltl(psi)) && wpd_mltl(to_mltl(psi)) <= hi + n by {
        Global_mltl_list_member(d, lo, hi, w, psi);
        let x = choose|x: MltlExt<A>| d.contains(x) && psi == global_mltl_ext(lo, hi, w, x);
        assert(intervals_welldef(to_mltl(x)) && wpd_mltl(to_mltl(x)) <= n);
    }
}

pub proof fn ok_future_list<A>(d: Seq<MltlExt<A>>, lo: usize, hi: usize, w: Seq<usize>, n: nat)
    requires
        all_ok(d, n),
        lo <= hi,
    ensures
        all_ok(Future_mltl_list_spec(d, lo, hi, w), (hi + n) as nat),
{
    assert forall|psi: MltlExt<A>| Future_mltl_list_spec(d, lo, hi, w).contains(psi) implies
        intervals_welldef(#[trigger] to_mltl(psi)) && wpd_mltl(to_mltl(psi)) <= hi + n by {
        Future_mltl_list_member(d, lo, hi, w, psi);
        let x = choose|x: MltlExt<A>| d.contains(x) && psi == future_mltl_ext(lo, hi, w, x);
        assert(intervals_welldef(to_mltl(x)) && wpd_mltl(to_mltl(x)) <= n);
    }
}

pub proof fn ok_until_list<A>(phi: MltlExt<A>, d: Seq<MltlExt<A>>, lo: usize, hi: usize, w: Seq<usize>, n: nat)
    requires
        all_ok(d, n),
        intervals_welldef(to_mltl(phi)),
        lo <= hi,
    ensures
        all_ok(Until_mltl_list_spec(phi, d, lo, hi, w), (hi + max_nat(wpd_mltl(to_mltl(phi)), n)) as nat),
{
    assert forall|psi: MltlExt<A>| Until_mltl_list_spec(phi, d, lo, hi, w).contains(psi) implies
        intervals_welldef(#[trigger] to_mltl(psi)) && wpd_mltl(to_mltl(psi)) <= hi + max_nat(wpd_mltl(to_mltl(phi)), n) by {
        Until_mltl_list_member(phi, d, lo, hi, w, psi);
        let x = choose|x: MltlExt<A>| d.contains(x) && psi == until_mltl_ext(phi, lo, hi, w, x);
        assert(intervals_welldef(to_mltl(x)) && wpd_mltl(to_mltl(x)) <= n);
    }
}

pub proof fn ok_mighty_release_list<A>(d: Seq<MltlExt<A>>, psi: MltlExt<A>, lo: usize, hi: usize, w: Seq<usize>, n: nat)
    requires
        all_ok(d, n),
        intervals_welldef(to_mltl(psi)),
        lo <= hi,
    ensures
        all_ok(Mighty_Release_mltl_list_spec(d, psi, lo, hi, w), (hi + max_nat(n, wpd_mltl(to_mltl(psi)))) as nat),
{
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 2);
    reveal_with_fuel(intervals_welldef, 2);
    reveal_with_fuel(wpd_mltl, 2);
    assert forall|e: MltlExt<A>| Mighty_Release_mltl_list_spec(d, psi, lo, hi, w).contains(e) implies
        intervals_welldef(#[trigger] to_mltl(e)) && wpd_mltl(to_mltl(e)) <= hi + max_nat(n, wpd_mltl(to_mltl(psi))) by {
        Mighty_Release_mltl_list_member(d, psi, lo, hi, w, e);
        let x = choose|x: MltlExt<A>| d.contains(x) && e == Mighty_Release_mltl_ext(x, psi, lo, hi, w);
        assert(intervals_welldef(to_mltl(x)) && wpd_mltl(to_mltl(x)) <= n);
    }
}

pub proof fn Global_mltl_decomp_ok<A>(d: Seq<MltlExt<A>>, a: usize, len: nat, l: Seq<usize>, n: nat)
    requires
        all_ok(d, n),
        a + len <= usize::MAX,
    ensures
        all_ok(Global_mltl_decomp_spec(d, a, len, l), (a + len + n) as nat),
    decreases len,
{
    let t = (a + len) as usize;
    ok_global_list(d, t, t, seq![1usize], n);
    if len > 0 {
        let prev = Global_mltl_decomp_spec(d, a, (len - 1) as nat, l);
        Global_mltl_decomp_ok(d, a, (len - 1) as nat, l, n);
        let g = Global_mltl_list_spec(d, t, t, seq![1usize]);
        ok_and_list(prev, g, (a + (len - 1) + n) as nat, (t + n) as nat);
    }
}

// ---------------------------------------------------------------------------
// Main structural lemmas
// ---------------------------------------------------------------------------

/// Stronger form of `LP_mltl_aux_intervals_welldef` and `LP_mltl_aux_wpd`
/// (no NNF assumption needed): every output formula has well-defined
/// intervals and `wpd` at most that of the input.
pub proof fn LP_mltl_aux_welldef_wpd<A>(phi: MltlExt<A>, k: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        is_composition_MLTL(phi),
    ensures
        all_ok(LP_mltl_aux_spec(phi, k), wpd_mltl(to_mltl(phi))),
    decreases k, 0nat,
{
    if k == 0 || phi is True || phi is False || phi is Prop || phi is Not {
        ok_single(phi);
        assert(all_ok(Seq::<MltlExt<A>>::empty(), 0));
    } else {
        let k1 = (k - 1) as nat;
        match phi {
            MltlParseTree::And(_, x, y) => {
                let dx = lp_child_ok(*x, k1);
                let dy = lp_child_ok(*y, k1);
                ok_and_list(dx, dy, wpd_mltl(to_mltl(*x)), wpd_mltl(to_mltl(*y)));
            },
            MltlParseTree::Or(_, x, y) => {
                let dx = lp_child_ok(*x, k1);
                let dy = lp_child_ok(*y, k1);
                lp_or_ok(*x, *y, dx, dy);
            },
            MltlParseTree::Global(l, a, b, x) => {
                let dx = lp_child_ok(*x, k1);
                if dx.len() > 1 {
                    Global_mltl_decomp_ok(dx, a, nat_sub(b as nat, a as nat), l, wpd_mltl(to_mltl(*x)));
                } else {
                    ok_single(phi);
                }
            },
            MltlParseTree::Future(l, a, b, x) => {
                let dx = lp_child_ok(*x, k1);
                lp_future_ok(l, a, b, *x, dx);
                assert(LP_mltl_aux_spec(phi, k) == lp_future_list(l, a, b, *x, dx));
            },
            MltlParseTree::Until(l, x, a, b, y) => {
                let dy = lp_child_ok(*y, k1);
                lp_until_ok(l, *x, a, b, *y, dy);
                assert(LP_mltl_aux_spec(phi, k) == lp_until_list(l, *x, a, b, *y, dy));
            },
            MltlParseTree::Release(l, x, a, b, y) => {
                let dx = lp_child_ok(*x, k1);
                lp_release_ok(l, *x, a, b, *y, dx);
                assert(LP_mltl_aux_spec(phi, k) == lp_release_list(l, *x, a, b, *y, dx));
            },
            _ => {},
        }
    }
}

/// The recursive call on a child: `LP_mltl_aux (convert_nnf_ext x) k`.
proof fn lp_child_ok<A>(x: MltlExt<A>, k: nat) -> (d: Seq<MltlExt<A>>)
    requires
        intervals_welldef(to_mltl(x)),
        is_composition_MLTL(x),
    ensures
        d == LP_mltl_aux_spec(convert_nnf_ext_spec(x), k),
        all_ok(d, wpd_mltl(to_mltl(x))),
    decreases k, 1nat,
{
    convert_nnf_ext_welldef(x);
    is_composition_convert_nnf_ext(x);
    convert_nnf_ext_preserves_wpd(x);
    LP_mltl_aux_welldef_wpd(convert_nnf_ext_spec(x), k);
    LP_mltl_aux_spec(convert_nnf_ext_spec(x), k)
}

/// The `Or` case of `LP_mltl_aux`, given the children's lists.
pub open spec fn lp_or_list<A>(x: MltlExt<A>, y: MltlExt<A>, dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>) -> Seq<MltlExt<A>> {
    And_mltl_list_spec(dx, dy) + And_mltl_list_spec(seq![not_mltl_ext(x)], dy) + And_mltl_list_spec(dx, seq![not_mltl_ext(y)])
}

/// The `F` case of `LP_mltl_aux`, given the child's list.
pub open spec fn lp_future_list<A>(l: Seq<usize>, a: usize, b: usize, x: MltlExt<A>, dx: Seq<MltlExt<A>>) -> Seq<MltlExt<A>> {
    let s = interval_times(a as nat, l);
    Future_mltl_list_spec(dx, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize])
        + concat(Seq::new(nat_sub(l.len(), 1), |j: int| LP_future_piece(dx, x, s, j + 1)))
}

/// The `U` case of `LP_mltl_aux`, given the list of the right operand.
pub open spec fn lp_until_list<A>(l: Seq<usize>, x: MltlExt<A>, a: usize, b: usize, y: MltlExt<A>, dy: Seq<MltlExt<A>>) -> Seq<MltlExt<A>> {
    let s = interval_times(a as nat, l);
    Until_mltl_list_spec(x, dy, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize])
        + concat(Seq::new(nat_sub(l.len(), 1), |j: int| LP_until_piece(x, dy, y, s, j + 1)))
}

/// The `R` case of `LP_mltl_aux`, given the list of the left operand.
pub open spec fn lp_release_list<A>(l: Seq<usize>, x: MltlExt<A>, a: usize, b: usize, y: MltlExt<A>, dx: Seq<MltlExt<A>>) -> Seq<MltlExt<A>> {
    let s = interval_times(a as nat, l);
    seq![global_mltl_ext(a, b, l, and_mltl_ext(not_mltl_ext(x), y))]
        + Mighty_Release_mltl_list_spec(dx, y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize])
        + concat(Seq::new(nat_sub(l.len(), 1), |j: int| LP_release_piece(dx, x, y, s, j + 1)))
}

proof fn lp_or_ok<A>(x: MltlExt<A>, y: MltlExt<A>, dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>)
    requires
        intervals_welldef(to_mltl(x)),
        intervals_welldef(to_mltl(y)),
        all_ok(dx, wpd_mltl(to_mltl(x))),
        all_ok(dy, wpd_mltl(to_mltl(y))),
    ensures
        all_ok(lp_or_list(x, y, dx, dy), max_nat(wpd_mltl(to_mltl(x)), wpd_mltl(to_mltl(y)))),
{
    let nx = wpd_mltl(to_mltl(x));
    let ny = wpd_mltl(to_mltl(y));
    let n = max_nat(nx, ny);
    let x_ = not_mltl_ext(x);
    let y_ = not_mltl_ext(y);
    assert(to_mltl(x_) == Mltl::Not(Box::new(to_mltl(x))));
    assert(to_mltl(y_) == Mltl::Not(Box::new(to_mltl(y))));
    ok_single(x_);
    ok_single(y_);
    ok_and_list(dx, dy, nx, ny);
    ok_and_list(seq![x_], dy, nx, ny);
    ok_and_list(dx, seq![y_], nx, ny);
    ok_append(And_mltl_list_spec(dx, dy), And_mltl_list_spec(seq![x_], dy), n);
    ok_append(And_mltl_list_spec(dx, dy) + And_mltl_list_spec(seq![x_], dy), And_mltl_list_spec(dx, seq![y_]), n);
}

/// A `G[s_0, s_i - 1] body` part of a block, with `wpd ≤ b + wpd body`.
proof fn ok_block_global<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, i: int, body: MltlExt<A>)
    requires
        blocks_ok(a, b, l, s),
        1 <= i < l.len(),
        intervals_welldef(to_mltl(body)),
    ensures
        all_ok(seq![global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], body)],
            (b + wpd_mltl(to_mltl(body))) as nat),
{
    block_bounds(a, b, l, s, i);
    let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], body);
    ok_single(g);
    ok_mono(seq![g], wpd_mltl(to_mltl(g)), (b + wpd_mltl(to_mltl(body))) as nat);
}

#[verifier::spinoff_prover]
proof fn lp_future_ok<A>(l: Seq<usize>, a: usize, b: usize, x: MltlExt<A>, dx: Seq<MltlExt<A>>)
    requires
        intervals_welldef(to_mltl(future_mltl_ext(a, b, l, x))),
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        all_ok(dx, wpd_mltl(to_mltl(x))),
    ensures
        all_ok(lp_future_list(l, a, b, x, dx), wpd_mltl(to_mltl(future_mltl_ext(a, b, l, x)))),
{
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
    reveal_with_fuel(wpd_mltl, 3);
    reveal_with_fuel(intervals_welldef, 3);
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let n = wpd_mltl(to_mltl(x));
    let bn = (b + n) as nat;
    assert(to_mltl(not_mltl_ext(x)) == Mltl::Not(Box::new(to_mltl(x))));
    block_bounds(a, b, l, s, 0);
    ok_future_list(dx, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize], n);
    let head = Future_mltl_list_spec(dx, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    ok_mono(head, ((s[1] - 1) + n) as nat, bn);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_future_piece(dx, x, s, j + 1));
    assert forall|j: int| 0 <= j < pieces.len() implies all_ok(#[trigger] pieces[j], bn) by {
        let i = j + 1;
        block_bounds(a, b, l, s, i);
        ok_block_global(a, b, l, s, i, not_mltl_ext(x));
        let f = Future_mltl_list_spec(dx, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]);
        ok_future_list(dx, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize], n);
        ok_mono(f, ((s[i + 1] - 1) + n) as nat, bn);
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], not_mltl_ext(x));
        ok_and_list(seq![g], f, bn, bn);
    }
    ok_concat(pieces, bn);
    ok_append(head, concat(pieces), bn);
}

#[verifier::spinoff_prover]
proof fn lp_until_ok<A>(l: Seq<usize>, x: MltlExt<A>, a: usize, b: usize, y: MltlExt<A>, dy: Seq<MltlExt<A>>)
    requires
        intervals_welldef(to_mltl(until_mltl_ext(x, a, b, l, y))),
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        all_ok(dy, wpd_mltl(to_mltl(y))),
    ensures
        all_ok(lp_until_list(l, x, a, b, y, dy), wpd_mltl(to_mltl(until_mltl_ext(x, a, b, l, y)))),
{
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
    reveal_with_fuel(wpd_mltl, 3);
    reveal_with_fuel(intervals_welldef, 3);
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let ny = wpd_mltl(to_mltl(y));
    let m = max_nat(wpd_mltl(to_mltl(x)), ny);
    let bn = (b + m) as nat;
    let body = and_mltl_ext(x, not_mltl_ext(y));
    assert(intervals_welldef(to_mltl(body)) && wpd_mltl(to_mltl(body)) == m);
    block_bounds(a, b, l, s, 0);
    ok_until_list(x, dy, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize], ny);
    let head = Until_mltl_list_spec(x, dy, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    ok_mono(head, ((s[1] - 1) + m) as nat, bn);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_until_piece(x, dy, y, s, j + 1));
    assert forall|j: int| 0 <= j < pieces.len() implies all_ok(#[trigger] pieces[j], bn) by {
        let i = j + 1;
        block_bounds(a, b, l, s, i);
        ok_block_global(a, b, l, s, i, body);
        let f = Until_mltl_list_spec(x, dy, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]);
        ok_until_list(x, dy, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize], ny);
        ok_mono(f, ((s[i + 1] - 1) + m) as nat, bn);
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], body);
        ok_and_list(seq![g], f, bn, bn);
    }
    ok_concat(pieces, bn);
    ok_append(head, concat(pieces), bn);
}

#[verifier::spinoff_prover]
proof fn lp_release_ok<A>(l: Seq<usize>, x: MltlExt<A>, a: usize, b: usize, y: MltlExt<A>, dx: Seq<MltlExt<A>>)
    requires
        intervals_welldef(to_mltl(release_mltl_ext(x, a, b, l, y))),
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        all_ok(dx, wpd_mltl(to_mltl(x))),
    ensures
        all_ok(lp_release_list(l, x, a, b, y, dx), wpd_mltl(to_mltl(release_mltl_ext(x, a, b, l, y)))),
{
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
    reveal_with_fuel(wpd_mltl, 3);
    reveal_with_fuel(intervals_welldef, 3);
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let nx = wpd_mltl(to_mltl(x));
    let m = max_nat(nx, wpd_mltl(to_mltl(y)));
    let bn = (b + m) as nat;
    let body = and_mltl_ext(not_mltl_ext(x), y);
    assert(intervals_welldef(to_mltl(body)) && wpd_mltl(to_mltl(body)) == m);
    let e0 = global_mltl_ext(a, b, l, body);
    ok_single(e0);
    block_bounds(a, b, l, s, 0);
    ok_mighty_release_list(dx, y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize], nx);
    let head = Mighty_Release_mltl_list_spec(dx, y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize]);
    ok_mono(head, ((s[1] - 1) + m) as nat, bn);
    let pieces = Seq::new(nat_sub(l.len(), 1), |j: int| LP_release_piece(dx, x, y, s, j + 1));
    assert forall|j: int| 0 <= j < pieces.len() implies all_ok(#[trigger] pieces[j], bn) by {
        let i = j + 1;
        block_bounds(a, b, l, s, i);
        ok_block_global(a, b, l, s, i, body);
        let f = Mighty_Release_mltl_list_spec(dx, y, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]);
        ok_mighty_release_list(dx, y, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize], nx);
        ok_mono(f, ((s[i + 1] - 1) + m) as nat, bn);
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], body);
        ok_and_list(seq![g], f, bn, bn);
    }
    ok_concat(pieces, bn);
    ok_append(seq![e0], head, bn);
    ok_append(seq![e0] + head, concat(pieces), bn);
}

pub proof fn LP_mltl_aux_intervals_welldef<A>(phi: MltlExt<A>, psi: MltlExt<A>, k: nat)
    requires
        intervals_welldef(to_mltl(phi)),
        LP_mltl_aux_spec(convert_nnf_ext_spec(phi), k).contains(psi),
        is_composition_MLTL(phi),
    ensures
        intervals_welldef(to_mltl(psi)),
{
    lp_child_ok(phi, k);
}

/// `∃φ_init. φ = convert_nnf_ext φ_init ⟹ intervals_welldef (to_mltl φ) ⟹
/// ψ ∈ set (LP_mltl_aux φ k) ⟹ is_composition_MLTL φ ⟹ wpd_mltl (to_mltl ψ) ≤ wpd_mltl (to_mltl φ)`
pub proof fn LP_mltl_aux_wpd<A>(phi: MltlExt<A>, psi: MltlExt<A>, k: nat)
    requires
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        intervals_welldef(to_mltl(phi)),
        LP_mltl_aux_spec(phi, k).contains(psi),
        is_composition_MLTL(phi),
    ensures
        wpd_mltl(to_mltl(psi)) <= wpd_mltl(to_mltl(phi)),
{
    LP_mltl_aux_welldef_wpd(phi, k);
}

/// `∃φ_init. φ = convert_nnf_ext φ_init ⟹ intervals_welldef (to_mltl φ) ⟹
/// is_composition_MLTL φ ⟹ LP_mltl_aux φ k ≠ []`
pub proof fn LP_mltl_aux_nonempty<A>(phi: MltlExt<A>, k: nat)
    requires
        exists|init: MltlExt<A>| phi == convert_nnf_ext_spec(init),
        intervals_welldef(to_mltl(phi)),
        is_composition_MLTL(phi),
    ensures
        LP_mltl_aux_spec(phi, k).len() != 0,
    decreases k, 0nat,
{
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 2);
    if k > 0 {
        let k1 = (k - 1) as nat;
        let init = choose|init: MltlExt<A>| phi == convert_nnf_ext_spec(init);
        convert_nnf_ext_not_is_prop(init);
        match phi {
            MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) => {
                lp_child_nonempty(*x, k1);
                lp_child_nonempty(*y, k1);
                And_mltl_list_nonempty(LP_mltl_aux_spec(convert_nnf_ext_spec(*x), k1), LP_mltl_aux_spec(convert_nnf_ext_spec(*y), k1));
            },
            MltlParseTree::Global(l, a, b, x) => {
                lp_child_nonempty(*x, k1);
                let dx = LP_mltl_aux_spec(convert_nnf_ext_spec(*x), k1);
                if dx.len() > 1 {
                    Global_mltl_decomp_nonempty(dx, a, nat_sub(b as nat, a as nat), l);
                }
            },
            MltlParseTree::Future(l, a, b, x) => {
                lp_child_nonempty(*x, k1);
            },
            MltlParseTree::Until(l, x, a, b, y) => {
                lp_child_nonempty(*y, k1);
            },
            _ => {},
        }
    }
}

proof fn lp_child_nonempty<A>(x: MltlExt<A>, k: nat)
    requires
        intervals_welldef(to_mltl(x)),
        is_composition_MLTL(x),
    ensures
        LP_mltl_aux_spec(convert_nnf_ext_spec(x), k).len() != 0,
    decreases k, 1nat,
{
    convert_nnf_ext_welldef(x);
    is_composition_convert_nnf_ext(x);
    LP_mltl_aux_nonempty(convert_nnf_ext_spec(x), k);
}

// ---------------------------------------------------------------------------
// LP_mltl
// ---------------------------------------------------------------------------

/// `ψ ∈ set (LP_mltl φ k) ⟷ (∃ψ_ext ∈ set (LP_mltl_aux (convert_nnf_ext φ) k). ψ = to_mltl (convert_nnf_ext ψ_ext))`
pub proof fn LP_mltl_element<A>(phi: MltlExt<A>, k: nat, psi: Mltl<A>)
    ensures
        LP_mltl_spec(phi, k).contains(psi) <==> exists|x: MltlExt<A>|
            LP_mltl_aux_spec(convert_nnf_ext_spec(phi), k).contains(x) && psi == to_mltl(convert_nnf_ext_spec(x)),
{
    let d = LP_mltl_aux_spec(convert_nnf_ext_spec(phi), k);
    let m = d.map_values(|x: MltlExt<A>| convert_nnf_ext_spec(x));
    let r = LP_mltl_spec(phi, k);
    if r.contains(psi) {
        let i = choose|i: int| 0 <= i < r.len() && r[i] == psi;
        assert(m[i] == convert_nnf_ext_spec(d[i]));
        assert(d.contains(d[i]));
    }
    if exists|x: MltlExt<A>| d.contains(x) && psi == to_mltl(convert_nnf_ext_spec(x)) {
        let x = choose|x: MltlExt<A>| d.contains(x) && psi == to_mltl(convert_nnf_ext_spec(x));
        let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
        assert(r[i] == psi);
    }
}

/// `ψ ∈ set (LP_mltl φ k) ⟹ ∃ψ_init. ψ = convert_nnf ψ_init`
pub proof fn LP_mltl_nnf<A>(phi: MltlExt<A>, psi: Mltl<A>, k: nat)
    requires
        LP_mltl_spec(phi, k).contains(psi),
    ensures
        exists|init: Mltl<A>| psi == convert_nnf_spec(init),
{
    LP_mltl_element(phi, k, psi);
    let x = choose|x: MltlExt<A>| LP_mltl_aux_spec(convert_nnf_ext_spec(phi), k).contains(x) && psi == to_mltl(convert_nnf_ext_spec(x));
    convert_nnf_and_convert_nnf_ext(x);
}

// ---------------------------------------------------------------------------
// Ands_mltl_ext and Global_mltl_decomp
// ---------------------------------------------------------------------------

/// `length X ≥ 1 ⟹ (π ⊨_c Ands_mltl_ext X ⟷ (∀x ∈ set X. π ⊨_c x))`
pub proof fn Ands_mltl_semantics<A>(x: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        x.len() >= 1,
    ensures
        semantics_mltl_ext(pi, Ands_mltl_ext(x))
            == forall|y: MltlExt<A>| x.contains(y) ==> #[trigger] semantics_mltl_ext(pi, y),
    decreases x.len(),
{
    if x.len() == 1 {
        assert forall|y: MltlExt<A>| x.contains(y) implies y == x[0] by {}
        assert(x.contains(x[0]));
    } else {
        let h = x.drop_last();
        Ands_mltl_semantics(h, pi);
        and_ext_semantics(Ands_mltl_ext(h), x.last(), pi);
        assert forall|y: MltlExt<A>| x.contains(y) <==> (h.contains(y) || y == x.last()) by {
            if x.contains(y) {
                let i = choose|i: int| 0 <= i < x.len() && x[i] == y;
                if i < h.len() {
                    assert(h[i] == y);
                }
            }
            if h.contains(y) {
                let i = choose|i: int| 0 <= i < h.len() && h[i] == y;
                assert(x[i] == y);
            }
            if y == x.last() {
                assert(x[x.len() - 1] == y);
            }
        }
    }
}

/// `length D_φ > 1 ⟹ ψ ∈ set (Global_mltl_decomp D_φ a n L) ⟹ ∃X. ψ = Ands_mltl_ext X ∧
/// (∀i < length X. ∃y ∈ set D_φ. X!i = Global_mltl_ext (a+i) (a+i) [1] y) ∧ length X = Suc n`
/// (holds without `length D_φ > 1`; returns `X`).
pub proof fn in_Global_mltl_decomp_exact_forward<A>(d: Seq<MltlExt<A>>, a: usize, n: nat, l: Seq<usize>, psi: MltlExt<A>)
    -> (x: Seq<MltlExt<A>>)
    requires
        Global_mltl_decomp_spec(d, a, n, l).contains(psi),
    ensures
        psi == Ands_mltl_ext(x),
        forall|i: int| 0 <= i < x.len() ==> exists|y: MltlExt<A>|
            d.contains(y) && #[trigger] x[i] == global_mltl_ext((a + i) as usize, (a + i) as usize, seq![1usize], y),
        x.len() == n + 1,
    decreases n,
{
    if n == 0 {
        Global_mltl_list_member(d, a, a, seq![1usize], psi);
        let x = seq![psi];
        assert(x[0] == psi);
        x
    } else {
        let t = (a + n) as usize;
        let prev = Global_mltl_decomp_spec(d, a, (n - 1) as nat, l);
        let r = And_mltl_list_member_forward(prev, Global_mltl_list_spec(d, t, t, seq![1usize]), psi);
        let xp = in_Global_mltl_decomp_exact_forward(d, a, (n - 1) as nat, l, r.0);
        Global_mltl_list_member(d, t, t, seq![1usize], r.1);
        let x = xp.push(r.1);
        assert(x.drop_last() =~= xp);
        assert forall|i: int| 0 <= i < x.len() implies exists|y: MltlExt<A>|
            d.contains(y) && #[trigger] x[i] == global_mltl_ext((a + i) as usize, (a + i) as usize, seq![1usize], y) by {
            if i < xp.len() {
                assert(x[i] == xp[i]);
            }
        }
        x
    }
}

/// `ψ ∈ set (Global_mltl_decomp D_φ a n L) ⟹ ∃X. ψ = Ands_mltl_ext X ∧ (∀x ∈ X. ∃y ∈ D_φ. ∃k.
/// a ≤ k ≤ a+n ∧ x = Global_mltl_ext k k [1] y) ∧ length X = Suc n` (without `length D_φ > 1`).
pub proof fn in_Global_mltl_decomp<A>(d: Seq<MltlExt<A>>, a: usize, n: nat, l: Seq<usize>, psi: MltlExt<A>)
    -> (x: Seq<MltlExt<A>>)
    requires
        Global_mltl_decomp_spec(d, a, n, l).contains(psi),
    ensures
        psi == Ands_mltl_ext(x),
        forall|z: MltlExt<A>| #[trigger] x.contains(z) ==> exists|y: MltlExt<A>, k: nat|
            d.contains(y) && a <= k <= a + n && z == #[trigger] global_mltl_ext(k as usize, k as usize, seq![1usize], y),
        x.len() == n + 1,
{
    let x = in_Global_mltl_decomp_exact_forward(d, a, n, l, psi);
    assert forall|z: MltlExt<A>| #[trigger] x.contains(z) implies exists|y: MltlExt<A>, k: nat|
        d.contains(y) && a <= k <= a + n && z == #[trigger] global_mltl_ext(k as usize, k as usize, seq![1usize], y) by {
        let i = choose|i: int| 0 <= i < x.len() && x[i] == z;
        let y = choose|y: MltlExt<A>| d.contains(y) && #[trigger] x[i] == global_mltl_ext((a + i) as usize, (a + i) as usize, seq![1usize], y);
        assert(d.contains(y) && a <= (a + i) as nat <= a + n
            && z == global_mltl_ext(((a + i) as nat) as usize, ((a + i) as nat) as usize, seq![1usize], y));
    }
    x
}

/// `ψ = Ands_mltl_ext X ⟹ (∀i < length X. ∃y ∈ set D_φ. X!i = Global_mltl_ext (a+i) (a+i) [1] y) ⟹
/// length X = n+1 ⟹ ψ ∈ set (Global_mltl_decomp D_φ a n L)` (without `length D_φ > 1`).
pub proof fn in_Global_mltl_decomp_exact_converse<A>(d: Seq<MltlExt<A>>, a: usize, n: nat, l: Seq<usize>, x: Seq<MltlExt<A>>)
    requires
        forall|i: int| 0 <= i < x.len() ==> exists|y: MltlExt<A>|
            d.contains(y) && #[trigger] x[i] == global_mltl_ext((a + i) as usize, (a + i) as usize, seq![1usize], y),
        x.len() == n + 1,
    ensures
        Global_mltl_decomp_spec(d, a, n, l).contains(Ands_mltl_ext(x)),
    decreases n,
{
    let last = x[n as int];
    let y = choose|y: MltlExt<A>| d.contains(y) && #[trigger] x[n as int] == global_mltl_ext((a + n) as usize, (a + n) as usize, seq![1usize], y);
    let t = (a + n) as usize;
    Global_mltl_list_member(d, t, t, seq![1usize], last);
    if n == 0 {
        assert(Ands_mltl_ext(x) == x[0]);
    } else {
        let h = x.drop_last();
        assert forall|i: int| 0 <= i < h.len() implies exists|y: MltlExt<A>|
            d.contains(y) && #[trigger] h[i] == global_mltl_ext((a + i) as usize, (a + i) as usize, seq![1usize], y) by {
            assert(h[i] == x[i]);
        }
        in_Global_mltl_decomp_exact_converse(d, a, (n - 1) as nat, l, h);
        And_mltl_list_member_converse(Global_mltl_decomp_spec(d, a, (n - 1) as nat, l), Global_mltl_list_spec(d, t, t, seq![1usize]), Ands_mltl_ext(h), last);
    }
}

} // verus!
