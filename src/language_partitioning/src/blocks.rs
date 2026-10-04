//! Semantics of the pieces that `LP_mltl_aux` builds.
//!
//! Not a section of Isabelle; this replaces the long case analyses inside
//! `LP_mltl_aux_language_union_forward/converse` and the disjointness
//! helpers by two kinds of lemma:
//! - *lifting*: if the formulas of `D` hold on a suffix exactly when `x`
//!   does, then some formula of `Future_mltl_list D …` holds exactly when
//!   `F … x` does (likewise for the other builders);
//! - *partition*: `F[a,b] x` holds exactly when one of its blocks holds
//!   (`future_block`), and no two blocks hold together.
//!
//! Throughout, `P(t)` means `drop π t ⊨_c x`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use crate::ext::*;
use crate::composition::*;
use crate::algorithm::*;
use crate::lists::*;

verus! {

/// On the suffixes `drop π t`, `lo ≤ t ≤ hi`, some formula of `D` holds
/// exactly when `x` does.
pub open spec fn agrees_on<A>(d: Seq<MltlExt<A>>, x: MltlExt<A>, pi: Seq<Set<A>>, lo: nat, hi: nat) -> bool {
    forall|t: nat| lo <= t <= hi ==> sat_some(d, #[trigger] drop(pi, t)) == semantics_mltl_ext(drop(pi, t), x)
}

/// `∃j. lb ≤ j ≤ i ∧ P j ∧ (∀l. lb ≤ l < j ⟶ ¬P l)` (returns `j`).
pub proof fn exist_first(p: spec_fn(nat) -> bool, lb: nat, i: nat) -> (j: nat)
    requires
        lb <= i,
        p(i),
    ensures
        lb <= j <= i,
        p(j),
        forall|l: nat| lb <= l < j ==> !#[trigger] p(l),
    decreases i - lb,
{
    if p(lb) {
        lb
    } else {
        let j = exist_first(p, lb + 1, i);
        assert forall|l: nat| lb <= l < j implies !#[trigger] p(l) by {
            if l > lb {
                assert(lb + 1 <= l);
            }
        }
        j
    }
}

// ---------------------------------------------------------------------------
// Lifting through the builders
// ---------------------------------------------------------------------------

pub proof fn Future_mltl_list_sat<A>(d: Seq<MltlExt<A>>, lo: usize, hi: usize, w: Seq<usize>, x: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        agrees_on(d, x, pi, lo as nat, hi as nat),
    ensures
        sat_some(Future_mltl_list_spec(d, lo, hi, w), pi) == semantics_mltl_ext(pi, future_mltl_ext(lo, hi, w, x)),
{
    let fl = Future_mltl_list_spec(d, lo, hi, w);
    if sat_some(fl, pi) {
        let psi = choose|psi: MltlExt<A>| fl.contains(psi) && semantics_mltl_ext(pi, psi);
        Future_mltl_list_member(d, lo, hi, w, psi);
        let y = choose|y: MltlExt<A>| d.contains(y) && psi == future_mltl_ext(lo, hi, w, y);
        let t = choose|t: nat| lo <= t <= hi && semantics_mltl(drop(pi, t), to_mltl(y));
        assert(sat_some(d, drop(pi, t)));
        assert(semantics_mltl(drop(pi, t), to_mltl(x)));
    }
    if semantics_mltl_ext(pi, future_mltl_ext(lo, hi, w, x)) {
        let t = choose|t: nat| lo <= t <= hi && semantics_mltl(drop(pi, t), to_mltl(x));
        assert(sat_some(d, drop(pi, t)));
        let y = choose|y: MltlExt<A>| d.contains(y) && semantics_mltl_ext(drop(pi, t), y);
        Future_mltl_list_member(d, lo, hi, w, future_mltl_ext(lo, hi, w, y));
        assert(semantics_mltl(drop(pi, t), to_mltl(y)));
        assert(semantics_mltl_ext(pi, future_mltl_ext(lo, hi, w, y)));
    }
}

/// `G_c[t,t]` on a long enough trace: holds exactly when the body holds at `t`.
pub proof fn global_point_semantics<A>(t: usize, w: Seq<usize>, x: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        pi.len() > t,
    ensures
        semantics_mltl_ext(pi, global_mltl_ext(t, t, w, x)) == semantics_mltl_ext(drop(pi, t as nat), x),
{
    if semantics_mltl_ext(pi, global_mltl_ext(t, t, w, x)) {
        assert(semantics_mltl(drop(pi, t as nat), to_mltl(x)));
    }
}

pub proof fn Global_mltl_list_point_sat<A>(d: Seq<MltlExt<A>>, t: usize, w: Seq<usize>, x: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        pi.len() > t,
        agrees_on(d, x, pi, t as nat, t as nat),
    ensures
        sat_some(Global_mltl_list_spec(d, t, t, w), pi) == semantics_mltl_ext(drop(pi, t as nat), x),
{
    let gl = Global_mltl_list_spec(d, t, t, w);
    assert(sat_some(d, drop(pi, t as nat)) == semantics_mltl_ext(drop(pi, t as nat), x));
    if sat_some(gl, pi) {
        let psi = choose|psi: MltlExt<A>| gl.contains(psi) && semantics_mltl_ext(pi, psi);
        Global_mltl_list_member(d, t, t, w, psi);
        let y = choose|y: MltlExt<A>| d.contains(y) && psi == global_mltl_ext(t, t, w, y);
        global_point_semantics(t, w, y, pi);
    }
    if semantics_mltl_ext(drop(pi, t as nat), x) {
        let y = choose|y: MltlExt<A>| d.contains(y) && semantics_mltl_ext(drop(pi, t as nat), y);
        Global_mltl_list_member(d, t, t, w, global_mltl_ext(t, t, w, y));
        global_point_semantics(t, w, y, pi);
    }
}

pub proof fn Until_mltl_list_sat<A>(phi: MltlExt<A>, d: Seq<MltlExt<A>>, lo: usize, hi: usize, w: Seq<usize>, x: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        agrees_on(d, x, pi, lo as nat, hi as nat),
    ensures
        sat_some(Until_mltl_list_spec(phi, d, lo, hi, w), pi) == semantics_mltl_ext(pi, until_mltl_ext(phi, lo, hi, w, x)),
{
    let ul = Until_mltl_list_spec(phi, d, lo, hi, w);
    if sat_some(ul, pi) {
        let psi = choose|psi: MltlExt<A>| ul.contains(psi) && semantics_mltl_ext(pi, psi);
        Until_mltl_list_member(phi, d, lo, hi, w, psi);
        let y = choose|y: MltlExt<A>| d.contains(y) && psi == until_mltl_ext(phi, lo, hi, w, y);
        let t = choose|t: nat| lo <= t <= hi && (semantics_mltl(drop(pi, t), to_mltl(y))
            && forall|j: nat| (j >= lo && j < t) ==> semantics_mltl(drop(pi, j), to_mltl(phi)));
        assert(sat_some(d, drop(pi, t)));
        assert(semantics_mltl(drop(pi, t), to_mltl(x)));
    }
    if semantics_mltl_ext(pi, until_mltl_ext(phi, lo, hi, w, x)) {
        let t = choose|t: nat| lo <= t <= hi && (semantics_mltl(drop(pi, t), to_mltl(x))
            && forall|j: nat| (j >= lo && j < t) ==> semantics_mltl(drop(pi, j), to_mltl(phi)));
        assert(sat_some(d, drop(pi, t)));
        let y = choose|y: MltlExt<A>| d.contains(y) && semantics_mltl_ext(drop(pi, t), y);
        Until_mltl_list_member(phi, d, lo, hi, w, until_mltl_ext(phi, lo, hi, w, y));
        assert(semantics_mltl(drop(pi, t), to_mltl(y)));
        assert(semantics_mltl_ext(pi, until_mltl_ext(phi, lo, hi, w, y)));
    }
}

/// `Mighty_Release_mltl_ext x ψ a b L` is the conjunction of its two parts.
pub proof fn mighty_release_semantics<A>(x: MltlExt<A>, psi: MltlExt<A>, lo: usize, hi: usize, w: Seq<usize>, pi: Seq<Set<A>>)
    ensures
        semantics_mltl_ext(pi, Mighty_Release_mltl_ext(x, psi, lo, hi, w))
            == (semantics_mltl(pi, Mltl::Release(Box::new(to_mltl(x)), lo, hi, Box::new(to_mltl(psi))))
                && semantics_mltl(pi, Mltl::Future(lo, hi, Box::new(to_mltl(x))))),
{
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
}

pub proof fn Mighty_Release_mltl_list_sat<A>(d: Seq<MltlExt<A>>, psi: MltlExt<A>, lo: usize, hi: usize, w: Seq<usize>, x: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        agrees_on(d, x, pi, lo as nat, hi as nat),
    ensures
        sat_some(Mighty_Release_mltl_list_spec(d, psi, lo, hi, w), pi)
            == semantics_mltl_ext(pi, Mighty_Release_mltl_ext(x, psi, lo, hi, w)),
{
    let ml = Mighty_Release_mltl_list_spec(d, psi, lo, hi, w);
    let tx = to_mltl(x);
    let tp = to_mltl(psi);
    mighty_release_semantics(x, psi, lo, hi, w, pi);
    if sat_some(ml, pi) {
        let e = choose|e: MltlExt<A>| ml.contains(e) && semantics_mltl_ext(pi, e);
        Mighty_Release_mltl_list_member(d, psi, lo, hi, w, e);
        let y = choose|y: MltlExt<A>| d.contains(y) && e == Mighty_Release_mltl_ext(y, psi, lo, hi, w);
        let ty = to_mltl(y);
        mighty_release_semantics(y, psi, lo, hi, w, pi);
        assert(semantics_mltl(pi, Mltl::Future(lo, hi, Box::new(ty))));
        // F y ⟹ F x
        let t = choose|t: nat| lo <= t <= hi && semantics_mltl(drop(pi, t), ty);
        assert(sat_some(d, drop(pi, t)));
        assert(semantics_mltl(drop(pi, t), tx));
        assert(semantics_mltl(pi, Mltl::Future(lo, hi, Box::new(tx))));
        // y R ψ ⟹ x R ψ
        assert(semantics_mltl(pi, Mltl::Release(Box::new(ty), lo, hi, Box::new(tp))));
        if !(forall|i: nat| (lo <= i && i <= hi) ==> semantics_mltl(drop(pi, i), tp)) {
            let j = choose|j: nat| (j >= lo && j <= nat_sub(hi as nat, 1)) && semantics_mltl(drop(pi, j), ty)
                && forall|k: nat| (lo <= k && k <= j) ==> semantics_mltl(drop(pi, k), tp);
            assert(sat_some(d, drop(pi, j)));
            assert(semantics_mltl(drop(pi, j), tx));
        }
        assert(semantics_mltl(pi, Mltl::Release(Box::new(tx), lo, hi, Box::new(tp))));
    }
    if semantics_mltl_ext(pi, Mighty_Release_mltl_ext(x, psi, lo, hi, w)) {
        assert(semantics_mltl(pi, Mltl::Future(lo, hi, Box::new(tx))));
        assert(semantics_mltl(pi, Mltl::Release(Box::new(tx), lo, hi, Box::new(tp))));
        let all_p = forall|i: nat| (lo <= i && i <= hi) ==> semantics_mltl(drop(pi, i), tp);
        let m: nat = if all_p {
            choose|t: nat| lo <= t <= hi && semantics_mltl(drop(pi, t), tx)
        } else {
            choose|j: nat| (j >= lo && j <= nat_sub(hi as nat, 1)) && semantics_mltl(drop(pi, j), tx)
                && forall|k: nat| (lo <= k && k <= j) ==> semantics_mltl(drop(pi, k), tp)
        };
        assert(lo <= m <= hi && semantics_mltl(drop(pi, m), tx));
        assert(sat_some(d, drop(pi, m)));
        let y = choose|y: MltlExt<A>| d.contains(y) && semantics_mltl_ext(drop(pi, m), y);
        let ty = to_mltl(y);
        Mighty_Release_mltl_list_member(d, psi, lo, hi, w, Mighty_Release_mltl_ext(y, psi, lo, hi, w));
        mighty_release_semantics(y, psi, lo, hi, w, pi);
        assert(semantics_mltl(drop(pi, m), ty));
        assert(semantics_mltl(pi, Mltl::Future(lo, hi, Box::new(ty))));
        assert(semantics_mltl(pi, Mltl::Release(Box::new(ty), lo, hi, Box::new(tp))));
        assert(semantics_mltl_ext(pi, Mighty_Release_mltl_ext(y, psi, lo, hi, w)));
    }
}

/// Some decomposition of `G[a, a+len]` holds exactly when `x` holds at every
/// time in `[a, a+len]`.
pub proof fn Global_mltl_decomp_sat<A>(d: Seq<MltlExt<A>>, a: usize, len: nat, l: Seq<usize>, x: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        a + len <= usize::MAX,
        pi.len() > a + len,
        agrees_on(d, x, pi, a as nat, (a + len) as nat),
    ensures
        sat_some(Global_mltl_decomp_spec(d, a, len, l), pi)
            == forall|t: nat| a <= t <= a + len ==> semantics_mltl_ext(#[trigger] drop(pi, t), x),
    decreases len,
{
    let t_last = (a + len) as usize;
    Global_mltl_list_point_sat(d, t_last, seq![1usize], x, pi);
    if len > 0 {
        let prev = Global_mltl_decomp_spec(d, a, (len - 1) as nat, l);
        Global_mltl_decomp_sat(d, a, (len - 1) as nat, l, x, pi);
        And_mltl_list_sat(prev, Global_mltl_list_spec(d, t_last, t_last, seq![1usize]), pi);
        if forall|t: nat| a <= t <= a + (len - 1) ==> semantics_mltl_ext(#[trigger] drop(pi, t), x) {
            if semantics_mltl_ext(drop(pi, t_last as nat), x) {
                assert forall|t: nat| a <= t <= a + len implies semantics_mltl_ext(#[trigger] drop(pi, t), x) by {
                    if t < a + len {
                        assert(t <= a + (len - 1));
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Blocks of F, U, R
// ---------------------------------------------------------------------------

/// Block `i` of `F_c[a,b] <L> x` with `s = interval_times a L`: `x` first
/// holds in `[s_i, s_{i+1} - 1]`.
pub open spec fn future_block<A>(x: MltlExt<A>, s: Seq<nat>, i: int) -> MltlExt<A> {
    if i == 0 {
        future_mltl_ext(s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize], x)
    } else {
        and_mltl_ext(
            global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], not_mltl_ext(x)),
            future_mltl_ext(s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize], x),
        )
    }
}

/// Block `i` of `x U_c[a,b] <L> y`: `y` first holds in block `i`.
pub open spec fn until_block<A>(x: MltlExt<A>, y: MltlExt<A>, s: Seq<nat>, i: int) -> MltlExt<A> {
    if i == 0 {
        until_mltl_ext(x, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize], y)
    } else {
        and_mltl_ext(
            global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(x, not_mltl_ext(y))),
            until_mltl_ext(x, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize], y),
        )
    }
}

/// Block `i` of `x R_c[a,b] <L> y`: `x` first holds in block `i`.
pub open spec fn release_block<A>(x: MltlExt<A>, y: MltlExt<A>, s: Seq<nat>, i: int) -> MltlExt<A> {
    if i == 0 {
        Mighty_Release_mltl_ext(x, y, s[0] as usize, (s[1] - 1) as usize, seq![(s[1] - s[0]) as usize])
    } else {
        and_mltl_ext(
            global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(not_mltl_ext(x), y)),
            Mighty_Release_mltl_ext(x, y, s[i] as usize, (s[i + 1] - 1) as usize, seq![(s[i + 1] - s[i]) as usize]),
        )
    }
}

/// The facts about block bounds that every partition proof uses.
pub open spec fn blocks_ok(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>) -> bool {
    &&& a <= b
    &&& is_composition(nat_sub(b as nat, a as nat) + 1, l)
    &&& s == interval_times(a as nat, l)
    &&& l.len() >= 1
    &&& s.len() == l.len() + 1
    &&& s[0] == a
    &&& s[l.len() as int] == b + 1
    &&& forall|i: int| 0 <= i < l.len() ==> #[trigger] s[i + 1] == s[i] + l[i] && l[i] > 0
    &&& forall|i: int, j: int| #![trigger s[i], s[j]] 0 <= i < j <= l.len() ==> s[i] + (j - i) <= s[j]
    &&& forall|i: int| 0 <= i <= l.len() ==> a <= #[trigger] s[i] <= b + 1
}

pub proof fn lemma_blocks_ok(a: usize, b: usize, l: Seq<usize>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
    ensures
        blocks_ok(a, b, l, interval_times(a as nat, l)),
{
    interval_times_facts(a as nat, b as nat, l);
}

/// Block `i` lies inside `[a,b]`: `a ≤ s_0 ≤ s_i ≤ s_{i+1} - 1 ≤ b`, and
/// for `i > 0`, `s_0 ≤ s_i - 1`.
pub proof fn block_bounds(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, i: int)
    requires
        blocks_ok(a, b, l, s),
        0 <= i < l.len(),
    ensures
        s[0] == a,
        a <= s[i] <= s[i + 1] - 1 <= b,
        i > 0 ==> s[0] <= s[i] - 1,
        forall|j: int| i < j < l.len() ==> s[i + 1] <= #[trigger] s[j],
{
    assert(s[i] + 1 <= s[i + 1]);
    assert(s[i + 1] <= b + 1);
    if i > 0 {
        assert(s[0] + i <= s[i]);
    }
    assert forall|j: int| i < j < l.len() implies s[i + 1] <= #[trigger] s[j] by {
        if i + 1 < j {
            assert(s[i + 1] + (j - (i + 1)) <= s[j]);
        }
    }
}

/// The block of the time `t ∈ [a,b]`.
pub proof fn block_of(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, t: nat) -> (i: int)
    requires
        blocks_ok(a, b, l, s),
        a <= t <= b,
    ensures
        0 <= i < l.len(),
        s[i] <= t <= s[i + 1] - 1,
{
    interval_times_obtain(a as nat, b as nat, l, t) as int
}

// --- What the block formulas mean (on traces longer than b) ---------------

pub proof fn and_ext_semantics<A>(x: MltlExt<A>, y: MltlExt<A>, pi: Seq<Set<A>>)
    ensures
        semantics_mltl_ext(pi, and_mltl_ext(x, y)) == (semantics_mltl_ext(pi, x) && semantics_mltl_ext(pi, y)),
{
}

/// `G[lo,hi] ¬x`, `G[lo,hi] (x ∧ ¬y)`, `G[lo,hi] (¬x ∧ y)` on a trace longer than `lo`.
pub proof fn global_body_semantics<A>(lo: usize, hi: usize, w: Seq<usize>, x: MltlExt<A>, y: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        lo <= hi,
        pi.len() > lo,
    ensures
        semantics_mltl_ext(pi, global_mltl_ext(lo, hi, w, not_mltl_ext(x)))
            == forall|u: nat| lo <= u <= hi ==> !semantics_mltl(#[trigger] drop(pi, u), to_mltl(x)),
        semantics_mltl_ext(pi, global_mltl_ext(lo, hi, w, and_mltl_ext(x, not_mltl_ext(y))))
            == forall|u: nat| lo <= u <= hi ==> semantics_mltl(#[trigger] drop(pi, u), to_mltl(x))
                && !semantics_mltl(drop(pi, u), to_mltl(y)),
        semantics_mltl_ext(pi, global_mltl_ext(lo, hi, w, and_mltl_ext(not_mltl_ext(x), y)))
            == forall|u: nat| lo <= u <= hi ==> !semantics_mltl(#[trigger] drop(pi, u), to_mltl(x))
                && semantics_mltl(drop(pi, u), to_mltl(y)),
{
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 4);
    reveal_with_fuel(semantics_mltl, 4);
}

/// Semantics of `F_c`, `U_c`, `R_c` and the mighty release on a trace longer than `hi`.
pub proof fn temporal_semantics<A>(lo: usize, hi: usize, w: Seq<usize>, x: MltlExt<A>, y: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        lo <= hi,
        pi.len() > hi,
    ensures
        semantics_mltl_ext(pi, future_mltl_ext(lo, hi, w, x))
            == exists|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(x)),
        semantics_mltl_ext(pi, until_mltl_ext(x, lo, hi, w, y))
            == exists|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(y))
                && forall|j: nat| lo <= j < t ==> semantics_mltl(#[trigger] drop(pi, j), to_mltl(x)),
        semantics_mltl_ext(pi, release_mltl_ext(x, lo, hi, w, y))
            == release_body(pi, to_mltl(x), to_mltl(y), lo as nat, hi as nat),
        semantics_mltl_ext(pi, Mighty_Release_mltl_ext(x, y, lo, hi, w))
            == (release_body(pi, to_mltl(x), to_mltl(y), lo as nat, hi as nat)
                && exists|t: nat| lo <= t <= hi && semantics_mltl(#[trigger] drop(pi, t), to_mltl(x))),
{
    mighty_release_semantics(x, y, lo, hi, w, pi);
}

/// The release condition on a long trace: `y` throughout, or `x` at some
/// `j ≤ hi - 1` with `y` up to `j`.
pub open spec fn release_body<A>(pi: Seq<Set<A>>, x: Mltl<A>, y: Mltl<A>, lo: nat, hi: nat) -> bool {
    (forall|u: nat| lo <= u <= hi ==> semantics_mltl(#[trigger] drop(pi, u), y))
        || exists|j: nat| lo <= j <= nat_sub(hi, 1) && semantics_mltl(#[trigger] drop(pi, j), x)
            && forall|k: nat| lo <= k <= j ==> semantics_mltl(#[trigger] drop(pi, k), y)
}

/// What `future_block x s i` says.
pub proof fn future_block_semantics<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, x: MltlExt<A>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, s),
        0 <= i < l.len(),
        pi.len() > b,
    ensures
        semantics_mltl_ext(pi, future_block(x, s, i))
            == ((forall|u: nat| s[0] <= u < s[i] ==> !semantics_mltl(#[trigger] drop(pi, u), to_mltl(x)))
                && exists|t: nat| s[i] <= t <= s[i + 1] - 1 && semantics_mltl(#[trigger] drop(pi, t), to_mltl(x))),
{
    block_bounds(a, b, l, s, i);
    let e = (s[i + 1] - 1) as usize;
    temporal_semantics(s[i] as usize, e, seq![(s[i + 1] - s[i]) as usize], x, x, pi);
    if i > 0 {
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], not_mltl_ext(x));
        and_ext_semantics(g, future_mltl_ext(s[i] as usize, e, seq![(s[i + 1] - s[i]) as usize], x), pi);
        global_body_semantics(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], x, x, pi);
    }
}

/// What `until_block x y s i` says.
pub proof fn until_block_semantics<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, x: MltlExt<A>, y: MltlExt<A>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, s),
        0 <= i < l.len(),
        pi.len() > b,
    ensures
        semantics_mltl_ext(pi, until_block(x, y, s, i))
            == ((forall|u: nat| s[0] <= u < s[i] ==> semantics_mltl(#[trigger] drop(pi, u), to_mltl(x))
                    && !semantics_mltl(drop(pi, u), to_mltl(y)))
                && exists|t: nat| s[i] <= t <= s[i + 1] - 1 && semantics_mltl(#[trigger] drop(pi, t), to_mltl(y))
                    && forall|j: nat| s[i] <= j < t ==> semantics_mltl(#[trigger] drop(pi, j), to_mltl(x))),
{
    block_bounds(a, b, l, s, i);
    let e = (s[i + 1] - 1) as usize;
    temporal_semantics(s[i] as usize, e, seq![(s[i + 1] - s[i]) as usize], x, y, pi);
    if i > 0 {
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(x, not_mltl_ext(y)));
        and_ext_semantics(g, until_mltl_ext(x, s[i] as usize, e, seq![(s[i + 1] - s[i]) as usize], y), pi);
        global_body_semantics(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], x, y, pi);
    }
}

/// What `release_block x y s i` says.
pub proof fn release_block_semantics<A>(a: usize, b: usize, l: Seq<usize>, s: Seq<nat>, x: MltlExt<A>, y: MltlExt<A>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, s),
        0 <= i < l.len(),
        pi.len() > b,
    ensures
        semantics_mltl_ext(pi, release_block(x, y, s, i))
            == ((forall|u: nat| s[0] <= u < s[i] ==> !semantics_mltl(#[trigger] drop(pi, u), to_mltl(x))
                    && semantics_mltl(drop(pi, u), to_mltl(y)))
                && release_body(pi, to_mltl(x), to_mltl(y), s[i] as nat, (s[i + 1] - 1) as nat)
                && exists|t: nat| s[i] <= t <= s[i + 1] - 1 && semantics_mltl(#[trigger] drop(pi, t), to_mltl(x))),
{
    block_bounds(a, b, l, s, i);
    let e = (s[i + 1] - 1) as usize;
    temporal_semantics(s[i] as usize, e, seq![(s[i + 1] - s[i]) as usize], x, y, pi);
    if i > 0 {
        let g = global_mltl_ext(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], and_mltl_ext(not_mltl_ext(x), y));
        and_ext_semantics(g, Mighty_Release_mltl_ext(x, y, s[i] as usize, e, seq![(s[i + 1] - s[i]) as usize]), pi);
        global_body_semantics(s[0] as usize, (s[i] - 1) as usize, seq![(s[i] - s[0]) as usize], x, y, pi);
    }
}

// --- Partitions ------------------------------------------------------------

/// `F[a,b] x` holds exactly when one of its blocks does.
pub proof fn future_partition<A>(a: usize, b: usize, l: Seq<usize>, x: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        pi.len() > b,
    ensures
        semantics_mltl_ext(pi, future_mltl_ext(a, b, l, x))
            == exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] future_block(x, interval_times(a as nat, l), i)),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let tx = to_mltl(x);
    temporal_semantics(a, b, l, x, x, pi);
    if semantics_mltl_ext(pi, future_mltl_ext(a, b, l, x)) {
        let t = choose|t: nat| a <= t <= b && semantics_mltl(#[trigger] drop(pi, t), tx);
        let p = |t: nat| semantics_mltl(drop(pi, t), tx);
        assert(p(t));
        let t0 = exist_first(p, a as nat, t);
        let i = block_of(a, b, l, s, t0);
        future_block_semantics(a, b, l, s, x, pi, i);
        assert(semantics_mltl(drop(pi, t0), tx));
        assert forall|u: nat| s[0] <= u < s[i] implies !semantics_mltl(#[trigger] drop(pi, u), tx) by {
            assert(!p(u));
        }
        assert(semantics_mltl_ext(pi, future_block(x, s, i)));
    }
    if exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] future_block(x, s, i)) {
        let i = choose|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] future_block(x, s, i));
        future_block_semantics(a, b, l, s, x, pi, i);
        block_bounds(a, b, l, s, i);
        let t = choose|t: nat| s[i] <= t <= s[i + 1] - 1 && semantics_mltl(#[trigger] drop(pi, t), tx);
        assert(semantics_mltl(drop(pi, t), tx));
    }
}

/// No two blocks of `F[a,b] x` hold together.
pub proof fn future_blocks_exclusive<A>(a: usize, b: usize, l: Seq<usize>, x: MltlExt<A>, pi: Seq<Set<A>>, i: int, j: int)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        pi.len() > b,
        0 <= i < j < l.len(),
    ensures
        !(semantics_mltl_ext(pi, future_block(x, interval_times(a as nat, l), i))
            && semantics_mltl_ext(pi, future_block(x, interval_times(a as nat, l), j))),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let tx = to_mltl(x);
    future_block_semantics(a, b, l, s, x, pi, i);
    future_block_semantics(a, b, l, s, x, pi, j);
    block_bounds(a, b, l, s, i);
    block_bounds(a, b, l, s, j);
    if semantics_mltl_ext(pi, future_block(x, s, i)) && semantics_mltl_ext(pi, future_block(x, s, j)) {
        let t = choose|t: nat| s[i] <= t <= s[i + 1] - 1 && semantics_mltl(#[trigger] drop(pi, t), tx);
        assert(s[0] <= t < s[j]);
        assert(!semantics_mltl(drop(pi, t), tx));
    }
}

/// `x U[a,b] y` holds exactly when one of its blocks does.
pub proof fn until_partition<A>(x: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        pi.len() > b,
    ensures
        semantics_mltl_ext(pi, until_mltl_ext(x, a, b, l, y))
            == exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] until_block(x, y, interval_times(a as nat, l), i)),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let tx = to_mltl(x);
    let ty = to_mltl(y);
    temporal_semantics(a, b, l, x, y, pi);
    if semantics_mltl_ext(pi, until_mltl_ext(x, a, b, l, y)) {
        let t = choose|t: nat| a <= t <= b && semantics_mltl(#[trigger] drop(pi, t), ty)
            && forall|j: nat| a <= j < t ==> semantics_mltl(#[trigger] drop(pi, j), tx);
        let q = |t: nat| semantics_mltl(drop(pi, t), ty);
        assert(q(t));
        let t0 = exist_first(q, a as nat, t);
        let i = block_of(a, b, l, s, t0);
        until_block_semantics(a, b, l, s, x, y, pi, i);
        assert(semantics_mltl(drop(pi, t0), ty));
        assert forall|u: nat| s[0] <= u < s[i] implies semantics_mltl(#[trigger] drop(pi, u), tx)
            && !semantics_mltl(drop(pi, u), ty) by {
            assert(!q(u));
        }
        assert forall|j: nat| s[i] <= j < t0 implies semantics_mltl(#[trigger] drop(pi, j), tx) by {}
        assert(semantics_mltl_ext(pi, until_block(x, y, s, i)));
    }
    if exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] until_block(x, y, s, i)) {
        let i = choose|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] until_block(x, y, s, i));
        until_block_semantics(a, b, l, s, x, y, pi, i);
        block_bounds(a, b, l, s, i);
        let t = choose|t: nat| s[i] <= t <= s[i + 1] - 1 && semantics_mltl(#[trigger] drop(pi, t), ty)
            && forall|j: nat| s[i] <= j < t ==> semantics_mltl(#[trigger] drop(pi, j), tx);
        assert forall|j: nat| a <= j < t implies semantics_mltl(#[trigger] drop(pi, j), tx) by {
            if j < s[i] {
                assert(s[0] <= j < s[i]);
            }
        }
        assert(semantics_mltl(drop(pi, t), ty));
    }
}

/// No two blocks of `x U[a,b] y` hold together.
pub proof fn until_blocks_exclusive<A>(x: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>, pi: Seq<Set<A>>, i: int, j: int)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        pi.len() > b,
        0 <= i < j < l.len(),
    ensures
        !(semantics_mltl_ext(pi, until_block(x, y, interval_times(a as nat, l), i))
            && semantics_mltl_ext(pi, until_block(x, y, interval_times(a as nat, l), j))),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let ty = to_mltl(y);
    until_block_semantics(a, b, l, s, x, y, pi, i);
    until_block_semantics(a, b, l, s, x, y, pi, j);
    block_bounds(a, b, l, s, i);
    block_bounds(a, b, l, s, j);
    if semantics_mltl_ext(pi, until_block(x, y, s, i)) && semantics_mltl_ext(pi, until_block(x, y, s, j)) {
        let t = choose|t: nat| s[i] <= t <= s[i + 1] - 1 && semantics_mltl(#[trigger] drop(pi, t), ty)
            && forall|u: nat| s[i] <= u < t ==> semantics_mltl(#[trigger] drop(pi, u), to_mltl(x));
        assert(s[0] <= t < s[j]);
        assert(!semantics_mltl(drop(pi, t), ty));
    }
}

/// `x R[a,b] y` holds exactly when `G[a,b] (¬x ∧ y)` or one of its blocks does.
pub proof fn release_partition<A>(x: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        pi.len() > b,
    ensures
        semantics_mltl_ext(pi, release_mltl_ext(x, a, b, l, y))
            == (semantics_mltl_ext(pi, global_mltl_ext(a, b, l, and_mltl_ext(not_mltl_ext(x), y)))
                || exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] release_block(x, y, interval_times(a as nat, l), i))),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    temporal_semantics(a, b, l, x, y, pi);
    global_body_semantics(a, b, l, x, y, pi);
    if semantics_mltl_ext(pi, release_mltl_ext(x, a, b, l, y)) {
        release_forward(x, a, b, l, y, pi);
    }
    if exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] release_block(x, y, s, i)) {
        let i = choose|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] release_block(x, y, s, i));
        release_block_implies(x, a, b, l, y, pi, i);
    }
}

/// The forward half of `release_partition`.
proof fn release_forward<A>(x: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>, pi: Seq<Set<A>>)
    requires
        blocks_ok(a, b, l, interval_times(a as nat, l)),
        pi.len() > b,
        release_body(pi, to_mltl(x), to_mltl(y), a as nat, b as nat),
    ensures
        (forall|u: nat| a <= u <= b ==> !semantics_mltl(#[trigger] drop(pi, u), to_mltl(x))
            && semantics_mltl(drop(pi, u), to_mltl(y)))
            || exists|i: int| 0 <= i < l.len() && semantics_mltl_ext(pi, #[trigger] release_block(x, y, interval_times(a as nat, l), i)),
{
    let s = interval_times(a as nat, l);
    let tx = to_mltl(x);
    let ty = to_mltl(y);
    let all_y = forall|u: nat| a <= u <= b ==> semantics_mltl(#[trigger] drop(pi, u), ty);
    if exists|u: nat| a <= u <= b && semantics_mltl(#[trigger] drop(pi, u), tx) {
        let p = |t: nat| semantics_mltl(drop(pi, t), tx);
        let t = choose|u: nat| a <= u <= b && semantics_mltl(#[trigger] drop(pi, u), tx);
        assert(p(t));
        let t0 = exist_first(p, a as nat, t);
        assert(semantics_mltl(drop(pi, t0), tx));
        // y holds on [a, t0]
        assert(forall|u: nat| a <= u <= t0 ==> semantics_mltl(#[trigger] drop(pi, u), ty)) by {
            if !all_y {
                let j = choose|j: nat| a <= j <= nat_sub(b as nat, 1) && semantics_mltl(#[trigger] drop(pi, j), tx)
                    && forall|k: nat| a <= k <= j ==> semantics_mltl(#[trigger] drop(pi, k), ty);
                assert(p(j));
                assert(t0 <= j);
            }
        }
        let i = block_of(a, b, l, s, t0);
        block_bounds(a, b, l, s, i);
        release_block_semantics(a, b, l, s, x, y, pi, i);
        let e = (s[i + 1] - 1) as nat;
        assert forall|u: nat| s[0] <= u < s[i] implies !semantics_mltl(#[trigger] drop(pi, u), tx)
            && semantics_mltl(drop(pi, u), ty) by {
            assert(!p(u));
        }
        if t0 > nat_sub(e, 1) {
            assert(t0 == e);
            assert(forall|u: nat| s[i] <= u <= e ==> semantics_mltl(#[trigger] drop(pi, u), ty));
        } else {
            assert(forall|k: nat| s[i] <= k <= t0 ==> semantics_mltl(#[trigger] drop(pi, k), ty));
            assert(release_body(pi, tx, ty, s[i] as nat, e));
        }
        assert(semantics_mltl_ext(pi, release_block(x, y, s, i)));
    } else {
        assert(all_y);
    }
}

/// The converse half of `release_partition` for one block.
proof fn release_block_implies<A>(x: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>, pi: Seq<Set<A>>, i: int)
    requires
        blocks_ok(a, b, l, interval_times(a as nat, l)),
        pi.len() > b,
        0 <= i < l.len(),
        semantics_mltl_ext(pi, release_block(x, y, interval_times(a as nat, l), i)),
    ensures
        release_body(pi, to_mltl(x), to_mltl(y), a as nat, b as nat),
{
    let s = interval_times(a as nat, l);
    let tx = to_mltl(x);
    let ty = to_mltl(y);
    block_bounds(a, b, l, s, i);
    release_block_semantics(a, b, l, s, x, y, pi, i);
    let e = (s[i + 1] - 1) as nat;
    let m = choose|m: nat| s[i] <= m <= e && semantics_mltl(#[trigger] drop(pi, m), tx);
    assert(semantics_mltl(drop(pi, m), tx));
    if forall|u: nat| s[i] <= u <= e ==> semantics_mltl(#[trigger] drop(pi, u), ty) {
        assert(forall|u: nat| a <= u <= e ==> semantics_mltl(#[trigger] drop(pi, u), ty)) by {
            assert forall|u: nat| a <= u <= e implies semantics_mltl(#[trigger] drop(pi, u), ty) by {
                if u < s[i] {
                    assert(s[0] <= u < s[i]);
                }
            }
        }
        if m <= nat_sub(b as nat, 1) {
            assert(forall|k: nat| a <= k <= m ==> semantics_mltl(#[trigger] drop(pi, k), ty));
        } else {
            assert(m == b);
        }
    } else {
        let j = choose|j: nat| s[i] <= j <= nat_sub(e, 1) && semantics_mltl(#[trigger] drop(pi, j), tx)
            && forall|k: nat| s[i] <= k <= j ==> semantics_mltl(#[trigger] drop(pi, k), ty);
        assert(semantics_mltl(drop(pi, j), tx));
        assert forall|k: nat| a <= k <= j implies semantics_mltl(#[trigger] drop(pi, k), ty) by {
            if k < s[i] {
                assert(s[0] <= k < s[i]);
            }
        }
    }
}

/// `G[a,b] (¬x ∧ y)` and the blocks of `x R[a,b] y`: no two hold together.
/// Block index `-1` stands for `G[a,b] (¬x ∧ y)`.
pub proof fn release_blocks_exclusive<A>(x: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>, pi: Seq<Set<A>>, i: int, j: int)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l),
        pi.len() > b,
        -1 <= i < j < l.len(),
    ensures
        !((if i == -1 {
            semantics_mltl_ext(pi, global_mltl_ext(a, b, l, and_mltl_ext(not_mltl_ext(x), y)))
        } else {
            semantics_mltl_ext(pi, release_block(x, y, interval_times(a as nat, l), i))
        }) && semantics_mltl_ext(pi, release_block(x, y, interval_times(a as nat, l), j))),
{
    let s = interval_times(a as nat, l);
    lemma_blocks_ok(a, b, l);
    let tx = to_mltl(x);
    release_block_semantics(a, b, l, s, x, y, pi, j);
    block_bounds(a, b, l, s, j);
    if semantics_mltl_ext(pi, release_block(x, y, s, j)) {
        if i == -1 {
            global_body_semantics(a, b, l, x, y, pi);
            let m = choose|m: nat| s[j] <= m <= s[j + 1] - 1 && semantics_mltl(#[trigger] drop(pi, m), tx);
            assert(semantics_mltl(drop(pi, m), tx));
        } else {
            release_block_semantics(a, b, l, s, x, y, pi, i);
            block_bounds(a, b, l, s, i);
            if semantics_mltl_ext(pi, release_block(x, y, s, i)) {
                let m = choose|m: nat| s[i] <= m <= s[i + 1] - 1 && semantics_mltl(#[trigger] drop(pi, m), tx);
                assert(s[0] <= m < s[j]);
                assert(!semantics_mltl(drop(pi, m), tx));
            }
        }
    }
}

} // verus!
