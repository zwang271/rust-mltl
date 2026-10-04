//! Integer compositions of intervals.
//!
//! Mirrors `MLTL_Language_Partition_Algorithm.thy`, section "List Helper
//! Functions and Properties", and `MLTL_Language_Partition_Proof.thy`,
//! section "Lemmas about Integer Composition".
//!
//! A composition `L` of `n` lists positive widths summing to `n`. For
//! `F[a,b] <L>`, `interval_times a L = [s_0, …, s_m]` gives the block starts:
//! block `i` is `[s_i, s_{i+1} - 1]`, `s_0 = a`, `s_m = b + 1`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use mltl_core::parse_tree::*;
use crate::ext::*;

verus! {

// ---------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------

/// Isabelle `sum_list` on `nat list` (recursion from the back, so that
/// `sum_list (take (i+1) L) = sum_list (take i L) + L!i` is one unfolding).
pub open spec fn sum_list(l: Seq<usize>) -> nat
    decreases l.len(),
{
    if l.len() == 0 {
        0
    } else {
        sum_list(l.drop_last()) + l.last() as nat
    }
}

/// `partial_sum L i = sum_list (take i L)`
pub open spec fn partial_sum(l: Seq<usize>, i: nat) -> nat {
    sum_list(take(l, i))
}

/// `interval_times a L = map (λi. a + partial_sum L i) [0 ..< length L + 1]`
pub open spec fn interval_times(a: nat, l: Seq<usize>) -> Seq<nat> {
    Seq::new((l.len() + 1) as nat, |i: int| a + partial_sum(l, i as nat))
}

/// `is_composition n L ⟷ (∀i∈set L. i > 0) ∧ sum_list L = n`
pub open spec fn is_composition(n: nat, l: Seq<usize>) -> bool {
    (forall|i: int| 0 <= i < l.len() ==> #[trigger] l[i] > 0) && sum_list(l) == n
}

/// `is_composition_MLTL φ`: every composition is one of its interval's
/// length `b - a + 1`.
pub open spec fn is_composition_MLTL<A>(phi: MltlExt<A>) -> bool
    decreases phi,
{
    match phi {
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) =>
            is_composition_MLTL(*x) && is_composition_MLTL(*y),
        MltlParseTree::Global(l, a, b, x) | MltlParseTree::Future(l, a, b, x) =>
            is_composition(nat_sub(b as nat, a as nat) + 1, l) && is_composition_MLTL(*x),
        MltlParseTree::Not(_, x) => is_composition_MLTL(*x),
        MltlParseTree::Until(l, x, a, b, y) | MltlParseTree::Release(l, x, a, b, y) =>
            is_composition(nat_sub(b as nat, a as nat) + 1, l) && is_composition_MLTL(*x)
                && is_composition_MLTL(*y),
        _ => true,
    }
}

/// `is_composition_allones n L = (is_composition n L ∧ (∀i<length L. L!i = 1))`
pub open spec fn is_composition_allones(n: nat, l: Seq<usize>) -> bool {
    is_composition(n, l) && forall|i: int| 0 <= i < l.len() ==> #[trigger] l[i] == 1
}

/// `is_composition_MLTL_allones φ`: every composition is all ones.
pub open spec fn is_composition_MLTL_allones<A>(phi: MltlExt<A>) -> bool
    decreases phi,
{
    match phi {
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) =>
            is_composition_MLTL_allones(*x) && is_composition_MLTL_allones(*y),
        MltlParseTree::Global(l, a, b, x) | MltlParseTree::Future(l, a, b, x) =>
            is_composition_allones(nat_sub(b as nat, a as nat) + 1, l) && is_composition_MLTL_allones(*x),
        MltlParseTree::Not(_, x) => is_composition_MLTL_allones(*x),
        MltlParseTree::Until(l, x, a, b, y) | MltlParseTree::Release(l, x, a, b, y) =>
            is_composition_allones(nat_sub(b as nat, a as nat) + 1, l) && is_composition_MLTL_allones(*x)
                && is_composition_MLTL_allones(*y),
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// Sums
// ---------------------------------------------------------------------------

/// Not in Isabelle: `partial_sum L (i+1) = partial_sum L i + L!i`.
pub proof fn lemma_partial_sum_step(l: Seq<usize>, i: nat)
    requires
        i < l.len(),
    ensures
        partial_sum(l, i + 1) == partial_sum(l, i) + l[i as int] as nat,
{
    assert(take(l, i + 1).drop_last() =~= take(l, i));
}

/// Not in Isabelle: `partial_sum L (length L) = sum_list L`, `partial_sum L 0 = 0`.
pub proof fn lemma_partial_sum_ends(l: Seq<usize>)
    ensures
        partial_sum(l, l.len()) == sum_list(l),
        partial_sum(l, 0) == 0,
{
    assert(take(l, l.len()) =~= l);
}

/// Not in Isabelle: partial sums grow by at least the number of positive
/// entries added: `i ≤ j ≤ length L ⟹ partial_sum L i + (j - i) ≤ partial_sum L j`.
pub proof fn lemma_partial_sum_mono(l: Seq<usize>, i: nat, j: nat)
    requires
        i <= j <= l.len(),
        forall|k: int| 0 <= k < l.len() ==> #[trigger] l[k] > 0,
    ensures
        partial_sum(l, i) + (j - i) <= partial_sum(l, j),
    decreases j - i,
{
    if i < j {
        lemma_partial_sum_mono(l, i, (j - 1) as nat);
        lemma_partial_sum_step(l, (j - 1) as nat);
        assert(l[j - 1] > 0);
    }
}

/// `(∀x∈set xs. 0 < x) ⟹ length xs > 0 ⟹ 0 < sum_list xs`
pub proof fn sum_list_pos(xs: Seq<usize>)
    requires
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] xs[i] > 0,
        xs.len() > 0,
    ensures
        0 < sum_list(xs),
{
    assert(xs[xs.len() - 1] > 0);
}

/// `is_composition n L ⟹ length L ≤ n`
pub proof fn composition_length_ub(n: nat, l: Seq<usize>)
    requires
        is_composition(n, l),
    ensures
        l.len() <= n,
{
    lemma_partial_sum_mono(l, 0, l.len());
    lemma_partial_sum_ends(l);
}

/// `is_composition n L ⟹ n > 0 ⟹ 0 < length L`
pub proof fn composition_length_lb(n: nat, l: Seq<usize>)
    requires
        is_composition(n, l),
        n > 0,
    ensures
        0 < l.len(),
{
}

/// `n > 0 ⟹ is_composition n [n]`
pub proof fn trivial_composition(n: usize)
    requires
        n > 0,
    ensures
        is_composition(n as nat, seq![n]),
{
    reveal_with_fuel(sum_list, 2);
    assert(seq![n].drop_last() =~= Seq::<usize>::empty());
}

// ---------------------------------------------------------------------------
// interval_times
// ---------------------------------------------------------------------------

/// `length (interval_times a L) = length L + 1`
pub proof fn interval_times_length(a: nat, l: Seq<usize>)
    ensures
        interval_times(a, l).len() == l.len() + 1,
{
}

/// `(interval_times a L)!0 = a`
pub proof fn interval_times_first(a: nat, l: Seq<usize>)
    ensures
        interval_times(a, l)[0] == a,
{
    lemma_partial_sum_ends(l);
}

/// `a ≤ b ⟹ is_composition (b-a+1) L ⟹ (interval_times a L)!(length L) = b+1`
pub proof fn interval_times_last(a: nat, b: nat, l: Seq<usize>)
    requires
        a <= b,
        is_composition(nat_sub(b, a) + 1, l),
    ensures
        interval_times(a, l)[l.len() as int] == b + 1,
{
    lemma_partial_sum_ends(l);
}

/// `… ⟹ i < length L ⟹ s!(i+1) - s!i = L!i` (no assumptions needed here).
pub proof fn interval_times_diff(a: nat, l: Seq<usize>, i: nat)
    requires
        i < l.len(),
    ensures
        interval_times(a, l)[i + 1int] - interval_times(a, l)[i as int] == l[i as int],
{
    lemma_partial_sum_step(l, i);
}

/// `… ⟹ i < length L ⟹ s!(i+1) > s!i`
pub proof fn interval_times_diff_ge(a: nat, b: nat, l: Seq<usize>, i: nat)
    requires
        a <= b,
        is_composition(nat_sub(b, a) + 1, l),
        i < l.len(),
    ensures
        interval_times(a, l)[i + 1int] > interval_times(a, l)[i as int],
{
    lemma_partial_sum_step(l, i);
}

/// `… ⟹ j ≤ length L ⟹ i < j ⟹ s!j > s!i` (here with the stronger
/// `s!i + (j - i) ≤ s!j`).
pub proof fn interval_times_diff_ge_general(a: nat, b: nat, l: Seq<usize>, i: nat, j: nat)
    requires
        a <= b,
        is_composition(nat_sub(b, a) + 1, l),
        j <= l.len(),
        i < j,
    ensures
        interval_times(a, l)[j as int] > interval_times(a, l)[i as int],
        interval_times(a, l)[i as int] + (j - i) <= interval_times(a, l)[j as int],
{
    lemma_partial_sum_mono(l, i, j);
}

/// Not in Isabelle: all block facts at once. For a valid composition of
/// `[a,b]`: the starts are increasing, start at `a`, end at `b+1`, and every
/// start `s_i` (`i < length L`) and every end `s_{i+1} - 1` lie in `[a,b]`.
pub proof fn interval_times_facts(a: nat, b: nat, l: Seq<usize>)
    requires
        a <= b,
        is_composition(nat_sub(b, a) + 1, l),
    ensures
        l.len() >= 1,
        interval_times(a, l).len() == l.len() + 1,
        interval_times(a, l)[0] == a,
        interval_times(a, l)[l.len() as int] == b + 1,
        forall|i: int| 0 <= i < l.len() ==>
            #[trigger] interval_times(a, l)[i + 1int] == interval_times(a, l)[i] + l[i],
        forall|i: int, j: int| #![trigger interval_times(a, l)[i], interval_times(a, l)[j]]
            0 <= i < j <= l.len() ==> interval_times(a, l)[i] + (j - i) <= interval_times(a, l)[j],
        forall|i: int| 0 <= i <= l.len() ==> a <= #[trigger] interval_times(a, l)[i] <= b + 1,
{
    interval_times_first(a, l);
    interval_times_last(a, b, l);
    assert forall|i: int| 0 <= i < l.len() implies
        #[trigger] interval_times(a, l)[i + 1int] == interval_times(a, l)[i] + l[i] by {
        lemma_partial_sum_step(l, i as nat);
    }
    assert forall|i: int, j: int| #![trigger interval_times(a, l)[i], interval_times(a, l)[j]]
        0 <= i < j <= l.len() implies interval_times(a, l)[i] + (j - i) <= interval_times(a, l)[j] by {
        lemma_partial_sum_mono(l, i as nat, j as nat);
    }
    assert forall|i: int| 0 <= i <= l.len() implies a <= #[trigger] interval_times(a, l)[i] <= b + 1 by {
        lemma_partial_sum_mono(l, i as nat, l.len());
        lemma_partial_sum_ends(l);
    }
}

/// `value "interval_times 3 [1, 2, 3, 4, 5] = [3, 4, 6, 9, 13, 18]"`
pub proof fn example_interval_times()
    ensures
        interval_times(3, seq![1usize, 2, 3, 4, 5]) == seq![3nat, 4, 6, 9, 13, 18],
{
    let l = seq![1usize, 2, 3, 4, 5];
    lemma_partial_sum_ends(l);
    lemma_partial_sum_step(l, 0);
    lemma_partial_sum_step(l, 1);
    lemma_partial_sum_step(l, 2);
    lemma_partial_sum_step(l, 3);
    lemma_partial_sum_step(l, 4);
    assert(interval_times(3, l) =~= seq![3nat, 4, 6, 9, 13, 18]);
}

/// `L = H@[t] ⟹ k ≤ length L - 1 ⟹ take k H = take k L`
pub proof fn take_prefix<T>(l: Seq<T>, h: Seq<T>, t: T, k: nat)
    requires
        l == h.push(t),
        k <= l.len() - 1,
    ensures
        take(h, k) == take(l, k),
{
    assert(take(h, k) =~= take(l, k));
}

/// `length L ≥ k ⟹ take (k+1) (interval_times a L) = interval_times a (take k L)`
pub proof fn take_interval_times(a: nat, l: Seq<usize>, k: nat)
    requires
        l.len() >= k,
    ensures
        take(interval_times(a, l), k + 1) == interval_times(a, take(l, k)),
{
    assert forall|i: int| 0 <= i < k + 1 implies
        #[trigger] take(interval_times(a, l), k + 1)[i] == interval_times(a, take(l, k))[i] by {
        assert(take(take(l, k), i as nat) =~= take(l, i as nat));
    }
    assert(take(interval_times(a, l), k + 1) =~= interval_times(a, take(l, k)));
}

/// `a ≤ b ⟹ is_composition (b-a+1) L ⟹ s = interval_times a L ⟹ a ≤ t ≤ b ⟹
/// ∃i. s!i ≤ t ∧ t ≤ s!(i+1) - 1 ∧ 0 ≤ i ∧ i < length L` (returns `i`).
pub proof fn interval_times_obtain(a: nat, b: nat, l: Seq<usize>, t: nat) -> (i: nat)
    requires
        a <= b,
        is_composition(nat_sub(b, a) + 1, l),
        a <= t <= b,
    ensures
        i < l.len(),
        interval_times(a, l)[i as int] <= t <= interval_times(a, l)[i + 1int] - 1,
{
    interval_times_facts(a, b, l);
    interval_times_obtain_below(a, l, t, l.len())
}

/// The search behind `interval_times_obtain`: `a ≤ t < s!m` gives a block
/// `i < m` containing `t`.
proof fn interval_times_obtain_below(a: nat, l: Seq<usize>, t: nat, m: nat) -> (i: nat)
    requires
        m <= l.len(),
        a <= t < interval_times(a, l)[m as int],
        interval_times(a, l)[0] == a,
    ensures
        i < m,
        interval_times(a, l)[i as int] <= t <= interval_times(a, l)[i + 1int] - 1,
    decreases m,
{
    if m == 0 {
        assert(false);
        0
    } else if interval_times(a, l)[m - 1] <= t {
        (m - 1) as nat
    } else {
        interval_times_obtain_below(a, l, t, (m - 1) as nat)
    }
}

/// `a ≤ b ⟹ … ⟹ s!1 ≤ t ≤ b ⟹ ∃i. s!i ≤ t ≤ s!(i+1) - 1 ∧ 1 ≤ i < length L`
pub proof fn interval_times_obtain_aux(a: nat, b: nat, l: Seq<usize>, t: nat) -> (i: nat)
    requires
        a <= b,
        is_composition(nat_sub(b, a) + 1, l),
        interval_times(a, l)[1] <= t <= b,
    ensures
        1 <= i < l.len(),
        interval_times(a, l)[i as int] <= t <= interval_times(a, l)[i + 1int] - 1,
{
    interval_times_facts(a, b, l);
    let i = interval_times_obtain(a, b, l, t);
    if i == 0 {
        assert(false);
    }
    i
}

// ---------------------------------------------------------------------------
// All-ones compositions
// ---------------------------------------------------------------------------

/// `∀i<length L. L!i = 1 ⟹ L = map (λi. 1) [0 ..< length L]`
pub proof fn list_allones(l: Seq<usize>)
    requires
        forall|i: int| 0 <= i < l.len() ==> #[trigger] l[i] == 1,
    ensures
        l == Seq::new(l.len(), |i: int| 1usize),
{
    assert(l =~= Seq::new(l.len(), |i: int| 1usize));
}

/// `∀i<length L. L!i = k ⟹ sum_list L = k * length L`
pub proof fn sum_list_constants(l: Seq<usize>, k: nat)
    requires
        forall|i: int| 0 <= i < l.len() ==> #[trigger] l[i] == k,
    ensures
        sum_list(l) == k * l.len(),
    decreases l.len(),
{
    if l.len() > 0 {
        let h = l.drop_last();
        assert forall|i: int| 0 <= i < h.len() implies #[trigger] h[i] == k by {
            assert(h[i] == l[i]);
        }
        sum_list_constants(h, k);
        assert(l[l.len() - 1] == k);
        assert(k * l.len() == k * h.len() + k) by (nonlinear_arith)
            requires l.len() == h.len() + 1;
    }
}

/// `is_composition_allones n L ⟹ length L = n`
pub proof fn length_is_composition_allones(n: nat, l: Seq<usize>)
    requires
        is_composition_allones(n, l),
    ensures
        l.len() == n,
{
    sum_list_constants(l, 1);
}

/// `∀i<length L. L!i = 1 ⟹ i ≤ length L ⟹ partial_sum L i = i`
pub proof fn partial_sum_allones(l: Seq<usize>, i: nat)
    requires
        forall|j: int| 0 <= j < l.len() ==> #[trigger] l[j] == 1,
        i <= l.len(),
    ensures
        partial_sum(l, i) == i,
{
    let t = take(l, i);
    assert forall|j: int| 0 <= j < t.len() implies #[trigger] t[j] == 1 by {
        assert(t[j] == l[j]);
    }
    sum_list_constants(t, 1);
}

/// `a ≤ b ⟹ is_composition_allones (b-a+1) L ⟹ i < length (interval_times a L) ⟹
/// (interval_times a L)!i = a + i`
pub proof fn interval_times_allones(a: nat, b: nat, l: Seq<usize>, i: nat)
    requires
        a <= b,
        is_composition_allones(nat_sub(b, a) + 1, l),
        i < interval_times(a, l).len(),
    ensures
        interval_times(a, l)[i as int] == a + i,
{
    partial_sum_allones(l, i);
}

/// `is_composition_allones n L ⟹ is_composition n L`
pub proof fn allones_implies_is_composition(n: nat, l: Seq<usize>)
    requires
        is_composition_allones(n, l),
    ensures
        is_composition(n, l),
{
}

/// `is_composition_MLTL_allones φ ⟹ is_composition_MLTL φ`
pub proof fn allones_implies_is_composition_MLTL<A>(phi: MltlExt<A>)
    requires
        is_composition_MLTL_allones(phi),
    ensures
        is_composition_MLTL(phi),
    decreases phi,
{
    match phi {
        MltlParseTree::Not(_, x) | MltlParseTree::Global(_, _, _, x) | MltlParseTree::Future(_, _, _, x) =>
            allones_implies_is_composition_MLTL(*x),
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
        | MltlParseTree::Release(_, x, _, _, y) => {
            allones_implies_is_composition_MLTL(*x);
            allones_implies_is_composition_MLTL(*y);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------------
// Compositions and convert_nnf_ext  (Proof.thy, "Helper Lemmas")
// ---------------------------------------------------------------------------

/// `intervals_welldef (to_mltl φ) ⟹ is_composition_MLTL φ ⟹
/// is_composition_MLTL (convert_nnf_ext φ)` (holds without the first assumption).
pub proof fn is_composition_convert_nnf_ext<A>(phi: MltlExt<A>)
    requires
        is_composition_MLTL(phi),
    ensures
        is_composition_MLTL(convert_nnf_ext_spec(phi)),
    decreases depth_mltl(to_mltl(phi)),
{
    reveal_with_fuel(depth_mltl, 3);
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
    reveal_with_fuel(is_composition_MLTL, 2);
    match phi {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
        MltlParseTree::Not(dn, g) => match *g {
            MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
            MltlParseTree::Not(_, x) => is_composition_convert_nnf_ext(*x),
            MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
            | MltlParseTree::Release(_, x, _, _, y) => {
                is_composition_convert_nnf_ext(MltlParseTree::Not(dn, x));
                is_composition_convert_nnf_ext(MltlParseTree::Not(dn, y));
            },
            MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) => {
                is_composition_convert_nnf_ext(MltlParseTree::Not(dn, x));
            },
        },
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
        | MltlParseTree::Release(_, x, _, _, y) => {
            is_composition_convert_nnf_ext(*x);
            is_composition_convert_nnf_ext(*y);
        },
        MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) => {
            is_composition_convert_nnf_ext(*x);
        },
    }
}

/// `intervals_welldef (to_mltl φ) ⟹ is_composition_MLTL_allones φ ⟹
/// is_composition_MLTL_allones (convert_nnf_ext φ)` (holds without the first assumption).
pub proof fn is_composition_allones_convert_nnf_ext<A>(phi: MltlExt<A>)
    requires
        is_composition_MLTL_allones(phi),
    ensures
        is_composition_MLTL_allones(convert_nnf_ext_spec(phi)),
    decreases depth_mltl(to_mltl(phi)),
{
    reveal_with_fuel(depth_mltl, 3);
    reveal_with_fuel(mltl_parse_tree_to_mltl_spec, 3);
    reveal_with_fuel(is_composition_MLTL_allones, 2);
    match phi {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
        MltlParseTree::Not(dn, g) => match *g {
            MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => {},
            MltlParseTree::Not(_, x) => is_composition_allones_convert_nnf_ext(*x),
            MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
            | MltlParseTree::Release(_, x, _, _, y) => {
                is_composition_allones_convert_nnf_ext(MltlParseTree::Not(dn, x));
                is_composition_allones_convert_nnf_ext(MltlParseTree::Not(dn, y));
            },
            MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) => {
                is_composition_allones_convert_nnf_ext(MltlParseTree::Not(dn, x));
            },
        },
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
        | MltlParseTree::Release(_, x, _, _, y) => {
            is_composition_allones_convert_nnf_ext(*x);
            is_composition_allones_convert_nnf_ext(*y);
        },
        MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) => {
            is_composition_allones_convert_nnf_ext(*x);
        },
    }
}

} // verus!
