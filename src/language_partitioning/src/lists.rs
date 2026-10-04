//! Lemmas about the list builders (`pairs`, `And_mltl_list`, …).
//!
//! Mirrors `MLTL_Language_Partition_Proof.thy`, section "Lemmas for MLTL
//! operators that operate over lists of mltl formulas", plus helpers (not in
//! Isabelle) that lift satisfaction and disjointness through the builders.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::parse_tree::*;
use crate::ext::*;
use crate::algorithm::*;

verus! {

// ---------------------------------------------------------------------------
// Membership in appended / concatenated lists
// ---------------------------------------------------------------------------

/// `set (A @ B) = set A ∪ set B`
pub proof fn list_concat_set_union<T>(a: Seq<T>, b: Seq<T>, x: T)
    ensures
        (a + b).contains(x) <==> (a.contains(x) || b.contains(x)),
{
    if (a + b).contains(x) {
        let i = choose|i: int| 0 <= i < (a + b).len() && (a + b)[i] == x;
        if i < a.len() {
            assert(a[i] == x);
        } else {
            assert(b[i - a.len()] == x);
        }
    }
    if a.contains(x) {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == x;
        assert((a + b)[i] == x);
    }
    if b.contains(x) {
        let i = choose|i: int| 0 <= i < b.len() && b[i] == x;
        assert((a + b)[a.len() + i] == x);
    }
}

/// Not in Isabelle: `x ∈ set (concat xss) ⟷ ∃j. x ∈ set (xss!j)`.
pub proof fn concat_member<T>(xss: Seq<Seq<T>>, x: T)
    ensures
        concat(xss).contains(x) <==> exists|j: int| 0 <= j < xss.len() && #[trigger] xss[j].contains(x),
    decreases xss.len(),
{
    if xss.len() > 0 {
        let init = xss.drop_last();
        concat_member(init, x);
        list_concat_set_union(concat(init), xss.last(), x);
        if exists|j: int| 0 <= j < xss.len() && #[trigger] xss[j].contains(x) {
            let j = choose|j: int| 0 <= j < xss.len() && #[trigger] xss[j].contains(x);
            if j < init.len() {
                assert(init[j] == xss[j]);
            }
        }
        if exists|j: int| 0 <= j < init.len() && #[trigger] init[j].contains(x) {
            let j = choose|j: int| 0 <= j < init.len() && #[trigger] init[j].contains(x);
            assert(xss[j] == init[j]);
        }
    }
}

// ---------------------------------------------------------------------------
// pairs
// ---------------------------------------------------------------------------

/// `pairs A [] = []`
pub proof fn pairs_empty_list<T>(a: Seq<T>)
    ensures
        pairs(a, Seq::<T>::empty()) == Seq::<(T, T)>::empty(),
    decreases a.len(),
{
    if a.len() > 0 {
        pairs_empty_list(a.drop_first());
        assert(pairs(a, Seq::<T>::empty()) =~= Seq::<(T, T)>::empty());
    }
}

/// `(member A (fst x) ∧ member B (snd x)) ⟷ member (pairs A B) x`
pub proof fn pairs_member<T>(a: Seq<T>, b: Seq<T>, x: (T, T))
    ensures
        (a.contains(x.0) && b.contains(x.1)) <==> pairs(a, b).contains(x),
    decreases a.len(),
{
    if a.len() > 0 {
        let m = b.map_values(|y: T| (a[0], y));
        let rest = a.drop_first();
        pairs_member(rest, b, x);
        list_concat_set_union(m, pairs(rest, b), x);
        if m.contains(x) {
            let i = choose|i: int| 0 <= i < m.len() && m[i] == x;
            assert(b[i] == x.1);
            assert(a[0] == x.0);
        }
        if a.contains(x.0) && b.contains(x.1) {
            let i = choose|i: int| 0 <= i < a.len() && a[i] == x.0;
            let j = choose|j: int| 0 <= j < b.len() && b[j] == x.1;
            if i == 0 {
                assert(m[j] == x);
            } else {
                assert(rest[i - 1] == x.0);
            }
        }
        if rest.contains(x.0) {
            let i = choose|i: int| 0 <= i < rest.len() && rest[i] == x.0;
            assert(a[i + 1] == x.0);
        }
    }
}

/// `member (pairs A B) x ⟹ member A (fst x) ∧ member B (snd x)`
pub proof fn pairs_member_forward<T>(a: Seq<T>, b: Seq<T>, x: (T, T))
    requires
        pairs(a, b).contains(x),
    ensures
        a.contains(x.0) && b.contains(x.1),
{
    pairs_member(a, b, x);
}

/// `member (pairs A B) x ⟹ member A (fst x)`
pub proof fn pairs_member_fst_forward<T>(a: Seq<T>, b: Seq<T>, x: (T, T))
    requires
        pairs(a, b).contains(x),
    ensures
        a.contains(x.0),
{
    pairs_member(a, b, x);
}

/// `member (pairs A B) x ⟹ member B (snd x)`
pub proof fn pairs_member_snd_forward<T>(a: Seq<T>, b: Seq<T>, x: (T, T))
    requires
        pairs(a, b).contains(x),
    ensures
        b.contains(x.1),
{
    pairs_member(a, b, x);
}

/// `member A (fst x) ⟹ member B (snd x) ⟹ member (pairs A B) x`
pub proof fn pairs_member_converse<T>(a: Seq<T>, b: Seq<T>, x: (T, T))
    requires
        a.contains(x.0),
        b.contains(x.1),
    ensures
        pairs(a, b).contains(x),
{
    pairs_member(a, b, x);
}

/// `set (pairs L1 (h2#T2)) = set (map (λx. (x, h2)) L1 @ pairs L1 T2)`
pub proof fn pairs_alt<T>(l1: Seq<T>, h2: T, t2: Seq<T>, x: (T, T))
    ensures
        pairs(l1, seq![h2] + t2).contains(x)
            <==> (l1.map_values(|y: T| (y, h2)) + pairs(l1, t2)).contains(x),
{
    let m = l1.map_values(|y: T| (y, h2));
    pairs_member(l1, seq![h2] + t2, x);
    pairs_member(l1, t2, x);
    list_concat_set_union(m, pairs(l1, t2), x);
    list_concat_set_union(seq![h2], t2, x.1);
    if m.contains(x) {
        let i = choose|i: int| 0 <= i < m.len() && m[i] == x;
        assert(l1[i] == x.0);
        assert(seq![h2][0] == x.1);
    }
    if l1.contains(x.0) && x.1 == h2 {
        let i = choose|i: int| 0 <= i < l1.len() && l1[i] == x.0;
        assert(m[i] == x);
    }
    assert(seq![h2].contains(x.1) ==> x.1 == h2);
}

// ---------------------------------------------------------------------------
// And_mltl_list and the map-based builders
// ---------------------------------------------------------------------------

/// `member (And_mltl_list D_x D_y) ψ ⟹ ∃ψ1 ψ2. ψ = And_mltl_ext ψ1 ψ2 ∧ member D_x ψ1 ∧ member D_y ψ2`
/// (returns `(ψ1, ψ2)`).
pub proof fn And_mltl_list_member_forward<A>(dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>, psi: MltlExt<A>)
    -> (r: (MltlExt<A>, MltlExt<A>))
    requires
        And_mltl_list_spec(dx, dy).contains(psi),
    ensures
        psi == and_mltl_ext(r.0, r.1),
        dx.contains(r.0),
        dy.contains(r.1),
{
    let p = pairs(dx, dy);
    let i = choose|i: int| 0 <= i < And_mltl_list_spec(dx, dy).len() && And_mltl_list_spec(dx, dy)[i] == psi;
    assert(p.contains(p[i]));
    pairs_member(dx, dy, p[i]);
    p[i]
}

/// `∃ψ1 ψ2. ψ = And_mltl_ext ψ1 ψ2 ∧ member D_x ψ1 ∧ member D_y ψ2 ⟹ member (And_mltl_list D_x D_y) ψ`
pub proof fn And_mltl_list_member_converse<A>(dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>, psi1: MltlExt<A>, psi2: MltlExt<A>)
    requires
        dx.contains(psi1),
        dy.contains(psi2),
    ensures
        And_mltl_list_spec(dx, dy).contains(and_mltl_ext(psi1, psi2)),
{
    let p = pairs(dx, dy);
    pairs_member(dx, dy, (psi1, psi2));
    let i = choose|i: int| 0 <= i < p.len() && p[i] == (psi1, psi2);
    assert(And_mltl_list_spec(dx, dy)[i] == and_mltl_ext(psi1, psi2));
}

/// `(∃ψ1 ψ2. ψ = And_mltl_ext ψ1 ψ2 ∧ member D_x ψ1 ∧ member D_y ψ2) ⟷ member (And_mltl_list D_x D_y) ψ`
pub proof fn And_mltl_list_member<A>(dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>, psi: MltlExt<A>)
    ensures
        (exists|psi1: MltlExt<A>, psi2: MltlExt<A>|
            psi == and_mltl_ext(psi1, psi2) && dx.contains(psi1) && dy.contains(psi2))
            <==> And_mltl_list_spec(dx, dy).contains(psi),
{
    if And_mltl_list_spec(dx, dy).contains(psi) {
        let r = And_mltl_list_member_forward(dx, dy, psi);
        assert(psi == and_mltl_ext(r.0, r.1) && dx.contains(r.0) && dy.contains(r.1));
    }
    if exists|psi1: MltlExt<A>, psi2: MltlExt<A>|
        psi == and_mltl_ext(psi1, psi2) && dx.contains(psi1) && dy.contains(psi2) {
        let (psi1, psi2) = choose|psi1: MltlExt<A>, psi2: MltlExt<A>|
            psi == and_mltl_ext(psi1, psi2) && dx.contains(psi1) && dy.contains(psi2);
        And_mltl_list_member_converse(dx, dy, psi1, psi2);
    }
}

/// Not in Isabelle: lengths of the builders.
pub proof fn And_mltl_list_len<A>(dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>)
    ensures
        And_mltl_list_spec(dx, dy).len() == dx.len() * dy.len(),
    decreases dx.len(),
{
    if dx.len() > 0 {
        And_mltl_list_len(dx.drop_first(), dy);
        assert(dx.len() * dy.len() == dy.len() + (dx.len() - 1) * dy.len()) by (nonlinear_arith);
    }
}

/// Not in Isabelle: `ψ ∈ Global_mltl_list D a b L ⟷ ∃x ∈ D. ψ = G_c[a,b]<L> x`.
pub proof fn Global_mltl_list_member<A>(d: Seq<MltlExt<A>>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>)
    ensures
        Global_mltl_list_spec(d, a, b, l).contains(y) <==> exists|x: MltlExt<A>| d.contains(x) && y == global_mltl_ext(a, b, l, x),
{
    let m = Global_mltl_list_spec(d, a, b, l);
    if m.contains(y) {
        let i = choose|i: int| 0 <= i < m.len() && m[i] == y;
        assert(d.contains(d[i]));
    }
    if exists|x: MltlExt<A>| d.contains(x) && y == global_mltl_ext(a, b, l, x) {
        let x = choose|x: MltlExt<A>| d.contains(x) && y == global_mltl_ext(a, b, l, x);
        let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
        assert(m[i] == y);
    }
}

/// Not in Isabelle: `ψ ∈ Future_mltl_list D a b L ⟷ ∃x ∈ D. ψ = F_c[a,b]<L> x`.
pub proof fn Future_mltl_list_member<A>(d: Seq<MltlExt<A>>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>)
    ensures
        Future_mltl_list_spec(d, a, b, l).contains(y) <==> exists|x: MltlExt<A>| d.contains(x) && y == future_mltl_ext(a, b, l, x),
{
    let m = Future_mltl_list_spec(d, a, b, l);
    if m.contains(y) {
        let i = choose|i: int| 0 <= i < m.len() && m[i] == y;
        assert(d.contains(d[i]));
    }
    if exists|x: MltlExt<A>| d.contains(x) && y == future_mltl_ext(a, b, l, x) {
        let x = choose|x: MltlExt<A>| d.contains(x) && y == future_mltl_ext(a, b, l, x);
        let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
        assert(m[i] == y);
    }
}

/// Not in Isabelle: `ψ ∈ Until_mltl_list φ D a b L ⟷ ∃x ∈ D. ψ = φ U_c[a,b]<L> x`.
pub proof fn Until_mltl_list_member<A>(phi: MltlExt<A>, d: Seq<MltlExt<A>>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>)
    ensures
        Until_mltl_list_spec(phi, d, a, b, l).contains(y) <==> exists|x: MltlExt<A>| d.contains(x) && y == until_mltl_ext(phi, a, b, l, x),
{
    let m = Until_mltl_list_spec(phi, d, a, b, l);
    if m.contains(y) {
        let i = choose|i: int| 0 <= i < m.len() && m[i] == y;
        assert(d.contains(d[i]));
    }
    if exists|x: MltlExt<A>| d.contains(x) && y == until_mltl_ext(phi, a, b, l, x) {
        let x = choose|x: MltlExt<A>| d.contains(x) && y == until_mltl_ext(phi, a, b, l, x);
        let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
        assert(m[i] == y);
    }
}

/// Not in Isabelle: `ψ ∈ Mighty_Release_mltl_list D ψ' a b L ⟷ ∃x ∈ D. ψ = Mighty_Release_mltl_ext x ψ' a b L`.
pub proof fn Mighty_Release_mltl_list_member<A>(d: Seq<MltlExt<A>>, psi: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>)
    ensures
        Mighty_Release_mltl_list_spec(d, psi, a, b, l).contains(y)
            <==> exists|x: MltlExt<A>| d.contains(x) && y == Mighty_Release_mltl_ext(x, psi, a, b, l),
{
    let m = Mighty_Release_mltl_list_spec(d, psi, a, b, l);
    if m.contains(y) {
        let i = choose|i: int| 0 <= i < m.len() && m[i] == y;
        assert(d.contains(d[i]));
    }
    if exists|x: MltlExt<A>| d.contains(x) && y == Mighty_Release_mltl_ext(x, psi, a, b, l) {
        let x = choose|x: MltlExt<A>| d.contains(x) && y == Mighty_Release_mltl_ext(x, psi, a, b, l);
        let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
        assert(m[i] == y);
    }
}

/// Not in Isabelle: `ψ ∈ Release_mltl_list D ψ' a b L ⟷ ∃x ∈ D. ψ = x R_c[a,b]<L> ψ'`.
pub proof fn Release_mltl_list_member<A>(d: Seq<MltlExt<A>>, psi: MltlExt<A>, a: usize, b: usize, l: Seq<usize>, y: MltlExt<A>)
    ensures
        Release_mltl_list(d, psi, a, b, l).contains(y)
            <==> exists|x: MltlExt<A>| d.contains(x) && y == release_mltl_ext(x, a, b, l, psi),
{
    let m = Release_mltl_list(d, psi, a, b, l);
    if m.contains(y) {
        let i = choose|i: int| 0 <= i < m.len() && m[i] == y;
        assert(d.contains(d[i]));
    }
    if exists|x: MltlExt<A>| d.contains(x) && y == release_mltl_ext(x, a, b, l, psi) {
        let x = choose|x: MltlExt<A>| d.contains(x) && y == release_mltl_ext(x, a, b, l, psi);
        let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
        assert(m[i] == y);
    }
}

/// `A ≠ [] ⟹ B ≠ [] ⟹ And_mltl_list A B ≠ []`
pub proof fn And_mltl_list_nonempty<A>(dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>)
    requires
        dx.len() != 0,
        dy.len() != 0,
    ensures
        And_mltl_list_spec(dx, dy).len() != 0,
{
    And_mltl_list_len(dx, dy);
    assert(dx.len() * dy.len() > 0) by (nonlinear_arith)
        requires dx.len() > 0, dy.len() > 0;
}

/// `D ≠ [] ⟹ Global_mltl_decomp D a n L ≠ []`
pub proof fn Global_mltl_decomp_nonempty<A>(d: Seq<MltlExt<A>>, a: usize, n: nat, l: Seq<usize>)
    requires
        d.len() != 0,
    ensures
        Global_mltl_decomp_spec(d, a, n, l).len() != 0,
    decreases n,
{
    if n > 0 {
        Global_mltl_decomp_nonempty(d, a, (n - 1) as nat, l);
        And_mltl_list_nonempty(
            Global_mltl_decomp_spec(d, a, (n - 1) as nat, l),
            Global_mltl_list_spec(d, (a + n) as usize, (a + n) as usize, seq![1usize]),
        );
    }
}

// ---------------------------------------------------------------------------
// Satisfaction and disjointness over lists (not in Isabelle)
// ---------------------------------------------------------------------------

/// Some formula of `D` holds on `π` (Isabelle: `∃ψ ∈ set D. π ⊨_c ψ`).
pub open spec fn sat_some<A>(d: Seq<MltlExt<A>>, pi: Seq<Set<A>>) -> bool {
    exists|psi: MltlExt<A>| d.contains(psi) && semantics_mltl_ext(pi, psi)
}

/// No two different formulas of `D` both hold on `π`.
pub open spec fn disjoint_on<A>(d: Seq<MltlExt<A>>, pi: Seq<Set<A>>) -> bool {
    forall|psi1: MltlExt<A>, psi2: MltlExt<A>|
        d.contains(psi1) && d.contains(psi2) && psi1 != psi2 && semantics_mltl_ext(pi, psi1)
            ==> !semantics_mltl_ext(pi, psi2)
}

pub proof fn sat_some_single<A>(g: MltlExt<A>, pi: Seq<Set<A>>)
    ensures
        sat_some(seq![g], pi) == semantics_mltl_ext(pi, g),
{
    if semantics_mltl_ext(pi, g) {
        assert(seq![g][0] == g);
    }
}

pub proof fn sat_some_append<A>(x: Seq<MltlExt<A>>, y: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    ensures
        sat_some(x + y, pi) == (sat_some(x, pi) || sat_some(y, pi)),
{
    if sat_some(x + y, pi) {
        let psi = choose|psi: MltlExt<A>| (x + y).contains(psi) && semantics_mltl_ext(pi, psi);
        list_concat_set_union(x, y, psi);
    }
    if sat_some(x, pi) {
        let psi = choose|psi: MltlExt<A>| x.contains(psi) && semantics_mltl_ext(pi, psi);
        list_concat_set_union(x, y, psi);
    }
    if sat_some(y, pi) {
        let psi = choose|psi: MltlExt<A>| y.contains(psi) && semantics_mltl_ext(pi, psi);
        list_concat_set_union(x, y, psi);
    }
}

pub proof fn sat_some_concat<A>(xss: Seq<Seq<MltlExt<A>>>, pi: Seq<Set<A>>)
    ensures
        sat_some(concat(xss), pi) == exists|j: int| 0 <= j < xss.len() && #[trigger] sat_some(xss[j], pi),
{
    if sat_some(concat(xss), pi) {
        let psi = choose|psi: MltlExt<A>| concat(xss).contains(psi) && semantics_mltl_ext(pi, psi);
        concat_member(xss, psi);
        let j = choose|j: int| 0 <= j < xss.len() && #[trigger] xss[j].contains(psi);
        assert(sat_some(xss[j], pi));
    }
    if exists|j: int| 0 <= j < xss.len() && #[trigger] sat_some(xss[j], pi) {
        let j = choose|j: int| 0 <= j < xss.len() && #[trigger] sat_some(xss[j], pi);
        let psi = choose|psi: MltlExt<A>| xss[j].contains(psi) && semantics_mltl_ext(pi, psi);
        concat_member(xss, psi);
    }
}

/// `∃ψ ∈ And_mltl_list A B. π ⊨ ψ ⟷ (∃x ∈ A. π ⊨ x) ∧ (∃y ∈ B. π ⊨ y)`
pub proof fn And_mltl_list_sat<A>(dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    ensures
        sat_some(And_mltl_list_spec(dx, dy), pi) == (sat_some(dx, pi) && sat_some(dy, pi)),
{
    if sat_some(And_mltl_list_spec(dx, dy), pi) {
        let psi = choose|psi: MltlExt<A>| And_mltl_list_spec(dx, dy).contains(psi) && semantics_mltl_ext(pi, psi);
        let r = And_mltl_list_member_forward(dx, dy, psi);
        assert(semantics_mltl_ext(pi, r.0) && semantics_mltl_ext(pi, r.1));
    }
    if sat_some(dx, pi) && sat_some(dy, pi) {
        let x = choose|x: MltlExt<A>| dx.contains(x) && semantics_mltl_ext(pi, x);
        let y = choose|y: MltlExt<A>| dy.contains(y) && semantics_mltl_ext(pi, y);
        And_mltl_list_member_converse(dx, dy, x, y);
        assert(semantics_mltl_ext(pi, and_mltl_ext(x, y)));
    }
}

/// A list with at most one element is disjoint.
pub proof fn disjoint_len_le1<A>(d: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        d.len() <= 1,
    ensures
        disjoint_on(d, pi),
{
    assert forall|psi1: MltlExt<A>, psi2: MltlExt<A>|
        d.contains(psi1) && d.contains(psi2) && psi1 != psi2 && semantics_mltl_ext(pi, psi1)
        implies !semantics_mltl_ext(pi, psi2) by {
        let i = choose|i: int| 0 <= i < d.len() && d[i] == psi1;
        let j = choose|j: int| 0 <= j < d.len() && d[j] == psi2;
    }
}

/// Disjoint lists that never hold together append to a disjoint list.
pub proof fn disjoint_append<A>(x: Seq<MltlExt<A>>, y: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        disjoint_on(x, pi),
        disjoint_on(y, pi),
        !(sat_some(x, pi) && sat_some(y, pi)),
    ensures
        disjoint_on(x + y, pi),
{
    assert forall|psi1: MltlExt<A>, psi2: MltlExt<A>|
        (x + y).contains(psi1) && (x + y).contains(psi2) && psi1 != psi2 && semantics_mltl_ext(pi, psi1)
        implies !semantics_mltl_ext(pi, psi2) by {
        list_concat_set_union(x, y, psi1);
        list_concat_set_union(x, y, psi2);
    }
}

/// Disjoint blocks, no two of which hold together, concatenate to a disjoint list.
pub proof fn disjoint_concat<A>(xss: Seq<Seq<MltlExt<A>>>, pi: Seq<Set<A>>)
    requires
        forall|j: int| 0 <= j < xss.len() ==> disjoint_on(#[trigger] xss[j], pi),
        forall|i: int, j: int| #![trigger xss[i], xss[j]]
            0 <= i < xss.len() && 0 <= j < xss.len() && i != j ==> !(sat_some(xss[i], pi) && sat_some(xss[j], pi)),
    ensures
        disjoint_on(concat(xss), pi),
{
    assert forall|psi1: MltlExt<A>, psi2: MltlExt<A>|
        concat(xss).contains(psi1) && concat(xss).contains(psi2) && psi1 != psi2 && semantics_mltl_ext(pi, psi1)
        implies !semantics_mltl_ext(pi, psi2) by {
        concat_member(xss, psi1);
        concat_member(xss, psi2);
        let i = choose|i: int| 0 <= i < xss.len() && #[trigger] xss[i].contains(psi1);
        let j = choose|j: int| 0 <= j < xss.len() && #[trigger] xss[j].contains(psi2);
        if semantics_mltl_ext(pi, psi2) {
            assert(sat_some(xss[i], pi));
            assert(sat_some(xss[j], pi));
            if i == j {
                assert(disjoint_on(xss[i], pi));
            }
        }
    }
}

/// Distinct conjunctions differ in a conjunct, so disjoint lists combine.
pub proof fn And_mltl_list_disjoint<A>(dx: Seq<MltlExt<A>>, dy: Seq<MltlExt<A>>, pi: Seq<Set<A>>)
    requires
        disjoint_on(dx, pi),
        disjoint_on(dy, pi),
    ensures
        disjoint_on(And_mltl_list_spec(dx, dy), pi),
{
    assert forall|psi1: MltlExt<A>, psi2: MltlExt<A>|
        And_mltl_list_spec(dx, dy).contains(psi1) && And_mltl_list_spec(dx, dy).contains(psi2) && psi1 != psi2
            && semantics_mltl_ext(pi, psi1) implies !semantics_mltl_ext(pi, psi2) by {
        let r1 = And_mltl_list_member_forward(dx, dy, psi1);
        let r2 = And_mltl_list_member_forward(dx, dy, psi2);
        assert(semantics_mltl_ext(pi, r1.0) && semantics_mltl_ext(pi, r1.1));
        if semantics_mltl_ext(pi, psi2) {
            assert(semantics_mltl_ext(pi, r2.0) && semantics_mltl_ext(pi, r2.1));
            assert(r1.0 != r2.0 || r1.1 != r2.1);
        }
    }
}

} // verus!
