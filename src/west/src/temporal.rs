//! Correctness of the WEST temporal operations.
//!
//! Mirrors `WEST_Proofs.thy`, sections on `WEST_global`, `WEST_future`,
//! `WEST_until`, `WEST_release` (`WEST_global_correct`, …). Stated over
//! `shifted π L i` ("the suffix from step `i` exists and matches `L`") rather
//! than over formulas, so `correct.rs` only adds the induction hypothesis.
use vstd::prelude::*;
use mltl_core::mltl::*;
use crate::algorithms::*;
use crate::matching::*;
use crate::simp::*;

verus! {

/// Not in Isabelle: `i ≤ length π ∧ match (drop i π) L`, which is what
/// `match π (shift L n i)` means (`shift_correct`).
pub open spec fn shifted(pi: WestTrace, l: WestRegex, i: nat) -> bool {
    pi.len() >= i && west_match(drop(pi, i), l)
}

/// `∀i∈[a,b]. shifted π L i`
pub open spec fn all_shifted(pi: WestTrace, l: WestRegex, a: nat, b: nat) -> bool {
    forall|i: nat| a <= i <= b ==> #[trigger] shifted(pi, l, i)
}

/// `∃i∈[a,b]. shifted π L i`
pub open spec fn some_shifted(pi: WestTrace, l: WestRegex, a: nat, b: nat) -> bool {
    exists|i: nat| a <= i <= b && #[trigger] shifted(pi, l, i)
}

/// `∃i∈[a,b]. shifted π Lψ i ∧ ∀j∈[a,i). shifted π Lφ j`
pub open spec fn until_shifted(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, a: nat, b: nat) -> bool {
    exists|i: nat| a <= i <= b
        && #[trigger] shifted(pi, l_psi, i) && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, l_phi, j)
}

/// `∃j∈[a,ub]. shifted π Lφ j ∧ ∀k∈[a,j]. shifted π Lψ k`
pub open spec fn release_helper_shifted(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, a: nat, ub: nat) -> bool {
    exists|j: nat| a <= j <= ub
        && #[trigger] shifted(pi, l_phi, j) && forall|k: nat| a <= k <= j ==> #[trigger] shifted(pi, l_psi, k)
}

/// `(∀i∈[a,b]. shifted π Lψ i) ∨ (a < b ∧ ∃j∈[a,b-1]. shifted π Lφ j ∧ ∀k∈[a,j]. shifted π Lψ k)`
pub open spec fn release_shifted(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, a: nat, b: nat) -> bool {
    all_shifted(pi, l_psi, a, b) || (a < b && release_helper_shifted(pi, l_phi, l_psi, a, (b - 1) as nat))
}

/// `match π (WEST_global L a b n) ⟷ ∀i∈[a,b]. shifted π L i`
/// (Isabelle: `WEST_global_correct`).
pub proof fn WEST_global_correct(pi: WestTrace, l: WestRegex, a: nat, b: nat, n: nat)
    requires
        WEST_regex_of_vars(l, n),
        a <= b,
    ensures
        west_match(pi, WEST_global_spec(l, a, b, n)) <==> all_shifted(pi, l, a, b),
        WEST_regex_of_vars(WEST_global_spec(l, a, b, n), n),
    decreases b,
{
    if a == b {
        shift_correct(pi, l, n, a);
        if west_match(pi, WEST_global_spec(l, a, b, n)) {
            assert forall|i: nat| a <= i <= b implies #[trigger] shifted(pi, l, i) by {
                assert(i == a);
            }
        } else {
            assert(!shifted(pi, l, a));
        }
    } else {
        let bm = (b - 1) as nat;
        WEST_global_correct(pi, l, a, bm, n);
        shift_correct(pi, l, n, b);
        WEST_and_simp_correct(pi, shift_spec(l, n, b), WEST_global_spec(l, a, bm, n), n);
        if forall|i: nat| a <= i <= bm ==> #[trigger] shifted(pi, l, i) {
            if shifted(pi, l, b) {
                assert forall|i: nat| a <= i <= b implies #[trigger] shifted(pi, l, i) by {
                    if i < b {
                        assert(i <= bm);
                    }
                }
            }
        } else {
            let i = choose|i: nat| a <= i <= bm && !#[trigger] shifted(pi, l, i);
            assert(!(a <= i <= b ==> shifted(pi, l, i)));
        }
    }
}

/// `match π (WEST_future L a b n) ⟷ ∃i∈[a,b]. shifted π L i`
/// (Isabelle: `WEST_future_correct`).
pub proof fn WEST_future_correct(pi: WestTrace, l: WestRegex, a: nat, b: nat, n: nat)
    requires
        WEST_regex_of_vars(l, n),
        a <= b,
    ensures
        west_match(pi, WEST_future_spec(l, a, b, n)) <==> some_shifted(pi, l, a, b),
        WEST_regex_of_vars(WEST_future_spec(l, a, b, n), n),
    decreases b,
{
    if a == b {
        shift_correct(pi, l, n, a);
        if west_match(pi, WEST_future_spec(l, a, b, n)) {
            assert(shifted(pi, l, a));
        }
    } else {
        let bm = (b - 1) as nat;
        WEST_future_correct(pi, l, a, bm, n);
        shift_correct(pi, l, n, b);
        WEST_or_simp_correct(pi, shift_spec(l, n, b), WEST_future_spec(l, a, bm, n), n);
        if exists|i: nat| a <= i <= b && #[trigger] shifted(pi, l, i) {
            let i = choose|i: nat| a <= i <= b && #[trigger] shifted(pi, l, i);
            if i < b {
                assert(a <= i <= bm);
            }
        }
        if shifted(pi, l, b) {
            assert(a <= b <= b);
        }
    }
}

/// `match π (WEST_until Lφ Lψ a b n) ⟷ ∃i∈[a,b]. shifted π Lψ i ∧
/// ∀j∈[a,i). shifted π Lφ j` (Isabelle: `WEST_until_correct`).
pub proof fn WEST_until_correct(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, a: nat, b: nat, n: nat)
    requires
        WEST_regex_of_vars(l_phi, n),
        WEST_regex_of_vars(l_psi, n),
        a <= b,
    ensures
        west_match(pi, WEST_until_spec(l_phi, l_psi, a, b, n)) <==> until_shifted(pi, l_phi, l_psi, a, b),
        WEST_regex_of_vars(WEST_until_spec(l_phi, l_psi, a, b, n), n),
    decreases b,
{
    if a == b {
        WEST_global_correct(pi, l_psi, a, a, n);
        if west_match(pi, WEST_until_spec(l_phi, l_psi, a, b, n)) {
            assert(shifted(pi, l_psi, a));
            assert(forall|j: nat| a <= j < a ==> #[trigger] shifted(pi, l_phi, j));
        }
        if exists|i: nat| a <= i <= b && #[trigger] shifted(pi, l_psi, i)
            && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, l_phi, j) {
            let i = choose|i: nat| a <= i <= b && #[trigger] shifted(pi, l_psi, i)
                && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, l_phi, j);
            assert forall|k: nat| a <= k <= a implies #[trigger] shifted(pi, l_psi, k) by {
                assert(k == i);
            }
        }
    } else {
        let bm = (b - 1) as nat;
        WEST_until_correct(pi, l_phi, l_psi, a, bm, n);
        WEST_global_correct(pi, l_phi, a, bm, n);
        WEST_global_correct(pi, l_psi, b, b, n);
        let rec = WEST_until_spec(l_phi, l_psi, a, bm, n);
        let gphi = WEST_global_spec(l_phi, a, bm, n);
        let gpsi = WEST_global_spec(l_psi, b, b, n);
        WEST_and_simp_correct(pi, gphi, gpsi, n);
        WEST_or_simp_correct(pi, rec, WEST_and_simp_spec(gphi, gpsi, n), n);
        if west_match(pi, WEST_and_simp_spec(gphi, gpsi, n)) {
            assert(shifted(pi, l_psi, b));
            assert forall|j: nat| a <= j < b implies #[trigger] shifted(pi, l_phi, j) by {
                assert(a <= j <= bm);
            }
        }
        if exists|i: nat| a <= i <= b && #[trigger] shifted(pi, l_psi, i)
            && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, l_phi, j) {
            let i = choose|i: nat| a <= i <= b && #[trigger] shifted(pi, l_psi, i)
                && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, l_phi, j);
            if i < b {
                assert(a <= i <= bm);
            } else {
                assert forall|k: nat| b <= k <= b implies #[trigger] shifted(pi, l_psi, k) by {
                    assert(k == i);
                }
                assert forall|j: nat| a <= j <= bm implies #[trigger] shifted(pi, l_phi, j) by {
                    assert(a <= j < i);
                }
            }
        }
    }
}

/// `match π (WEST_release_helper Lφ Lψ a ub n) ⟷ ∃j∈[a,ub]. shifted π Lφ j ∧
/// ∀k∈[a,j]. shifted π Lψ k`.
pub proof fn WEST_release_helper_correct(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, a: nat, ub: nat, n: nat)
    requires
        WEST_regex_of_vars(l_phi, n),
        WEST_regex_of_vars(l_psi, n),
        a <= ub,
    ensures
        west_match(pi, WEST_release_helper_spec(l_phi, l_psi, a, ub, n)) <==> release_helper_shifted(pi, l_phi, l_psi, a, ub),
        WEST_regex_of_vars(WEST_release_helper_spec(l_phi, l_psi, a, ub, n), n),
    decreases ub,
{
    if a == ub {
        WEST_global_correct(pi, l_phi, a, a, n);
        WEST_global_correct(pi, l_psi, a, a, n);
        WEST_and_simp_correct(pi, WEST_global_spec(l_phi, a, a, n), WEST_global_spec(l_psi, a, a, n), n);
        if west_match(pi, WEST_release_helper_spec(l_phi, l_psi, a, ub, n)) {
            assert(shifted(pi, l_phi, a));
            assert(shifted(pi, l_psi, a));
        }
        if exists|j: nat| a <= j <= ub && #[trigger] shifted(pi, l_phi, j)
            && forall|k: nat| a <= k <= j ==> #[trigger] shifted(pi, l_psi, k) {
            let j = choose|j: nat| a <= j <= ub && #[trigger] shifted(pi, l_phi, j)
                && forall|k: nat| a <= k <= j ==> #[trigger] shifted(pi, l_psi, k);
            assert(j == a);
            assert(shifted(pi, l_psi, a));
            assert forall|k: nat| a <= k <= a implies #[trigger] shifted(pi, l_phi, k) by {}
        }
    } else {
        let um = (ub - 1) as nat;
        WEST_release_helper_correct(pi, l_phi, l_psi, a, um, n);
        WEST_global_correct(pi, l_psi, a, ub, n);
        WEST_global_correct(pi, l_phi, ub, ub, n);
        let rec = WEST_release_helper_spec(l_phi, l_psi, a, um, n);
        let gpsi = WEST_global_spec(l_psi, a, ub, n);
        let gphi = WEST_global_spec(l_phi, ub, ub, n);
        WEST_and_simp_correct(pi, gpsi, gphi, n);
        WEST_or_simp_correct(pi, rec, WEST_and_simp_spec(gpsi, gphi, n), n);
        if west_match(pi, WEST_and_simp_spec(gpsi, gphi, n)) {
            assert(shifted(pi, l_phi, ub));
        }
        if exists|j: nat| a <= j <= ub && #[trigger] shifted(pi, l_phi, j)
            && forall|k: nat| a <= k <= j ==> #[trigger] shifted(pi, l_psi, k) {
            let j = choose|j: nat| a <= j <= ub && #[trigger] shifted(pi, l_phi, j)
                && forall|k: nat| a <= k <= j ==> #[trigger] shifted(pi, l_psi, k);
            if j < ub {
                assert(a <= j <= um);
            } else {
                assert forall|k: nat| ub <= k <= ub implies #[trigger] shifted(pi, l_phi, k) by {}
            }
        }
    }
}

/// `match π (WEST_release Lφ Lψ a b n) ⟷ (∀i∈[a,b]. shifted π Lψ i) ∨
/// (a < b ∧ ∃j∈[a,b-1]. shifted π Lφ j ∧ ∀k∈[a,j]. shifted π Lψ k)`
/// (Isabelle: `WEST_release_correct`).
pub proof fn WEST_release_correct(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, a: nat, b: nat, n: nat)
    requires
        WEST_regex_of_vars(l_phi, n),
        WEST_regex_of_vars(l_psi, n),
        a <= b,
    ensures
        west_match(pi, WEST_release_spec(l_phi, l_psi, a, b, n)) <==> release_shifted(pi, l_phi, l_psi, a, b),
        WEST_regex_of_vars(WEST_release_spec(l_phi, l_psi, a, b, n), n),
{
    WEST_global_correct(pi, l_psi, a, b, n);
    if b > a {
        let bm = (b - 1) as nat;
        WEST_release_helper_correct(pi, l_phi, l_psi, a, bm, n);
        WEST_or_simp_correct(pi, WEST_global_spec(l_psi, a, b, n), WEST_release_helper_spec(l_phi, l_psi, a, bm, n), n);
    }
}

} // verus!
