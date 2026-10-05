//! Correctness of WEST simplification.
//!
//! Mirrors `WEST_Proofs.thy`, sections on `WEST_simp_trace`, `update_L` and
//! `WEST_simp_helper` (`WEST_simp_trace_correct`, `simp_correct`,
//! `WEST_and_simp_correct`, `WEST_or_simp_correct`). Shorter route: two
//! regexes with `check_simp` differ in at most one entry
//! (`check_simp_unique_diff`), and merging them matches exactly the traces
//! either one matches.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithms::*;
use crate::matching::*;

verus! {

// ---------------------------------------------------------------------------
// count_diff: two differing entries cost at least two
// ---------------------------------------------------------------------------

/// A differing entry of equal-length states is counted.
pub proof fn count_diff_state_one(s1: StateRegex, s2: StateRegex, i: int)
    requires
        s1.len() == s2.len(),
        0 <= i < s1.len(),
        s1[i] != s2[i],
    ensures
        count_diff_state(s1, s2) >= 1,
    decreases s1.len(),
{
    if i > 0 {
        let t1 = s1.drop_first();
        let t2 = s2.drop_first();
        assert(t1[i - 1] == s1[i] && t2[i - 1] == s2[i]);
        count_diff_state_one(t1, t2, i - 1);
    }
}

/// Two differing entries of equal-length states are both counted.
pub proof fn count_diff_state_two(s1: StateRegex, s2: StateRegex, i: int, j: int)
    requires
        s1.len() == s2.len(),
        0 <= i < j < s1.len(),
        s1[i] != s2[i],
        s1[j] != s2[j],
    ensures
        count_diff_state(s1, s2) >= 2,
    decreases s1.len(),
{
    let t1 = s1.drop_first();
    let t2 = s2.drop_first();
    assert(t1[j - 1] == s1[j] && t2[j - 1] == s2[j]);
    if i > 0 {
        assert(t1[i - 1] == s1[i] && t2[i - 1] == s2[i]);
        count_diff_state_two(t1, t2, i - 1, j - 1);
    } else {
        count_diff_state_one(t1, t2, j - 1);
    }
}

/// For equal-length regexes, `count_diff` is at least the count at step `k`.
pub proof fn count_diff_ge_state(t1: TraceRegex, t2: TraceRegex, k: int)
    requires
        t1.len() == t2.len(),
        0 <= k < t1.len(),
    ensures
        count_diff(t1, t2) >= count_diff_state(t1[k], t2[k]),
    decreases t1.len(),
{
    if k > 0 {
        let r1 = t1.drop_first();
        let r2 = t2.drop_first();
        assert(r1[k - 1] == t1[k] && r2[k - 1] == t2[k]);
        count_diff_ge_state(r1, r2, k - 1);
    }
}

/// For equal-length regexes, `count_diff` is at least the sum of the counts
/// at two different steps.
pub proof fn count_diff_ge_two_states(t1: TraceRegex, t2: TraceRegex, k: int, l: int)
    requires
        t1.len() == t2.len(),
        0 <= k < l < t1.len(),
    ensures
        count_diff(t1, t2) >= count_diff_state(t1[k], t2[k]) + count_diff_state(t1[l], t2[l]),
    decreases t1.len(),
{
    let r1 = t1.drop_first();
    let r2 = t2.drop_first();
    assert(r1[l - 1] == t1[l] && r2[l - 1] == t2[l]);
    if k > 0 {
        assert(r1[k - 1] == t1[k] && r2[k - 1] == t2[k]);
        count_diff_ge_two_states(r1, r2, k - 1, l - 1);
    } else {
        count_diff_ge_state(r1, r2, l - 1);
    }
}

/// Not in Isabelle: regexes accepted by `check_simp` (with `num_vars`-wide
/// states) differ in at most one entry.
pub proof fn check_simp_unique_diff(t1: TraceRegex, t2: TraceRegex, n: nat, k: int, i: int, l: int, j: int)
    requires
        check_simp_spec(t1, t2),
        trace_regex_of_vars(t1, n),
        trace_regex_of_vars(t2, n),
        0 <= k < t1.len(),
        0 <= l < t1.len(),
        0 <= i < n,
        0 <= j < n,
        t1[k][i] != t2[k][i],
        t1[l][j] != t2[l][j],
    ensures
        k == l && i == j,
{
    assert(t1[k].len() == n && t2[k].len() == n && t1[l].len() == n && t2[l].len() == n);
    if k == l {
        if i < j {
            count_diff_state_two(t1[k], t2[k], i, j);
            count_diff_ge_state(t1, t2, k);
        } else if j < i {
            count_diff_state_two(t1[k], t2[k], j, i);
            count_diff_ge_state(t1, t2, k);
        }
    } else {
        count_diff_state_one(t1[k], t2[k], i);
        count_diff_state_one(t1[l], t2[l], j);
        if k < l {
            count_diff_ge_two_states(t1, t2, k, l);
        } else {
            count_diff_ge_two_states(t1, t2, l, k);
        }
    }
}

// ---------------------------------------------------------------------------
// Merging two regexes
// ---------------------------------------------------------------------------

/// The merged bit allows everything either bit allows; equal bits stay.
pub proof fn WEST_simp_bitwise_ok(b: WestBit, c: WestBit, v: bool)
    ensures
        bit_ok(b, v) ==> bit_ok(WEST_simp_bitwise_spec(b, c), v),
        bit_ok(c, v) ==> bit_ok(WEST_simp_bitwise_spec(b, c), v),
        b == c ==> WEST_simp_bitwise_spec(b, c) == b,
        b != c && !bit_ok(b, v) ==> bit_ok(c, v),
{
}

/// `WEST_simp_trace` of two `check_simp` regexes matches exactly what either
/// matches (Isabelle: `WEST_simp_trace_correct`).
pub proof fn WEST_simp_trace_correct(pi: WestTrace, t1: TraceRegex, t2: TraceRegex, n: nat)
    requires
        check_simp_spec(t1, t2),
        trace_regex_of_vars(t1, n),
        trace_regex_of_vars(t2, n),
    ensures
        match_regex(pi, WEST_simp_trace_spec(t1, t2, n)) <==> (match_regex(pi, t1) || match_regex(pi, t2)),
        trace_regex_of_vars(WEST_simp_trace_spec(t1, t2, n), n),
        WEST_simp_trace_spec(t1, t2, n).len() == t1.len(),
{
    let m = WEST_simp_trace_spec(t1, t2, n);
    assert(m.len() == t1.len());
    assert forall|k: int| 0 <= k < m.len() implies #[trigger] m[k] == WEST_simp_state_spec(t1[k], t2[k]) by {}
    assert forall|k: int| 0 <= k < m.len() implies (#[trigger] m[k]).len() == n by {
        assert(t1[k].len() == n);
    }
    // Every entry of m allows what t1's and t2's entries allow.
    assert forall|k: int, x: int| 0 <= k < m.len() && 0 <= x < n && k < pi.len() implies
        (bit_ok(t1[k][x], atom_in(pi[k], x)) ==> bit_ok(#[trigger] m[k][x], atom_in(pi[k], x)))
        && (bit_ok(t2[k][x], atom_in(pi[k], x)) ==> bit_ok(m[k][x], atom_in(pi[k], x))) by {
        assert(t1[k].len() == n);
        WEST_simp_bitwise_ok(t1[k][x], t2[k][x], atom_in(pi[k], x));
    }
    if match_regex(pi, t1) {
        assert forall|k: int| 0 <= k < m.len() implies match_timestep(#[trigger] pi[k], m[k]) by {
            assert(match_timestep(pi[k], t1[k]));
            match_timestep_iff(pi[k], t1[k]);
            match_timestep_iff(pi[k], m[k]);
            assert(t1[k].len() == n);
        }
    }
    if match_regex(pi, t2) {
        assert forall|k: int| 0 <= k < m.len() implies match_timestep(#[trigger] pi[k], m[k]) by {
            assert(match_timestep(pi[k], t2[k]));
            match_timestep_iff(pi[k], t2[k]);
            match_timestep_iff(pi[k], m[k]);
            assert(t1[k].len() == n && t2[k].len() == n);
        }
    }
    if match_regex(pi, m) {
        if exists|k: int, x: int| 0 <= k < t1.len() && 0 <= x < n && #[trigger] t1[k][x] != t2[k][x] {
            let (k0, x0) = choose|k: int, x: int| 0 <= k < t1.len() && 0 <= x < n && #[trigger] t1[k][x] != t2[k][x];
            let v0 = atom_in(pi[k0], x0);
            assert(match_timestep(pi[k0], m[k0]));
            match_timestep_iff(pi[k0], m[k0]);
            assert(t1[k0].len() == n);
            WEST_simp_bitwise_ok(t1[k0][x0], t2[k0][x0], v0);
            // The single differing entry is S in m; pick the input that allows pi there.
            let use1 = bit_ok(t1[k0][x0], v0);
            let t = if use1 { t1 } else { t2 };
            assert(bit_ok(t[k0][x0], v0));
            assert forall|k: int| 0 <= k < t.len() implies match_timestep(#[trigger] pi[k], t[k]) by {
                assert(match_timestep(pi[k], m[k]));
                match_timestep_iff(pi[k], m[k]);
                match_timestep_iff(pi[k], t[k]);
                assert(t1[k].len() == n && t2[k].len() == n);
                assert forall|x: int| 0 <= x < t[k].len() implies bit_ok(#[trigger] t[k][x], atom_in(pi[k], x)) by {
                    if k == k0 && x == x0 {
                    } else {
                        if t1[k][x] != t2[k][x] {
                            check_simp_unique_diff(t1, t2, n, k, x, k0, x0);
                        }
                        WEST_simp_bitwise_ok(t1[k][x], t2[k][x], atom_in(pi[k], x));
                        assert(bit_ok(m[k][x], atom_in(pi[k], x)));
                    }
                }
            }
        } else {
            assert forall|k: int| 0 <= k < t1.len() implies match_timestep(#[trigger] pi[k], t1[k]) by {
                assert(match_timestep(pi[k], m[k]));
                match_timestep_iff(pi[k], m[k]);
                match_timestep_iff(pi[k], t1[k]);
                assert(t1[k].len() == n);
                assert forall|x: int| 0 <= x < t1[k].len() implies bit_ok(#[trigger] t1[k][x], atom_in(pi[k], x)) by {
                    WEST_simp_bitwise_ok(t1[k][x], t2[k][x], atom_in(pi[k], x));
                    assert(bit_ok(m[k][x], atom_in(pi[k], x)));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// update_L and the simplification loop
// ---------------------------------------------------------------------------

/// Not in Isabelle: `remove_element_at_index` by index.
pub proof fn remove_element_at_index_index<T>(n: nat, l: Seq<T>)
    requires
        n < l.len(),
    ensures
        remove_element_at_index(n, l).len() == l.len() - 1,
        forall|m: int| 0 <= m < l.len() - 1 ==>
            #[trigger] remove_element_at_index(n, l)[m] == if m < n { l[m] } else { l[m + 1] },
{
    let r = remove_element_at_index(n, l);
    assert forall|m: int| 0 <= m < l.len() - 1 implies #[trigger] r[m] == if m < n { l[m] } else { l[m + 1] } by {
        if m < n {
            assert(r[m] == take(l, n)[m]);
        } else {
            assert(r[m] == drop(l, n + 1)[m - n]);
        }
    }
}

/// `update_L` matches the same traces as `L` and keeps `num_vars`.
pub proof fn update_L_correct(pi: WestTrace, l: WestRegex, h: (nat, nat), n: nat)
    requires
        h.0 < h.1 < l.len(),
        check_simp_spec(l[h.0 as int], l[h.1 as int]),
        WEST_regex_of_vars(l, n),
    ensures
        west_match(pi, update_L(l, h, n)) <==> west_match(pi, l),
        WEST_regex_of_vars(update_L(l, h, n), n),
{
    let (i, j) = h;
    let r1 = remove_element_at_index(j, l);
    remove_element_at_index_index(j, l);
    let r = remove_element_at_index(i, r1);
    remove_element_at_index_index(i, r1);
    let merged = WEST_simp_trace_spec(l[i as int], l[j as int], n);
    assert(trace_regex_of_vars(l[i as int], n) && trace_regex_of_vars(l[j as int], n));
    WEST_simp_trace_correct(pi, l[i as int], l[j as int], n);
    // r holds exactly the traces of l other than those at i and j.
    assert forall|m: int| 0 <= m < r.len() implies #[trigger] r[m] == l[
        if m < i { m } else if m + 1 < j { m + 1 } else { m + 2 }] by {}
    assert(WEST_regex_of_vars(r, n)) by {
        assert forall|m: int| 0 <= m < r.len() implies trace_regex_of_vars(#[trigger] r[m], n) by {
            let k = if m < i { m } else if m + 1 < j { m + 1 } else { m + 2 };
            assert(r[m] == l[k]);
        }
    }
    regex_of_vars_append(r, seq![merged], n);
    west_match_append(pi, r, seq![merged]);
    west_match_single(pi, merged);
    if west_match(pi, r) {
        let m = choose|m: int| 0 <= m < r.len() && #[trigger] match_regex(pi, r[m]);
        let k = if m < i { m } else if m + 1 < j { m + 1 } else { m + 2 };
        assert(r[m] == l[k]);
    }
    if west_match(pi, l) {
        let k = choose|k: int| 0 <= k < l.len() && #[trigger] match_regex(pi, l[k]);
        if k != i && k != j {
            let m = if k < i { k } else if k < j { k - 1 } else { k - 2 };
            assert(r[m] == l[k]);
            assert(match_regex(pi, r[m]));
        }
    }
}

/// `WEST_simp_helper` matches the same traces as its input and keeps
/// `num_vars` (Isabelle: `WEST_simp_helper_correct_forward/converse`).
pub proof fn WEST_simp_helper_correct(pi: WestTrace, l: WestRegex, idx_pairs: Seq<(nat, nat)>, i: nat, n: nat)
    requires
        WEST_regex_of_vars(l, n),
    ensures
        west_match(pi, WEST_simp_helper_spec(l, idx_pairs, i, n)) <==> west_match(pi, l),
        WEST_regex_of_vars(WEST_simp_helper_spec(l, idx_pairs, i, n), n),
    decreases simp_measure(l, idx_pairs, i),
{
    if idx_pairs != enum_pairs(l) || i >= idx_pairs.len() {
    } else {
        enum_pairs_facts(l);
        let h = idx_pairs[i as int];
        if check_simp_spec(l[h.0 as int], l[h.1 as int]) {
            let new_l = update_L(l, h, n);
            update_L_len(l, h, n);
            update_L_correct(pi, l, h, n);
            enum_pairs_facts(new_l);
            let nn = l.len();
            let m = new_l.len();
            assert(m * m * m + m * m < nn * nn * nn) by (nonlinear_arith)
                requires m + 1 == nn;
            WEST_simp_helper_correct(pi, new_l, enum_pairs(new_l), 0, n);
        } else {
            WEST_simp_helper_correct(pi, l, idx_pairs, i + 1, n);
        }
    }
}

/// `match π (WEST_simp L n) ⟷ match π L` (Isabelle: `simp_correct`).
pub proof fn simp_correct(pi: WestTrace, l: WestRegex, n: nat)
    requires
        WEST_regex_of_vars(l, n),
    ensures
        west_match(pi, WEST_simp_spec(l, n)) <==> west_match(pi, l),
        WEST_regex_of_vars(WEST_simp_spec(l, n), n),
{
    WEST_simp_helper_correct(pi, l, enum_pairs(l), 0, n);
}

/// Isabelle: `WEST_and_simp_correct`.
pub proof fn WEST_and_simp_correct(pi: WestTrace, l1: WestRegex, l2: WestRegex, n: nat)
    requires
        WEST_regex_of_vars(l1, n),
        WEST_regex_of_vars(l2, n),
    ensures
        west_match(pi, WEST_and_simp_spec(l1, l2, n)) <==> (west_match(pi, l1) && west_match(pi, l2)),
        WEST_regex_of_vars(WEST_and_simp_spec(l1, l2, n), n),
{
    WEST_and_correct(pi, l1, l2, n);
    simp_correct(pi, WEST_and_spec(l1, l2), n);
}

/// Isabelle: `WEST_or_simp_correct`.
pub proof fn WEST_or_simp_correct(pi: WestTrace, l1: WestRegex, l2: WestRegex, n: nat)
    requires
        WEST_regex_of_vars(l1, n),
        WEST_regex_of_vars(l2, n),
    ensures
        west_match(pi, WEST_or_simp_spec(l1, l2, n)) <==> (west_match(pi, l1) || west_match(pi, l2)),
        WEST_regex_of_vars(WEST_or_simp_spec(l1, l2, n), n),
{
    west_match_append(pi, l1, l2);
    regex_of_vars_append(l1, l2, n);
    simp_correct(pi, l1 + l2, n);
}

} // verus!
