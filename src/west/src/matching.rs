//! Matching lemmas for the list operations: `@`, AND, shift and pad.
//!
//! Mirrors `WEST_Proofs.thy`, sections "Proofs about Traces Matching Regular
//! Expressions" and the AND / shift / pad parts of "WEST Operations". The
//! Isabelle proofs work on `h#t` cases; here most go through an index
//! characterization first (`WEST_and_state_index`, `WEST_and_trace_index`).
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithms::*;

verus! {

// ---------------------------------------------------------------------------
// Well-formed regexes (WEST_Proofs.thy: state/trace/WEST_regex_of_vars)
// ---------------------------------------------------------------------------

/// `trace_regex_of_vars trace num_vars`: every state has `num_vars` entries.
pub open spec fn trace_regex_of_vars(trace: TraceRegex, num_vars: nat) -> bool {
    forall|i: int| 0 <= i < trace.len() ==> (#[trigger] trace[i]).len() == num_vars
}

/// `WEST_regex_of_vars traceList num_vars`
pub open spec fn WEST_regex_of_vars(trace_list: WestRegex, num_vars: nat) -> bool {
    forall|k: int| 0 <= k < trace_list.len() ==> trace_regex_of_vars(#[trigger] trace_list[k], num_vars)
}

/// Not in Isabelle: bit `b` allows the atom value `v`.
pub open spec fn bit_ok(b: WestBit, v: bool) -> bool {
    (b == WestBit::One ==> v) && (b == WestBit::Zero ==> !v)
}

pub proof fn match_timestep_iff(state: Set<usize>, s: StateRegex)
    ensures
        match_timestep(state, s) <==> forall|x: int| 0 <= x < s.len() ==> bit_ok(#[trigger] s[x], atom_in(state, x)),
{
}

// ---------------------------------------------------------------------------
// Lists of regexes
// ---------------------------------------------------------------------------

/// `match π (L1 @ L2) ⟷ match π L1 ∨ match π L2` (Isabelle: `WEST_or_correct`).
pub proof fn west_match_append(pi: WestTrace, l1: WestRegex, l2: WestRegex)
    ensures
        west_match(pi, l1 + l2) <==> (west_match(pi, l1) || west_match(pi, l2)),
{
    let l = l1 + l2;
    if west_match(pi, l) {
        let i = choose|i: int| 0 <= i < l.len() && #[trigger] match_regex(pi, l[i]);
        if i < l1.len() {
            assert(l[i] == l1[i]);
        } else {
            assert(l[i] == l2[i - l1.len()]);
        }
    }
    if west_match(pi, l1) {
        let i = choose|i: int| 0 <= i < l1.len() && #[trigger] match_regex(pi, l1[i]);
        assert(l[i] == l1[i]);
    }
    if west_match(pi, l2) {
        let i = choose|i: int| 0 <= i < l2.len() && #[trigger] match_regex(pi, l2[i]);
        assert(l[l1.len() + i] == l2[i]);
    }
}

pub proof fn west_match_single(pi: WestTrace, t: TraceRegex)
    ensures
        west_match(pi, seq![t]) <==> match_regex(pi, t),
{
    if match_regex(pi, t) {
        assert(seq![t][0] == t);
    }
}

pub proof fn west_match_cons(pi: WestTrace, t: TraceRegex, rest: WestRegex)
    ensures
        west_match(pi, seq![t] + rest) <==> (match_regex(pi, t) || west_match(pi, rest)),
{
    west_match_append(pi, seq![t], rest);
    west_match_single(pi, t);
}

pub proof fn west_match_empty(pi: WestTrace)
    ensures
        !west_match(pi, Seq::<TraceRegex>::empty()),
{
}

pub proof fn regex_of_vars_append(l1: WestRegex, l2: WestRegex, n: nat)
    requires
        WEST_regex_of_vars(l1, n),
        WEST_regex_of_vars(l2, n),
    ensures
        WEST_regex_of_vars(l1 + l2, n),
{
    assert forall|k: int| 0 <= k < (l1 + l2).len() implies trace_regex_of_vars(#[trigger] (l1 + l2)[k], n) by {
        if k < l1.len() {
            assert((l1 + l2)[k] == l1[k]);
        } else {
            assert((l1 + l2)[k] == l2[k - l1.len()]);
        }
    }
}

pub proof fn regex_of_vars_drop_first(l: WestRegex, n: nat)
    requires
        WEST_regex_of_vars(l, n),
        l.len() > 0,
    ensures
        WEST_regex_of_vars(l.drop_first(), n),
        trace_regex_of_vars(l[0], n),
{
    assert forall|k: int| 0 <= k < l.drop_first().len() implies trace_regex_of_vars(#[trigger] l.drop_first()[k], n) by {
        assert(l.drop_first()[k] == l[k + 1]);
    }
}

// ---------------------------------------------------------------------------
// AND
// ---------------------------------------------------------------------------

/// The bitwise AND allows exactly the values both bits allow; `None` allows
/// none.
pub proof fn WEST_and_bitwise_ok(b: WestBit, c: WestBit, v: bool)
    ensures
        WEST_and_bitwise_spec(b, c) is Some ==>
            (bit_ok(WEST_and_bitwise_spec(b, c)->Some_0, v) <==> (bit_ok(b, v) && bit_ok(c, v))),
        WEST_and_bitwise_spec(b, c) is None ==> !(bit_ok(b, v) && bit_ok(c, v)),
{
}

/// Not in Isabelle: `WEST_and_state` entry by entry.
pub proof fn WEST_and_state_index(s1: StateRegex, s2: StateRegex)
    ensures
        WEST_and_state_spec(s1, s2) is Some <==> (s1.len() == s2.len()
            && forall|k: int| 0 <= k < s1.len() ==> #[trigger] WEST_and_bitwise_spec(s1[k], s2[k]) is Some),
        WEST_and_state_spec(s1, s2) is Some ==> (WEST_and_state_spec(s1, s2)->Some_0.len() == s1.len()
            && forall|k: int| 0 <= k < s1.len() ==>
                #[trigger] WEST_and_state_spec(s1, s2)->Some_0[k] == WEST_and_bitwise_spec(s1[k], s2[k])->Some_0),
    decreases s1.len(),
{
    if s1.len() > 0 && s2.len() > 0 {
        let t1 = s1.drop_first();
        let t2 = s2.drop_first();
        WEST_and_state_index(t1, t2);
        match WEST_and_bitwise_spec(s1[0], s2[0]) {
            None => {},
            Some(b) => {
                if WEST_and_state_spec(t1, t2) is Some {
                    let l = WEST_and_state_spec(t1, t2)->Some_0;
                    assert forall|k: int| 0 <= k < s1.len() implies #[trigger] WEST_and_bitwise_spec(s1[k], s2[k]) is Some by {
                        if k > 0 {
                            assert(s1[k] == t1[k - 1] && s2[k] == t2[k - 1]);
                        }
                    }
                    assert forall|k: int| 0 <= k < s1.len() implies
                        #[trigger] WEST_and_state_spec(s1, s2)->Some_0[k] == WEST_and_bitwise_spec(s1[k], s2[k])->Some_0 by {
                        if k > 0 {
                            assert(s1[k] == t1[k - 1] && s2[k] == t2[k - 1]);
                            assert((seq![b] + l)[k] == l[k - 1]);
                        }
                    }
                } else if s1.len() == s2.len() {
                    let k = choose|k: int| 0 <= k < t1.len() && !(#[trigger] WEST_and_bitwise_spec(t1[k], t2[k]) is Some);
                    assert(s1[k + 1] == t1[k] && s2[k + 1] == t2[k]);
                }
            },
        }
    }
}

/// `WEST_and_state` matches exactly the states both inputs match.
pub proof fn WEST_and_state_match(state: Set<usize>, s1: StateRegex, s2: StateRegex)
    requires
        s1.len() == s2.len(),
    ensures
        WEST_and_state_spec(s1, s2) is Some ==> (WEST_and_state_spec(s1, s2)->Some_0.len() == s1.len()
            && (match_timestep(state, WEST_and_state_spec(s1, s2)->Some_0)
                <==> (match_timestep(state, s1) && match_timestep(state, s2)))),
        WEST_and_state_spec(s1, s2) is None ==> !(match_timestep(state, s1) && match_timestep(state, s2)),
{
    WEST_and_state_index(s1, s2);
    match_timestep_iff(state, s1);
    match_timestep_iff(state, s2);
    if WEST_and_state_spec(s1, s2) is Some {
        let s = WEST_and_state_spec(s1, s2)->Some_0;
        match_timestep_iff(state, s);
        assert forall|x: int| 0 <= x < s.len() implies
            (bit_ok(#[trigger] s[x], atom_in(state, x)) <==> (bit_ok(s1[x], atom_in(state, x)) && bit_ok(s2[x], atom_in(state, x)))) by {
            WEST_and_bitwise_ok(s1[x], s2[x], atom_in(state, x));
        }
        if match_timestep(state, s) {
            assert forall|x: int| 0 <= x < s1.len() implies bit_ok(#[trigger] s1[x], atom_in(state, x)) by {
                assert(bit_ok(s[x], atom_in(state, x)));
            }
            assert forall|x: int| 0 <= x < s2.len() implies bit_ok(#[trigger] s2[x], atom_in(state, x)) by {
                assert(bit_ok(s[x], atom_in(state, x)));
            }
        }
        if match_timestep(state, s1) && match_timestep(state, s2) {
            assert forall|x: int| 0 <= x < s.len() implies bit_ok(#[trigger] s[x], atom_in(state, x)) by {
                assert(bit_ok(s1[x], atom_in(state, x)) && bit_ok(s2[x], atom_in(state, x)));
            }
        }
    } else {
        let k = choose|k: int| 0 <= k < s1.len() && !(#[trigger] WEST_and_bitwise_spec(s1[k], s2[k]) is Some);
        WEST_and_bitwise_ok(s1[k], s2[k], atom_in(state, k));
        if match_timestep(state, s1) && match_timestep(state, s2) {
            assert(bit_ok(s1[k], atom_in(state, k)));
            assert(bit_ok(s2[k], atom_in(state, k)));
        }
    }
}

/// Not in Isabelle: `WEST_and_trace` state by state. The common prefix is
/// ANDed; the longer regex's tail is kept.
pub proof fn WEST_and_trace_index(t1: TraceRegex, t2: TraceRegex)
    ensures
        WEST_and_trace_spec(t1, t2) is Some <==>
            forall|k: int| 0 <= k < t1.len() && k < t2.len() ==> #[trigger] WEST_and_state_spec(t1[k], t2[k]) is Some,
        WEST_and_trace_spec(t1, t2) is Some ==> ({
            let t = WEST_and_trace_spec(t1, t2)->Some_0;
            &&& t.len() == max_nat(t1.len(), t2.len())
            &&& forall|k: int| 0 <= k < t.len() ==> #[trigger] t[k] == (
                if k < t1.len() && k < t2.len() { WEST_and_state_spec(t1[k], t2[k])->Some_0 }
                else if k < t1.len() { t1[k] } else { t2[k] })
        }),
    decreases t1.len(),
{
    if t2.len() == 0 {
    } else if t1.len() == 0 {
    } else {
        let r1 = t1.drop_first();
        let r2 = t2.drop_first();
        WEST_and_trace_index(r1, r2);
        match WEST_and_state_spec(t1[0], t2[0]) {
            None => {},
            Some(state) => {
                if WEST_and_trace_spec(r1, r2) is Some {
                    let tr = WEST_and_trace_spec(r1, r2)->Some_0;
                    let t = seq![state] + tr;
                    assert forall|k: int| 0 <= k < t1.len() && k < t2.len() implies
                        #[trigger] WEST_and_state_spec(t1[k], t2[k]) is Some by {
                        if k > 0 {
                            assert(t1[k] == r1[k - 1] && t2[k] == r2[k - 1]);
                        }
                    }
                    assert forall|k: int| 0 <= k < t.len() implies #[trigger] t[k] == (
                        if k < t1.len() && k < t2.len() { WEST_and_state_spec(t1[k], t2[k])->Some_0 }
                        else if k < t1.len() { t1[k] } else { t2[k] }) by {
                        if k > 0 {
                            assert(t[k] == tr[k - 1]);
                            assert(k - 1 < r1.len() ==> t1[k] == r1[k - 1]);
                            assert(k - 1 < r2.len() ==> t2[k] == r2[k - 1]);
                        }
                    }
                } else {
                    let k = choose|k: int| 0 <= k < r1.len() && k < r2.len() && !(#[trigger] WEST_and_state_spec(r1[k], r2[k]) is Some);
                    assert(t1[k + 1] == r1[k] && t2[k + 1] == r2[k]);
                }
            },
        }
    }
}

/// `WEST_and_trace` matches exactly the traces both inputs match
/// (Isabelle: `WEST_and_trace_correct`), and keeps `num_vars`-wide states.
pub proof fn WEST_and_trace_match(pi: WestTrace, t1: TraceRegex, t2: TraceRegex, n: nat)
    requires
        trace_regex_of_vars(t1, n),
        trace_regex_of_vars(t2, n),
    ensures
        WEST_and_trace_spec(t1, t2) is Some ==> (
            (match_regex(pi, WEST_and_trace_spec(t1, t2)->Some_0) <==> (match_regex(pi, t1) && match_regex(pi, t2)))
            && trace_regex_of_vars(WEST_and_trace_spec(t1, t2)->Some_0, n)),
        WEST_and_trace_spec(t1, t2) is None ==> !(match_regex(pi, t1) && match_regex(pi, t2)),
{
    WEST_and_trace_index(t1, t2);
    if WEST_and_trace_spec(t1, t2) is Some {
        let t = WEST_and_trace_spec(t1, t2)->Some_0;
        assert forall|k: int| 0 <= k < t1.len() && k < t2.len() && k < pi.len() implies
            (match_timestep(pi[k], #[trigger] t[k]) <==> (match_timestep(pi[k], t1[k]) && match_timestep(pi[k], t2[k])))
            && t[k].len() == n by {
            assert(t1[k].len() == n && t2[k].len() == n);
            WEST_and_state_match(pi[k], t1[k], t2[k]);
        }
        assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).len() == n by {
            if k < t1.len() && k < t2.len() {
                assert(t1[k].len() == n && t2[k].len() == n);
                WEST_and_state_index(t1[k], t2[k]);
            } else if k < t1.len() {
                assert(t1[k].len() == n);
            } else {
                assert(t2[k].len() == n);
            }
        }
        if match_regex(pi, t) {
            assert forall|k: int| 0 <= k < t1.len() implies match_timestep(#[trigger] pi[k], t1[k]) by {
                assert(match_timestep(pi[k], t[k]));
            }
            assert forall|k: int| 0 <= k < t2.len() implies match_timestep(#[trigger] pi[k], t2[k]) by {
                assert(match_timestep(pi[k], t[k]));
            }
        }
        if match_regex(pi, t1) && match_regex(pi, t2) {
            assert forall|k: int| 0 <= k < t.len() implies match_timestep(#[trigger] pi[k], t[k]) by {
                if k < t1.len() {
                    assert(match_timestep(pi[k], t1[k]));
                }
                if k < t2.len() {
                    assert(match_timestep(pi[k], t2[k]));
                }
            }
        }
    } else {
        let k = choose|k: int| 0 <= k < t1.len() && k < t2.len() && !(#[trigger] WEST_and_state_spec(t1[k], t2[k]) is Some);
        assert(t1[k].len() == n && t2[k].len() == n);
        if match_regex(pi, t1) && match_regex(pi, t2) {
            WEST_and_state_match(pi[k], t1[k], t2[k]);
            assert(match_timestep(pi[k], t1[k]));
            assert(match_timestep(pi[k], t2[k]));
        }
    }
}

/// `WEST_and_helper trace traces` matches `trace` and some of `traces`.
pub proof fn WEST_and_helper_match(pi: WestTrace, t: TraceRegex, ts: WestRegex, n: nat)
    requires
        trace_regex_of_vars(t, n),
        WEST_regex_of_vars(ts, n),
    ensures
        west_match(pi, WEST_and_helper_spec(t, ts)) <==> (match_regex(pi, t) && west_match(pi, ts)),
        WEST_regex_of_vars(WEST_and_helper_spec(t, ts), n),
    decreases ts.len(),
{
    if ts.len() == 0 {
    } else {
        let rest = ts.drop_first();
        regex_of_vars_drop_first(ts, n);
        WEST_and_helper_match(pi, t, rest, n);
        WEST_and_trace_match(pi, t, ts[0], n);
        assert(ts == seq![ts[0]] + rest);
        west_match_cons(pi, ts[0], rest);
        match WEST_and_trace_spec(t, ts[0]) {
            None => {},
            Some(res) => {
                west_match_cons(pi, res, WEST_and_helper_spec(t, rest));
                regex_of_vars_append(seq![res], WEST_and_helper_spec(t, rest), n);
            },
        }
    }
}

/// `match π (WEST_and L1 L2) ⟷ match π L1 ∧ match π L2`
/// (Isabelle: `WEST_and_correct`), and the result keeps `num_vars`.
pub proof fn WEST_and_correct(pi: WestTrace, l1: WestRegex, l2: WestRegex, n: nat)
    requires
        WEST_regex_of_vars(l1, n),
        WEST_regex_of_vars(l2, n),
    ensures
        west_match(pi, WEST_and_spec(l1, l2)) <==> (west_match(pi, l1) && west_match(pi, l2)),
        WEST_regex_of_vars(WEST_and_spec(l1, l2), n),
    decreases l1.len(),
{
    if l2.len() == 0 {
    } else if l1.len() == 0 {
    } else {
        let rest = l1.drop_first();
        regex_of_vars_drop_first(l1, n);
        WEST_and_correct(pi, rest, l2, n);
        WEST_and_helper_match(pi, l1[0], l2, n);
        let h = WEST_and_helper_spec(l1[0], l2);
        west_match_append(pi, h, WEST_and_spec(rest, l2));
        regex_of_vars_append(h, WEST_and_spec(rest, l2), n);
        assert(l1 == seq![l1[0]] + rest);
        west_match_cons(pi, l1[0], rest);
        if h.len() == 0 {
            assert(h + WEST_and_spec(rest, l2) =~= WEST_and_spec(rest, l2));
        }
    }
}

// ---------------------------------------------------------------------------
// Shift and pad
// ---------------------------------------------------------------------------

/// All-`S` states match every state.
pub proof fn arbitrary_state_match(state: Set<usize>, n: nat)
    ensures
        match_timestep(state, arbitrary_state(n)),
{
}

/// `match_regex π (arbitrary_trace n a @ t) ⟷ a ≤ length π ∧ match_regex (drop a π) t`
pub proof fn shift_trace_match(pi: WestTrace, t: TraceRegex, n: nat, a: nat)
    ensures
        match_regex(pi, arbitrary_trace(n, a) + t) <==> (pi.len() >= a && match_regex(drop(pi, a), t)),
{
    let s = arbitrary_trace(n, a) + t;
    if match_regex(pi, s) {
        assert forall|k: int| 0 <= k < t.len() implies match_timestep(#[trigger] drop(pi, a)[k], t[k]) by {
            assert(s[a + k] == t[k]);
            assert(drop(pi, a)[k] == pi[a + k]);
            assert(match_timestep(pi[a + k], s[a + k]));
        }
    }
    if pi.len() >= a && match_regex(drop(pi, a), t) {
        assert forall|k: int| 0 <= k < s.len() implies match_timestep(#[trigger] pi[k], s[k]) by {
            if k < a {
                assert(s[k] == arbitrary_state(n));
            } else {
                assert(s[k] == t[k - a]);
                assert(drop(pi, a)[k - a] == pi[k]);
                assert(match_timestep(drop(pi, a)[k - a], t[k - a]));
            }
        }
    }
}

/// `match π (shift L n a) ⟷ a ≤ length π ∧ match (drop a π) L`
/// (Isabelle: `shift_match`), and shifting keeps `num_vars`.
pub proof fn shift_correct(pi: WestTrace, l: WestRegex, n: nat, a: nat)
    ensures
        west_match(pi, shift_spec(l, n, a)) <==> (pi.len() >= a && west_match(drop(pi, a), l)),
        WEST_regex_of_vars(l, n) ==> WEST_regex_of_vars(shift_spec(l, n, a), n),
{
    let sl = shift_spec(l, n, a);
    if west_match(pi, sl) {
        let i = choose|i: int| 0 <= i < sl.len() && #[trigger] match_regex(pi, sl[i]);
        shift_trace_match(pi, l[i], n, a);
    }
    if pi.len() >= a && west_match(drop(pi, a), l) {
        let i = choose|i: int| 0 <= i < l.len() && #[trigger] match_regex(drop(pi, a), l[i]);
        shift_trace_match(pi, l[i], n, a);
        assert(match_regex(pi, sl[i]));
    }
    if WEST_regex_of_vars(l, n) {
        assert forall|k: int| 0 <= k < sl.len() implies trace_regex_of_vars(#[trigger] sl[k], n) by {
            let s = arbitrary_trace(n, a) + l[k];
            assert(sl[k] == s);
            assert(trace_regex_of_vars(l[k], n));
            assert forall|i: int| 0 <= i < s.len() implies (#[trigger] s[i]).len() == n by {
                if i >= a {
                    assert(s[i] == l[k][i - a]);
                }
            }
        }
    }
}

/// `match_regex π (pad t n k) ⟷ length t + k ≤ length π ∧ match_regex π t`
pub proof fn pad_match(pi: WestTrace, t: TraceRegex, n: nat, k: nat)
    ensures
        match_regex(pi, pad_spec(t, n, k)) <==> (pi.len() >= t.len() + k && match_regex(pi, t)),
        trace_regex_of_vars(t, n) ==> trace_regex_of_vars(pad_spec(t, n, k), n),
{
    let p = pad_spec(t, n, k);
    if match_regex(pi, p) {
        assert forall|i: int| 0 <= i < t.len() implies match_timestep(#[trigger] pi[i], t[i]) by {
            assert(p[i] == t[i]);
        }
    }
    if pi.len() >= t.len() + k && match_regex(pi, t) {
        assert forall|i: int| 0 <= i < p.len() implies match_timestep(#[trigger] pi[i], p[i]) by {
            if i < t.len() {
                assert(p[i] == t[i]);
            } else {
                assert(p[i] == arbitrary_state(n));
            }
        }
    }
    if trace_regex_of_vars(t, n) {
        assert forall|i: int| 0 <= i < p.len() implies (#[trigger] p[i]).len() == n by {
            if i < t.len() {
                assert(p[i] == t[i]);
            }
        }
    }
}

} // verus!
