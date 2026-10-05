//! The WEST algorithm, as specifications.
//!
//! Mirrors `WEST_Algorithms.thy` definition by definition. Isabelle lists are
//! `Seq`s; recursive list functions recurse on `s[0]` / `s.drop_first()` as
//! Isabelle does on `h#t`. Executable versions are in `exec.rs` (D20).
//! Correspondence table: agent-docs/correspondence/west.md.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;

verus! {

// ---------------------------------------------------------------------------
// Custom types
// ---------------------------------------------------------------------------

/// `datatype WEST_bit = Zero | One | S` (`S`: either value).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WestBit {
    Zero,
    One,
    S,
}

/// `state_regex = WEST_bit list`: one entry per atom.
pub type StateRegex = Seq<WestBit>;

/// `trace_regex = WEST_bit list list`: one state per time step.
pub type TraceRegex = Seq<Seq<WestBit>>;

/// `WEST_regex = WEST_bit list list list`: a disjunction of trace regexes.
pub type WestRegex = Seq<Seq<Seq<WestBit>>>;

/// `trace = nat set list` (atoms are `usize`, D19).
pub type WestTrace = Seq<Set<usize>>;

// ---------------------------------------------------------------------------
// Trace regular expressions
// ---------------------------------------------------------------------------

/// `WEST_get_bit regex timestep var`: `S` outside the regex.
pub open spec fn WEST_get_bit(regex: TraceRegex, timestep: nat, var: nat) -> WestBit {
    if timestep >= regex.len() {
        WestBit::S
    } else {
        let regex_index = regex[timestep as int];
        if var >= regex_index.len() {
            WestBit::S
        } else {
            regex_index[var as int]
        }
    }
}

/// `WEST_get_state regex time num_vars`: all-`S` past the end.
pub open spec fn WEST_get_state(regex: TraceRegex, time: nat, num_vars: nat) -> StateRegex {
    if time >= regex.len() {
        Seq::new(num_vars, |k: int| WestBit::S)
    } else {
        regex[time as int]
    }
}

/// Atom `x` (a `nat` position, as in Isabelle) is in `state`. Atoms are
/// `usize` (D19), so a position past `usize::MAX` is never in a state: a
/// `usize` trace is an Isabelle trace whose atoms are all at most `usize::MAX`.
pub open spec fn atom_in(state: Set<usize>, x: int) -> bool {
    0 <= x <= usize::MAX && state.contains(x as usize)
}

/// `match_timestep state regex_state`: every `One` atom is in the state and
/// every `Zero` atom is not.
pub open spec fn match_timestep(state: Set<usize>, regex_state: StateRegex) -> bool {
    forall|x: int| 0 <= x < regex_state.len() ==> (
        (#[trigger] regex_state[x] == WestBit::One ==> atom_in(state, x))
        && (regex_state[x] == WestBit::Zero ==> !atom_in(state, x)))
}

/// `trim_reversed_regex`: drop leading all-`S` states (of a reversed regex).
pub open spec fn trim_reversed_regex(regex: TraceRegex) -> TraceRegex
    decreases regex.len(),
{
    if regex.len() == 0 {
        Seq::empty()
    } else if forall|i: int| 0 <= i < regex[0].len() ==> #[trigger] regex[0][i] == WestBit::S {
        trim_reversed_regex(regex.drop_first())
    } else {
        regex
    }
}

/// `trim_regex regex = rev (trim_reversed_regex (rev regex))`
pub open spec fn trim_regex(regex: TraceRegex) -> TraceRegex {
    trim_reversed_regex(regex.reverse()).reverse()
}

/// `match_regex trace regex`: the trace is at least as long as the regex and
/// matches it at every step.
pub open spec fn match_regex(trace: WestTrace, regex: TraceRegex) -> bool {
    (forall|time: int| 0 <= time < regex.len() ==> match_timestep(#[trigger] trace[time], regex[time]))
    && trace.len() >= regex.len()
}

/// Isabelle `match trace regex_list` (renamed: `match` is a Rust keyword):
/// the trace matches some trace regex of the list.
pub open spec fn west_match(trace: WestTrace, regex_list: WestRegex) -> bool {
    exists|i: int| 0 <= i < regex_list.len() && #[trigger] match_regex(trace, regex_list[i])
}

/// `regex_equiv rl1 rl2`: the two lists match the same traces.
pub open spec fn regex_equiv(rl1: WestRegex, rl2: WestRegex) -> bool {
    forall|pi: WestTrace| #[trigger] west_match(pi, rl1) == west_match(pi, rl2)
}

// ---------------------------------------------------------------------------
// WEST operations: AND
// ---------------------------------------------------------------------------

/// `WEST_and_bitwise b c`: `None` on a `One`/`Zero` clash.
pub open spec fn WEST_and_bitwise_spec(b: WestBit, c: WestBit) -> Option<WestBit> {
    match c {
        WestBit::One => if b == WestBit::Zero { None } else { Some(WestBit::One) },
        WestBit::Zero => if b == WestBit::One { None } else { Some(WestBit::Zero) },
        WestBit::S => Some(b),
    }
}

/// `WEST_and_state s1 s2`: `None` on a clash or different lengths.
pub open spec fn WEST_and_state_spec(s1: StateRegex, s2: StateRegex) -> Option<StateRegex>
    decreases s1.len(),
{
    if s1.len() == 0 && s2.len() == 0 {
        Some(Seq::empty())
    } else if s1.len() > 0 && s2.len() > 0 {
        match WEST_and_bitwise_spec(s1[0], s2[0]) {
            None => None,
            Some(b) => match WEST_and_state_spec(s1.drop_first(), s2.drop_first()) {
                None => None,
                Some(l) => Some(seq![b] + l),
            },
        }
    } else {
        None
    }
}

/// `WEST_and_trace t1 t2`: statewise AND; the longer regex's tail is kept.
pub open spec fn WEST_and_trace_spec(trace1: TraceRegex, trace2: TraceRegex) -> Option<TraceRegex>
    decreases trace1.len(),
{
    if trace2.len() == 0 {
        Some(trace1)
    } else if trace1.len() == 0 {
        Some(trace2)
    } else {
        match WEST_and_state_spec(trace1[0], trace2[0]) {
            None => None,
            Some(state) => match WEST_and_trace_spec(trace1.drop_first(), trace2.drop_first()) {
                None => None,
                Some(trace) => Some(seq![state] + trace),
            },
        }
    }
}

/// `WEST_and_helper trace traces`: AND `trace` with each of `traces`, dropping
/// clashes.
pub open spec fn WEST_and_helper_spec(trace: TraceRegex, traces: WestRegex) -> WestRegex
    decreases traces.len(),
{
    if traces.len() == 0 {
        Seq::empty()
    } else {
        match WEST_and_trace_spec(trace, traces[0]) {
            None => WEST_and_helper_spec(trace, traces.drop_first()),
            Some(res) => seq![res] + WEST_and_helper_spec(trace, traces.drop_first()),
        }
    }
}

/// `WEST_and L1 L2`: all pairwise ANDs, in the order of `L1`, then `L2`.
pub open spec fn WEST_and_spec(trace_list1: WestRegex, trace_list2: WestRegex) -> WestRegex
    decreases trace_list1.len(),
{
    if trace_list2.len() == 0 {
        Seq::empty()
    } else if trace_list1.len() == 0 {
        Seq::empty()
    } else {
        let h = WEST_and_helper_spec(trace_list1[0], trace_list2);
        if h.len() == 0 {
            WEST_and_spec(trace_list1.drop_first(), trace_list2)
        } else {
            h + WEST_and_spec(trace_list1.drop_first(), trace_list2)
        }
    }
}

// ---------------------------------------------------------------------------
// WEST operations: simplification
// ---------------------------------------------------------------------------

/// `WEST_simp_bitwise b c`: `S` where the bits differ.
pub open spec fn WEST_simp_bitwise_spec(b: WestBit, c: WestBit) -> WestBit {
    match c {
        WestBit::S => WestBit::S,
        WestBit::Zero => if b == WestBit::Zero { WestBit::Zero } else { WestBit::S },
        WestBit::One => if b == WestBit::One { WestBit::One } else { WestBit::S },
    }
}

/// `WEST_simp_state s1 s2 = map (λk. WEST_simp_bitwise (s1!k) (s2!k)) [0..<length s1]`
pub open spec fn WEST_simp_state_spec(s1: StateRegex, s2: StateRegex) -> StateRegex {
    Seq::new(s1.len(), |k: int| WEST_simp_bitwise_spec(s1[k], s2[k]))
}

/// `WEST_simp_trace trace1 trace2 num_vars`: statewise merge, padded with
/// all-`S` states to the longer length.
pub open spec fn WEST_simp_trace_spec(trace1: TraceRegex, trace2: TraceRegex, num_vars: nat) -> TraceRegex {
    Seq::new(max_nat(trace1.len(), trace2.len()), |k: int| WEST_simp_state_spec(
        WEST_get_state(trace1, k as nat, num_vars), WEST_get_state(trace2, k as nat, num_vars)))
}

/// `count_nonS_trace`: number of non-`S` entries of a state.
pub open spec fn count_nonS_trace(s: StateRegex) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else if s[0] != WestBit::S {
        1 + count_nonS_trace(s.drop_first())
    } else {
        count_nonS_trace(s.drop_first())
    }
}

/// `count_diff_state s1 s2`: positions where the states differ (an entry
/// missing from the shorter state counts if the other entry is not `S`).
pub open spec fn count_diff_state(s1: StateRegex, s2: StateRegex) -> nat
    decreases s1.len() + s2.len(),
{
    if s1.len() == 0 && s2.len() == 0 {
        0
    } else if s2.len() == 0 {
        count_nonS_trace(s1)
    } else if s1.len() == 0 {
        count_nonS_trace(s2)
    } else {
        (if s1[0] == s2[0] { 0nat } else { 1nat }) + count_diff_state(s1.drop_first(), s2.drop_first())
    }
}

/// `count_diff t1 t2`: total number of differing entries. (As in Isabelle,
/// the `(h#t) []` case counts `count_diff_state [] h + count_diff [] t`.)
pub open spec fn count_diff(trace1: TraceRegex, trace2: TraceRegex) -> nat
    decreases trace1.len() + trace2.len(),
{
    if trace1.len() == 0 && trace2.len() == 0 {
        0
    } else if trace1.len() == 0 {
        count_diff_state(Seq::empty(), trace2[0]) + count_diff(Seq::empty(), trace2.drop_first())
    } else if trace2.len() == 0 {
        count_diff_state(Seq::empty(), trace1[0]) + count_diff(Seq::empty(), trace1.drop_first())
    } else {
        count_diff_state(trace1[0], trace2[0]) + count_diff(trace1.drop_first(), trace2.drop_first())
    }
}

/// `check_simp t1 t2`: same length and at most one differing entry.
pub open spec fn check_simp_spec(trace1: TraceRegex, trace2: TraceRegex) -> bool {
    count_diff(trace1, trace2) <= 1 && trace1.len() == trace2.len()
}

/// `enumerate_pairs xs`: all pairs `(xs!i, xs!j)` with `i < j`, row by row.
pub open spec fn enumerate_pairs(xs: Seq<nat>) -> Seq<(nat, nat)>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else {
        xs.drop_first().map_values(|y: nat| (xs[0], y)) + enumerate_pairs(xs.drop_first())
    }
}

/// `[0 ..< n]`
pub open spec fn upt(n: nat) -> Seq<nat> {
    Seq::new(n, |i: int| i as nat)
}

/// `enum_pairs L = enumerate_pairs [0 ..< length L]`
pub open spec fn enum_pairs<T>(l: Seq<T>) -> Seq<(nat, nat)> {
    enumerate_pairs(upt(l.len()))
}

/// `remove_element_at_index n L = take n L @ drop (n+1) L`
pub open spec fn remove_element_at_index<T>(n: nat, l: Seq<T>) -> Seq<T> {
    take(l, n) + drop(l, n + 1)
}

/// `update_L L h num_vars`: replace the traces at `fst h < snd h` by their
/// merge, appended at the end.
pub open spec fn update_L(l: WestRegex, h: (nat, nat), num_vars: nat) -> WestRegex {
    remove_element_at_index(h.0, remove_element_at_index(h.1, l))
        + seq![WEST_simp_trace_spec(l[h.0 as int], l[h.1 as int], num_vars)]
}

/// Termination measure of `WEST_simp_helper` (Isabelle's `measure`).
pub open spec fn simp_measure(l: WestRegex, idx_pairs: Seq<(nat, nat)>, i: nat) -> int {
    (l.len() * l.len() * l.len() + idx_pairs.len()) as int - i
}

/// `WEST_simp_helper L idx_pairs i num_vars`: scan the pairs from index `i`;
/// on the first mergeable pair, merge and restart from the new list's pairs.
pub open spec fn WEST_simp_helper_spec(l: WestRegex, idx_pairs: Seq<(nat, nat)>, i: nat, num_vars: nat) -> WestRegex
    decreases simp_measure(l, idx_pairs, i),
    via WEST_simp_helper_decreases
{
    if idx_pairs != enum_pairs(l) || i >= idx_pairs.len() {
        l
    } else if check_simp_spec(l[idx_pairs[i as int].0 as int], l[idx_pairs[i as int].1 as int]) {
        let new_l = update_L(l, idx_pairs[i as int], num_vars);
        WEST_simp_helper_spec(new_l, enum_pairs(new_l), 0, num_vars)
    } else {
        WEST_simp_helper_spec(l, idx_pairs, i + 1, num_vars)
    }
}

/// `[lo ..< n]`
pub open spec fn upt_from(lo: nat, n: nat) -> Seq<nat> {
    Seq::new((n - lo) as nat, |i: int| (lo + i) as nat)
}

/// `length (enumerate_pairs [lo..<n]) ≤ (n - lo)²`, and every pair is
/// `(i, j)` with `lo ≤ i < j < n`.
pub proof fn enumerate_pairs_facts(lo: nat, n: nat)
    requires
        lo <= n,
    ensures
        enumerate_pairs(upt_from(lo, n)).len() <= (n - lo) * (n - lo),
        forall|k: int| 0 <= k < enumerate_pairs(upt_from(lo, n)).len() ==>
            lo <= (#[trigger] enumerate_pairs(upt_from(lo, n))[k]).0
            && enumerate_pairs(upt_from(lo, n))[k].0 < enumerate_pairs(upt_from(lo, n))[k].1
            && enumerate_pairs(upt_from(lo, n))[k].1 < n,
    decreases n - lo,
{
    let xs = upt_from(lo, n);
    if lo < n {
        let ys = upt_from(lo + 1, n);
        assert(xs.drop_first() =~= ys);
        enumerate_pairs_facts(lo + 1, n);
        let row = ys.map_values(|y: nat| (xs[0], y));
        let rest = enumerate_pairs(ys);
        assert(enumerate_pairs(xs) == row + rest);
        assert((n - lo) * (n - lo) == (n - (lo + 1)) * (n - (lo + 1)) + 2 * (n - (lo + 1)) + 1) by (nonlinear_arith)
            requires lo < n;
        assert forall|k: int| 0 <= k < enumerate_pairs(xs).len() implies
            lo <= (#[trigger] enumerate_pairs(xs)[k]).0 && enumerate_pairs(xs)[k].0 < enumerate_pairs(xs)[k].1
            && enumerate_pairs(xs)[k].1 < n by {
            if k < row.len() {
                assert(enumerate_pairs(xs)[k] == row[k]);
            } else {
                assert(enumerate_pairs(xs)[k] == rest[k - row.len()]);
            }
        }
    } else {
        assert(xs.len() == 0);
    }
}

/// `enum_pairs L`: length at most `(length L)²`; every pair is `(i, j)` with
/// `i < j < length L` (Isabelle: `length_enum_pairs`, `enum_pairs_fact`,
/// `enum_pairs_bound`).
pub proof fn enum_pairs_facts<T>(l: Seq<T>)
    ensures
        enum_pairs(l).len() <= l.len() * l.len(),
        forall|k: int| 0 <= k < enum_pairs(l).len() ==>
            (#[trigger] enum_pairs(l)[k]).0 < enum_pairs(l)[k].1 && enum_pairs(l)[k].1 < l.len(),
{
    enumerate_pairs_facts(0, l.len());
    assert(upt_from(0, l.len()) =~= upt(l.len()));
}

/// `update_L` shortens the list by one (for a valid pair).
pub proof fn update_L_len(l: WestRegex, h: (nat, nat), num_vars: nat)
    requires
        h.0 < h.1 < l.len(),
    ensures
        update_L(l, h, num_vars).len() == l.len() - 1,
{
    let r1 = remove_element_at_index(h.1, l);
    assert(r1.len() == l.len() - 1);
    assert(remove_element_at_index(h.0, r1).len() == l.len() - 2);
}

#[via_fn]
proof fn WEST_simp_helper_decreases(l: WestRegex, idx_pairs: Seq<(nat, nat)>, i: nat, num_vars: nat) {
    if idx_pairs != enum_pairs(l) || i >= idx_pairs.len() {
    } else if check_simp_spec(l[idx_pairs[i as int].0 as int], l[idx_pairs[i as int].1 as int]) {
        enum_pairs_facts(l);
        let h = idx_pairs[i as int];
        assert(h.0 < h.1 && h.1 < l.len());
        let new_l = update_L(l, h, num_vars);
        update_L_len(l, h, num_vars);
        enum_pairs_facts(new_l);
        let n = l.len();
        let m = new_l.len();
        assert(m + 1 == n);
        assert(m * m * m + m * m < n * n * n) by (nonlinear_arith)
            requires m + 1 == n;
        assert(enum_pairs(new_l).len() <= m * m);
    } else {
    }
}

/// `WEST_simp L num_vars = WEST_simp_helper L (enum_pairs L) 0 num_vars`
pub open spec fn WEST_simp_spec(l: WestRegex, num_vars: nat) -> WestRegex {
    WEST_simp_helper_spec(l, enum_pairs(l), 0, num_vars)
}

/// `WEST_and_simp L1 L2 num_vars = WEST_simp (WEST_and L1 L2) num_vars`
pub open spec fn WEST_and_simp_spec(l1: WestRegex, l2: WestRegex, num_vars: nat) -> WestRegex {
    WEST_simp_spec(WEST_and_spec(l1, l2), num_vars)
}

/// `WEST_or_simp L1 L2 num_vars = WEST_simp (L1 @ L2) num_vars`
pub open spec fn WEST_or_simp_spec(l1: WestRegex, l2: WestRegex, num_vars: nat) -> WestRegex {
    WEST_simp_spec(l1 + l2, num_vars)
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// `arbitrary_state num_vars`: all `S`.
pub open spec fn arbitrary_state(num_vars: nat) -> StateRegex {
    Seq::new(num_vars, |k: int| WestBit::S)
}

/// `arbitrary_trace num_vars num_pad`: `num_pad` all-`S` states.
pub open spec fn arbitrary_trace(num_vars: nat, num_pad: nat) -> TraceRegex {
    Seq::new(num_pad, |k: int| arbitrary_state(num_vars))
}

/// `shift traceList num_vars num_pad`: prepend `num_pad` all-`S` states to
/// every trace regex (delay by `num_pad` steps).
pub open spec fn shift_spec(trace_list: WestRegex, num_vars: nat, num_pad: nat) -> WestRegex {
    trace_list.map_values(|trace: TraceRegex| arbitrary_trace(num_vars, num_pad) + trace)
}

/// `pad trace num_vars num_pad`: append `num_pad` all-`S` states.
pub open spec fn pad_spec(trace: TraceRegex, num_vars: nat, num_pad: nat) -> TraceRegex {
    trace + arbitrary_trace(num_vars, num_pad)
}

// ---------------------------------------------------------------------------
// WEST temporal operations
// ---------------------------------------------------------------------------

/// `WEST_global L a b num_vars`
pub open spec fn WEST_global_spec(l: WestRegex, a: nat, b: nat, num_vars: nat) -> WestRegex
    decreases b,
{
    if a == b {
        shift_spec(l, num_vars, a)
    } else if a < b {
        WEST_and_simp_spec(shift_spec(l, num_vars, b), WEST_global_spec(l, a, (b - 1) as nat, num_vars), num_vars)
    } else {
        Seq::empty()
    }
}

/// `WEST_future L a b num_vars`
pub open spec fn WEST_future_spec(l: WestRegex, a: nat, b: nat, num_vars: nat) -> WestRegex
    decreases b,
{
    if a == b {
        shift_spec(l, num_vars, a)
    } else if a < b {
        WEST_or_simp_spec(shift_spec(l, num_vars, b), WEST_future_spec(l, a, (b - 1) as nat, num_vars), num_vars)
    } else {
        Seq::empty()
    }
}

/// `WEST_until L_φ L_ψ a b num_vars`
pub open spec fn WEST_until_spec(l_phi: WestRegex, l_psi: WestRegex, a: nat, b: nat, num_vars: nat) -> WestRegex
    decreases b,
{
    if a == b {
        WEST_global_spec(l_psi, a, a, num_vars)
    } else if a < b {
        WEST_or_simp_spec(
            WEST_until_spec(l_phi, l_psi, a, (b - 1) as nat, num_vars),
            WEST_and_simp_spec(WEST_global_spec(l_phi, a, (b - 1) as nat, num_vars),
                WEST_global_spec(l_psi, b, b, num_vars), num_vars),
            num_vars)
    } else {
        Seq::empty()
    }
}

/// `WEST_release_helper L_φ L_ψ a ub num_vars`
pub open spec fn WEST_release_helper_spec(l_phi: WestRegex, l_psi: WestRegex, a: nat, ub: nat, num_vars: nat) -> WestRegex
    decreases ub,
{
    if a == ub {
        WEST_and_simp_spec(WEST_global_spec(l_phi, a, a, num_vars), WEST_global_spec(l_psi, a, a, num_vars), num_vars)
    } else if a < ub {
        WEST_or_simp_spec(
            WEST_release_helper_spec(l_phi, l_psi, a, (ub - 1) as nat, num_vars),
            WEST_and_simp_spec(WEST_global_spec(l_psi, a, ub, num_vars),
                WEST_global_spec(l_phi, ub, ub, num_vars), num_vars),
            num_vars)
    } else {
        Seq::empty()
    }
}

/// `WEST_release L_φ L_ψ a b num_vars`
pub open spec fn WEST_release_spec(l_phi: WestRegex, l_psi: WestRegex, a: nat, b: nat, num_vars: nat) -> WestRegex {
    if b > a {
        WEST_or_simp_spec(WEST_global_spec(l_psi, a, b, num_vars),
            WEST_release_helper_spec(l_phi, l_psi, a, (b - 1) as nat, num_vars), num_vars)
    } else {
        WEST_global_spec(l_psi, a, b, num_vars)
    }
}

// ---------------------------------------------------------------------------
// WEST recursive reg function
// ---------------------------------------------------------------------------

/// `WEST_termination_measure`. Isabelle lists 19 equations; they amount to
/// `1` on atoms, `1 + 3·m φ` on `Not φ` (`WEST_termination_measure_not`),
/// and `1 + m φ (+ m ψ)` on the other operators, which is how it is written
/// here.
pub open spec fn WEST_termination_measure(f: Mltl<usize>) -> nat
    decreases f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(phi) => 1 + 3 * WEST_termination_measure(*phi),
        Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => 1 + WEST_termination_measure(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
        | Mltl::Release(phi, _, _, psi) => 1 + WEST_termination_measure(*phi) + WEST_termination_measure(*psi),
    }
}

/// `WEST_reg_aux F num_vars`: the regex of `F`. Not-cases push the negation
/// one level down, as in Isabelle.
pub open spec fn WEST_reg_aux_spec(f: Mltl<usize>, num_vars: nat) -> WestRegex
    decreases WEST_termination_measure(f),
    via WEST_reg_aux_decreases
{
    match f {
        Mltl::True => seq![seq![Seq::new(num_vars, |j: int| WestBit::S)]],
        Mltl::False => Seq::empty(),
        Mltl::Prop(p) => seq![seq![Seq::new(num_vars, |j: int| if p as int == j { WestBit::One } else { WestBit::S })]],
        Mltl::Or(phi, psi) => WEST_or_simp_spec(WEST_reg_aux_spec(*phi, num_vars), WEST_reg_aux_spec(*psi, num_vars), num_vars),
        Mltl::And(phi, psi) => WEST_and_simp_spec(WEST_reg_aux_spec(*phi, num_vars), WEST_reg_aux_spec(*psi, num_vars), num_vars),
        Mltl::Future(a, b, phi) => WEST_future_spec(WEST_reg_aux_spec(*phi, num_vars), a as nat, b as nat, num_vars),
        Mltl::Global(a, b, phi) => WEST_global_spec(WEST_reg_aux_spec(*phi, num_vars), a as nat, b as nat, num_vars),
        Mltl::Until(phi, a, b, psi) => WEST_until_spec(WEST_reg_aux_spec(*phi, num_vars),
            WEST_reg_aux_spec(*psi, num_vars), a as nat, b as nat, num_vars),
        Mltl::Release(phi, a, b, psi) => WEST_release_spec(WEST_reg_aux_spec(*phi, num_vars),
            WEST_reg_aux_spec(*psi, num_vars), a as nat, b as nat, num_vars),
        Mltl::Not(g) => match *g {
            Mltl::Prop(p) => seq![seq![Seq::new(num_vars, |j: int| if p as int == j { WestBit::Zero } else { WestBit::S })]],
            Mltl::True => WEST_reg_aux_spec(Mltl::False, num_vars),
            Mltl::False => WEST_reg_aux_spec(Mltl::True, num_vars),
            Mltl::And(phi, psi) => WEST_reg_aux_spec(
                Mltl::Or(Box::new(Mltl::Not(phi)), Box::new(Mltl::Not(psi))), num_vars),
            Mltl::Or(phi, psi) => WEST_reg_aux_spec(
                Mltl::And(Box::new(Mltl::Not(phi)), Box::new(Mltl::Not(psi))), num_vars),
            Mltl::Future(a, b, phi) => WEST_reg_aux_spec(Mltl::Global(a, b, Box::new(Mltl::Not(phi))), num_vars),
            Mltl::Global(a, b, phi) => WEST_reg_aux_spec(Mltl::Future(a, b, Box::new(Mltl::Not(phi))), num_vars),
            Mltl::Until(phi, a, b, psi) => WEST_reg_aux_spec(
                Mltl::Release(Box::new(Mltl::Not(phi)), a, b, Box::new(Mltl::Not(psi))), num_vars),
            Mltl::Release(phi, a, b, psi) => WEST_reg_aux_spec(
                Mltl::Until(Box::new(Mltl::Not(phi)), a, b, Box::new(Mltl::Not(psi))), num_vars),
            Mltl::Not(phi) => WEST_reg_aux_spec(*phi, num_vars),
        },
    }
}

#[via_fn]
proof fn WEST_reg_aux_decreases(f: Mltl<usize>, num_vars: nat) {
    reveal_with_fuel(WEST_termination_measure, 3);
}

/// `WEST_num_vars F`: one more than the largest atom (1 without atoms).
pub open spec fn WEST_num_vars_spec(f: Mltl<usize>) -> nat
    decreases f,
{
    match f {
        Mltl::True | Mltl::False => 1,
        Mltl::Prop(p) => p as nat + 1,
        Mltl::Not(phi) | Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => WEST_num_vars_spec(*phi),
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi) | Mltl::Release(phi, _, _, psi) =>
            max_nat(WEST_num_vars_spec(*phi), WEST_num_vars_spec(*psi)),
    }
}

/// `WEST_reg F = WEST_reg_aux (convert_nnf F) (WEST_num_vars F)`
pub open spec fn WEST_reg_spec(f: Mltl<usize>) -> WestRegex {
    WEST_reg_aux_spec(convert_nnf_spec(f), WEST_num_vars_spec(f))
}

/// `pad_WEST_reg φ`: every trace regex padded to `complen_mltl φ`.
pub open spec fn pad_WEST_reg_spec(phi: Mltl<usize>) -> WestRegex {
    let unpadded = WEST_reg_spec(phi);
    let complen = complen_mltl(phi);
    let num_vars = WEST_num_vars_spec(phi);
    unpadded.map_values(|l: TraceRegex|
        if l.len() < complen { pad_spec(l, num_vars, (complen - l.len()) as nat) } else { l })
}

/// `simp_pad_WEST_reg φ = WEST_simp (pad_WEST_reg φ) (WEST_num_vars φ)`
pub open spec fn simp_pad_WEST_reg_spec(phi: Mltl<usize>) -> WestRegex {
    WEST_simp_spec(pad_WEST_reg_spec(phi), WEST_num_vars_spec(phi))
}

} // verus!
