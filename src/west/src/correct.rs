//! Top-level correctness of WEST.
//!
//! Mirrors `WEST_Proofs.thy`, sections "WEST_reg_aux", "Top level result"
//! and "Top level result for padded version": `WEST_reg_aux_correct`,
//! `WEST_correct`, `WEST_correct_v2`, `WEST_correct_pad`, with the NNF facts
//! they use (`WEST_num_vars_nnf`, `complen_convert_nnf`, `nnf_int_welldef`).
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithms::*;
use crate::matching::*;
use crate::simp::*;
use crate::temporal::*;

verus! {

// ---------------------------------------------------------------------------
// convert_nnf keeps intervals, num_vars and complen
// ---------------------------------------------------------------------------

/// `intervals_welldef φ ⟹ intervals_welldef (convert_nnf φ)` (Isabelle:
/// `nnf_int_welldef`).
pub proof fn convert_nnf_welldef(f: Mltl<usize>)
    requires
        intervals_welldef(f),
    ensures
        intervals_welldef(convert_nnf_spec(f)),
    decreases depth_mltl(f),
{
    reveal_with_fuel(depth_mltl, 2);
    reveal_with_fuel(intervals_welldef, 3);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => match *g {
            Mltl::True | Mltl::False | Mltl::Prop(_) => {},
            Mltl::Not(phi) => convert_nnf_welldef(*phi),
            Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
            | Mltl::Release(phi, _, _, psi) => {
                convert_nnf_welldef(Mltl::Not(phi));
                convert_nnf_welldef(Mltl::Not(psi));
            },
            Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
                convert_nnf_welldef(Mltl::Not(phi));
            },
        },
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
        | Mltl::Release(phi, _, _, psi) => {
            convert_nnf_welldef(*phi);
            convert_nnf_welldef(*psi);
        },
        Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
            convert_nnf_welldef(*phi);
        },
    }
}

/// `WEST_num_vars φ = WEST_num_vars (convert_nnf φ)` and
/// `complen_mltl (convert_nnf φ) = complen_mltl φ` (Isabelle:
/// `WEST_num_vars_nnf`, `complen_convert_nnf`).
pub proof fn convert_nnf_num_vars_complen(f: Mltl<usize>)
    ensures
        WEST_num_vars_spec(convert_nnf_spec(f)) == WEST_num_vars_spec(f),
        complen_mltl(convert_nnf_spec(f)) == complen_mltl(f),
    decreases depth_mltl(f),
{
    reveal_with_fuel(depth_mltl, 2);
    reveal_with_fuel(complen_mltl, 3);
    reveal_with_fuel(WEST_num_vars_spec, 3);
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => match *g {
            Mltl::True | Mltl::False | Mltl::Prop(_) => {},
            Mltl::Not(phi) => convert_nnf_num_vars_complen(*phi),
            Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
            | Mltl::Release(phi, _, _, psi) => {
                convert_nnf_num_vars_complen(Mltl::Not(phi));
                convert_nnf_num_vars_complen(Mltl::Not(psi));
            },
            Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
                convert_nnf_num_vars_complen(Mltl::Not(phi));
            },
        },
        Mltl::And(phi, psi) | Mltl::Or(phi, psi) | Mltl::Until(phi, _, _, psi)
        | Mltl::Release(phi, _, _, psi) => {
            convert_nnf_num_vars_complen(*phi);
            convert_nnf_num_vars_complen(*psi);
        },
        Mltl::Future(_, _, phi) | Mltl::Global(_, _, phi) => {
            convert_nnf_num_vars_complen(*phi);
        },
    }
}

// ---------------------------------------------------------------------------
// WEST_reg_aux
// ---------------------------------------------------------------------------

/// Not in Isabelle as a separate lemma: `WEST_reg_aux` of an NNF formula
/// has `num_vars`-wide states (Isabelle: `WEST_reg_aux_num_vars`).
pub proof fn WEST_reg_aux_of_vars(f: Mltl<usize>, n: nat)
    requires
        is_nnf(f),
    ensures
        WEST_regex_of_vars(WEST_reg_aux_spec(f, n), n),
    decreases f,
{
    let pi = Seq::<Set<usize>>::empty();
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => {},
        Mltl::Not(g) => {
            assert(*g is Prop);
        },
        Mltl::Or(phi, psi) => {
            WEST_reg_aux_of_vars(*phi, n);
            WEST_reg_aux_of_vars(*psi, n);
            WEST_or_simp_correct(pi, WEST_reg_aux_spec(*phi, n), WEST_reg_aux_spec(*psi, n), n);
        },
        Mltl::And(phi, psi) => {
            WEST_reg_aux_of_vars(*phi, n);
            WEST_reg_aux_of_vars(*psi, n);
            WEST_and_simp_correct(pi, WEST_reg_aux_spec(*phi, n), WEST_reg_aux_spec(*psi, n), n);
        },
        Mltl::Future(a, b, phi) => {
            WEST_reg_aux_of_vars(*phi, n);
            if a <= b {
                WEST_future_correct(pi, WEST_reg_aux_spec(*phi, n), a as nat, b as nat, n);
            }
        },
        Mltl::Global(a, b, phi) => {
            WEST_reg_aux_of_vars(*phi, n);
            if a <= b {
                WEST_global_correct(pi, WEST_reg_aux_spec(*phi, n), a as nat, b as nat, n);
            }
        },
        Mltl::Until(phi, a, b, psi) => {
            WEST_reg_aux_of_vars(*phi, n);
            WEST_reg_aux_of_vars(*psi, n);
            if a <= b {
                WEST_until_correct(pi, WEST_reg_aux_spec(*phi, n), WEST_reg_aux_spec(*psi, n), a as nat, b as nat, n);
            }
        },
        Mltl::Release(phi, a, b, psi) => {
            WEST_reg_aux_of_vars(*phi, n);
            WEST_reg_aux_of_vars(*psi, n);
            if a <= b {
                WEST_release_correct(pi, WEST_reg_aux_spec(*phi, n), WEST_reg_aux_spec(*psi, n), a as nat, b as nat, n);
            }
        },
    }
}

/// Base cases: a single one-state regex with entry `bit` at `p`.
proof fn single_state_match(pi: WestTrace, n: nat, p: usize, bit: WestBit)
    requires
        p < n,
        pi.len() >= 1,
    ensures
        west_match(pi, seq![seq![Seq::new(n, |j: int| if p as int == j { bit } else { WestBit::S })]])
            <==> bit_ok(bit, pi[0].contains(p)),
{
    let s = Seq::new(n, |j: int| if p as int == j { bit } else { WestBit::S });
    let t = seq![s];
    west_match_single(pi, t);
    match_timestep_iff(pi[0], s);
    assert(s[p as int] == bit);
    if bit_ok(bit, pi[0].contains(p)) {
        assert(match_timestep(pi[0], t[0]));
    }
    if match_regex(pi, t) {
        assert(match_timestep(pi[0], t[0]));
        assert(bit_ok(s[p as int], atom_in(pi[0], p as int)));
    }
}

/// The F case on any regex list `l` whose shifts mean `φ` (shared with the
/// fast version).
pub proof fn future_sem(pi: WestTrace, l: WestRegex, phi: Mltl<usize>, a: usize, b: usize)
    requires
        a <= b,
        pi.len() > b,
        forall|i: nat| a <= i <= b ==> (#[trigger] shifted(pi, l, i) <==> semantics_mltl(drop(pi, i), phi)),
    ensures
        some_shifted(pi, l, a as nat, b as nat) <==> semantics_mltl(pi, Mltl::Future(a, b, Box::new(phi))),
{
    if semantics_mltl(pi, Mltl::Future(a, b, Box::new(phi))) {
        let i = choose|i: nat| (a <= i && i <= b) && semantics_mltl(drop(pi, i), phi);
        assert(shifted(pi, l, i));
    }
}

proof fn future_case(pi: WestTrace, l: WestRegex, phi: Mltl<usize>, a: usize, b: usize, n: nat)
    requires
        WEST_regex_of_vars(l, n),
        a <= b,
        pi.len() > b,
        forall|i: nat| a <= i <= b ==> (#[trigger] shifted(pi, l, i) <==> semantics_mltl(drop(pi, i), phi)),
    ensures
        west_match(pi, WEST_future_spec(l, a as nat, b as nat, n)) <==> semantics_mltl(pi, Mltl::Future(a, b, Box::new(phi))),
{
    WEST_future_correct(pi, l, a as nat, b as nat, n);
    future_sem(pi, l, phi, a, b);
}

/// The G case on any regex list `l` whose shifts mean `φ`.
pub proof fn global_sem(pi: WestTrace, l: WestRegex, phi: Mltl<usize>, a: usize, b: usize)
    requires
        a <= b,
        pi.len() > b,
        forall|i: nat| a <= i <= b ==> (#[trigger] shifted(pi, l, i) <==> semantics_mltl(drop(pi, i), phi)),
    ensures
        all_shifted(pi, l, a as nat, b as nat) <==> semantics_mltl(pi, Mltl::Global(a, b, Box::new(phi))),
{
    if all_shifted(pi, l, a as nat, b as nat) {
        assert forall|i: nat| a <= i <= b implies semantics_mltl(#[trigger] drop(pi, i), phi) by {
            assert(shifted(pi, l, i));
        }
    }
    if semantics_mltl(pi, Mltl::Global(a, b, Box::new(phi))) {
        assert forall|i: nat| a <= i <= b implies #[trigger] shifted(pi, l, i) by {
            assert(semantics_mltl(drop(pi, i), phi));
        }
    }
}

proof fn global_case(pi: WestTrace, l: WestRegex, phi: Mltl<usize>, a: usize, b: usize, n: nat)
    requires
        WEST_regex_of_vars(l, n),
        a <= b,
        pi.len() > b,
        forall|i: nat| a <= i <= b ==> (#[trigger] shifted(pi, l, i) <==> semantics_mltl(drop(pi, i), phi)),
    ensures
        west_match(pi, WEST_global_spec(l, a as nat, b as nat, n)) <==> semantics_mltl(pi, Mltl::Global(a, b, Box::new(phi))),
{
    WEST_global_correct(pi, l, a as nat, b as nat, n);
    global_sem(pi, l, phi, a, b);
}

/// The U case on any regex lists whose shifts mean `φ` and `ψ`.
pub proof fn until_sem(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, phi: Mltl<usize>, psi: Mltl<usize>,
    a: usize, b: usize)
    requires
        a <= b,
        pi.len() > b,
        forall|i: nat| a <= i <= b ==> (#[trigger] shifted(pi, l_psi, i) <==> semantics_mltl(drop(pi, i), psi)),
        forall|j: nat| a <= j < b ==> (#[trigger] shifted(pi, l_phi, j) <==> semantics_mltl(drop(pi, j), phi)),
    ensures
        until_shifted(pi, l_phi, l_psi, a as nat, b as nat)
            <==> semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi))),
{
    if until_shifted(pi, l_phi, l_psi, a as nat, b as nat) {
        let i = choose|i: nat| a <= i <= b
            && #[trigger] shifted(pi, l_psi, i) && forall|j: nat| a <= j < i ==> #[trigger] shifted(pi, l_phi, j);
        assert(semantics_mltl(drop(pi, i), psi));
        assert forall|j: nat| j >= a && j < i implies semantics_mltl(#[trigger] drop(pi, j), phi) by {
            assert(shifted(pi, l_phi, j));
        }
    }
    if semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi))) {
        let i = choose|i: nat| (a <= i && i <= b) && (semantics_mltl(drop(pi, i), psi)
            && forall|j: nat| (j >= a && j < i) ==> semantics_mltl(#[trigger] drop(pi, j), phi));
        assert(shifted(pi, l_psi, i));
        assert forall|j: nat| a <= j < i implies #[trigger] shifted(pi, l_phi, j) by {
            assert(semantics_mltl(drop(pi, j), phi));
        }
    }
}

proof fn until_case(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, phi: Mltl<usize>, psi: Mltl<usize>,
    a: usize, b: usize, n: nat)
    requires
        WEST_regex_of_vars(l_phi, n),
        WEST_regex_of_vars(l_psi, n),
        a <= b,
        pi.len() > b,
        forall|i: nat| a <= i <= b ==> (#[trigger] shifted(pi, l_psi, i) <==> semantics_mltl(drop(pi, i), psi)),
        forall|j: nat| a <= j < b ==> (#[trigger] shifted(pi, l_phi, j) <==> semantics_mltl(drop(pi, j), phi)),
    ensures
        west_match(pi, WEST_until_spec(l_phi, l_psi, a as nat, b as nat, n))
            <==> semantics_mltl(pi, Mltl::Until(Box::new(phi), a, b, Box::new(psi))),
{
    WEST_until_correct(pi, l_phi, l_psi, a as nat, b as nat, n);
    until_sem(pi, l_phi, l_psi, phi, psi, a, b);
}

/// The R case on any regex lists whose shifts mean `φ` and `ψ`.
pub proof fn release_sem(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, phi: Mltl<usize>, psi: Mltl<usize>,
    a: usize, b: usize)
    requires
        a <= b,
        pi.len() > b,
        forall|i: nat| a <= i <= b ==> (#[trigger] shifted(pi, l_psi, i) <==> semantics_mltl(drop(pi, i), psi)),
        forall|j: nat| a <= j < b ==> (#[trigger] shifted(pi, l_phi, j) <==> semantics_mltl(drop(pi, j), phi)),
    ensures
        release_shifted(pi, l_phi, l_psi, a as nat, b as nat)
            <==> semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))),
{
    let all_psi = all_shifted(pi, l_psi, a as nat, b as nat);
    let sem_all_psi = forall|i: nat| (a <= i && i <= b) ==> semantics_mltl(#[trigger] drop(pi, i), psi);
    assert(all_psi <==> sem_all_psi) by {
        if all_psi {
            assert forall|i: nat| (a <= i && i <= b) implies semantics_mltl(#[trigger] drop(pi, i), psi) by {
                assert(shifted(pi, l_psi, i));
            }
        }
        if sem_all_psi {
            assert forall|i: nat| a <= i <= b implies #[trigger] shifted(pi, l_psi, i) by {
                assert(semantics_mltl(drop(pi, i), psi));
            }
        }
    }
    let sem = semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi)));
    if release_shifted(pi, l_phi, l_psi, a as nat, b as nat) && !all_psi {
        let j = choose|j: nat| a <= j <= (b - 1) as nat
            && #[trigger] shifted(pi, l_phi, j) && forall|k: nat| a <= k <= j ==> #[trigger] shifted(pi, l_psi, k);
        assert(semantics_mltl(drop(pi, j), phi));
        assert forall|k: nat| (a <= k && k <= j) implies semantics_mltl(#[trigger] drop(pi, k), psi) by {
            assert(shifted(pi, l_psi, k));
        }
        assert(sem);
    }
    if sem && !sem_all_psi {
        let j = choose|j: nat| (j >= a && j <= nat_sub(b as nat, 1)) && semantics_mltl(drop(pi, j), phi)
            && forall|k: nat| (a <= k && k <= j) ==> semantics_mltl(#[trigger] drop(pi, k), psi);
        if a == b {
            // j = a = b = 0: then ψ holds on all of [a, b].
            assert forall|i: nat| (a <= i && i <= b) implies semantics_mltl(#[trigger] drop(pi, i), psi) by {
                assert(i == j);
            }
        } else {
            assert(shifted(pi, l_phi, j));
            assert forall|k: nat| a <= k <= j implies #[trigger] shifted(pi, l_psi, k) by {
                assert(semantics_mltl(drop(pi, k), psi));
            }
            assert(release_helper_shifted(pi, l_phi, l_psi, a as nat, (b - 1) as nat));
        }
    }
}

proof fn release_case(pi: WestTrace, l_phi: WestRegex, l_psi: WestRegex, phi: Mltl<usize>, psi: Mltl<usize>,
    a: usize, b: usize, n: nat)
    requires
        WEST_regex_of_vars(l_phi, n),
        WEST_regex_of_vars(l_psi, n),
        a <= b,
        pi.len() > b,
        forall|i: nat| a <= i <= b ==> (#[trigger] shifted(pi, l_psi, i) <==> semantics_mltl(drop(pi, i), psi)),
        forall|j: nat| a <= j < b ==> (#[trigger] shifted(pi, l_phi, j) <==> semantics_mltl(drop(pi, j), phi)),
    ensures
        west_match(pi, WEST_release_spec(l_phi, l_psi, a as nat, b as nat, n))
            <==> semantics_mltl(pi, Mltl::Release(Box::new(phi), a, b, Box::new(psi))),
{
    WEST_release_correct(pi, l_phi, l_psi, a as nat, b as nat, n);
    release_sem(pi, l_phi, l_psi, phi, psi, a, b);
}

/// `length π ≥ complen_mltl F ⟹ F` in NNF `⟹ WEST_num_vars F ≤ num_vars ⟹
/// intervals_welldef F ⟹ (match π (WEST_reg_aux F num_vars) ⟷ π ⊨ F)`
/// (Isabelle: `WEST_reg_aux_correct`; NNF stated as `is_nnf` instead of
/// `∃ψ. F = convert_nnf ψ`).
pub proof fn WEST_reg_aux_correct(pi: WestTrace, f: Mltl<usize>, n: nat)
    requires
        pi.len() >= complen_mltl(f),
        is_nnf(f),
        WEST_num_vars_spec(f) <= n,
        intervals_welldef(f),
    ensures
        west_match(pi, WEST_reg_aux_spec(f, n)) <==> semantics_mltl(pi, f),
    decreases f,
{
    complen_geq_one(f);
    match f {
        Mltl::True => {
            let t = seq![Seq::new(n, |j: int| WestBit::S)];
            west_match_single(pi, t);
            assert(match_timestep(pi[0], t[0]));
        },
        Mltl::False => {},
        Mltl::Prop(p) => {
            single_state_match(pi, n, p, WestBit::One);
        },
        Mltl::Not(g) => {
            assert(*g is Prop);
            let p = g->Prop_0;
            assert(*g == Mltl::<usize>::Prop(p));
            reveal_with_fuel(WEST_num_vars_spec, 2);
            reveal_with_fuel(semantics_mltl, 2);
            single_state_match(pi, n, p, WestBit::Zero);
            assert(WEST_reg_aux_spec(f, n)
                == seq![seq![Seq::new(n, |j: int| if p as int == j { WestBit::Zero } else { WestBit::S })]]);
        },
        Mltl::Or(phi, psi) => {
            WEST_reg_aux_correct(pi, *phi, n);
            WEST_reg_aux_correct(pi, *psi, n);
            WEST_reg_aux_of_vars(*phi, n);
            WEST_reg_aux_of_vars(*psi, n);
            WEST_or_simp_correct(pi, WEST_reg_aux_spec(*phi, n), WEST_reg_aux_spec(*psi, n), n);
        },
        Mltl::And(phi, psi) => {
            WEST_reg_aux_correct(pi, *phi, n);
            WEST_reg_aux_correct(pi, *psi, n);
            WEST_reg_aux_of_vars(*phi, n);
            WEST_reg_aux_of_vars(*psi, n);
            WEST_and_simp_correct(pi, WEST_reg_aux_spec(*phi, n), WEST_reg_aux_spec(*psi, n), n);
        },
        Mltl::Future(a, b, phi) => {
            let l = WEST_reg_aux_spec(*phi, n);
            WEST_reg_aux_of_vars(*phi, n);
            complen_geq_one(*phi);
            assert forall|i: nat| a <= i <= b implies (#[trigger] shifted(pi, l, i) <==> semantics_mltl(drop(pi, i), *phi)) by {
                WEST_reg_aux_correct(drop(pi, i), *phi, n);
            }
            future_case(pi, l, *phi, a, b, n);
        },
        Mltl::Global(a, b, phi) => {
            let l = WEST_reg_aux_spec(*phi, n);
            WEST_reg_aux_of_vars(*phi, n);
            complen_geq_one(*phi);
            assert forall|i: nat| a <= i <= b implies (#[trigger] shifted(pi, l, i) <==> semantics_mltl(drop(pi, i), *phi)) by {
                WEST_reg_aux_correct(drop(pi, i), *phi, n);
            }
            global_case(pi, l, *phi, a, b, n);
        },
        Mltl::Until(phi, a, b, psi) => {
            let lp = WEST_reg_aux_spec(*phi, n);
            let lq = WEST_reg_aux_spec(*psi, n);
            WEST_reg_aux_of_vars(*phi, n);
            WEST_reg_aux_of_vars(*psi, n);
            complen_geq_one(*psi);
            assert forall|i: nat| a <= i <= b implies (#[trigger] shifted(pi, lq, i) <==> semantics_mltl(drop(pi, i), *psi)) by {
                WEST_reg_aux_correct(drop(pi, i), *psi, n);
            }
            assert forall|j: nat| a <= j < b implies (#[trigger] shifted(pi, lp, j) <==> semantics_mltl(drop(pi, j), *phi)) by {
                WEST_reg_aux_correct(drop(pi, j), *phi, n);
            }
            until_case(pi, lp, lq, *phi, *psi, a, b, n);
        },
        Mltl::Release(phi, a, b, psi) => {
            let lp = WEST_reg_aux_spec(*phi, n);
            let lq = WEST_reg_aux_spec(*psi, n);
            WEST_reg_aux_of_vars(*phi, n);
            WEST_reg_aux_of_vars(*psi, n);
            complen_geq_one(*psi);
            assert forall|i: nat| a <= i <= b implies (#[trigger] shifted(pi, lq, i) <==> semantics_mltl(drop(pi, i), *psi)) by {
                WEST_reg_aux_correct(drop(pi, i), *psi, n);
            }
            assert forall|j: nat| a <= j < b implies (#[trigger] shifted(pi, lp, j) <==> semantics_mltl(drop(pi, j), *phi)) by {
                WEST_reg_aux_correct(drop(pi, j), *phi, n);
            }
            release_case(pi, lp, lq, *phi, *psi, a, b, n);
        },
    }
}

// ---------------------------------------------------------------------------
// Top-level results
// ---------------------------------------------------------------------------

/// `WEST_reg` produces `WEST_num_vars`-wide states.
pub proof fn WEST_reg_of_vars(f: Mltl<usize>)
    ensures
        WEST_regex_of_vars(WEST_reg_spec(f), WEST_num_vars_spec(f)),
{
    convert_nnf_is_nnf(f);
    WEST_reg_aux_of_vars(convert_nnf_spec(f), WEST_num_vars_spec(f));
}

/// `intervals_welldef φ ⟹ complen_mltl (convert_nnf φ) ≤ length π ⟹
/// (match π (WEST_reg φ) ⟷ π ⊨ φ)` (Isabelle: `WEST_correct`).
pub proof fn WEST_correct(pi: WestTrace, f: Mltl<usize>)
    requires
        intervals_welldef(f),
        pi.len() >= complen_mltl(convert_nnf_spec(f)),
    ensures
        west_match(pi, WEST_reg_spec(f)) <==> semantics_mltl(pi, f),
{
    let g = convert_nnf_spec(f);
    convert_nnf_is_nnf(f);
    convert_nnf_welldef(f);
    convert_nnf_num_vars_complen(f);
    convert_nnf_preserves_semantics(pi, f);
    WEST_reg_aux_correct(pi, g, WEST_num_vars_spec(f));
}

/// The same with `complen_mltl φ` (Isabelle: `WEST_correct_v2`).
pub proof fn WEST_correct_v2(pi: WestTrace, f: Mltl<usize>)
    requires
        intervals_welldef(f),
        pi.len() >= complen_mltl(f),
    ensures
        west_match(pi, WEST_reg_spec(f)) <==> semantics_mltl(pi, f),
{
    convert_nnf_num_vars_complen(f);
    WEST_correct(pi, f);
}

/// `pad_WEST_reg` keeps `WEST_num_vars`-wide states.
pub proof fn pad_WEST_reg_of_vars(f: Mltl<usize>)
    ensures
        WEST_regex_of_vars(pad_WEST_reg_spec(f), WEST_num_vars_spec(f)),
{
    let unpadded = WEST_reg_spec(f);
    let padded = pad_WEST_reg_spec(f);
    let c = complen_mltl(f);
    let n = WEST_num_vars_spec(f);
    WEST_reg_of_vars(f);
    assert forall|k: int| 0 <= k < padded.len() implies trace_regex_of_vars(#[trigger] padded[k], n) by {
        assert(trace_regex_of_vars(unpadded[k], n));
        if unpadded[k].len() < c {
            pad_match(Seq::empty(), unpadded[k], n, (c - unpadded[k].len()) as nat);
        }
    }
}

/// `pad_WEST_reg` matches the same traces as `WEST_reg` on traces of length
/// at least `complen_mltl φ`, and keeps `num_vars`.
pub proof fn pad_WEST_reg_correct(pi: WestTrace, f: Mltl<usize>)
    requires
        pi.len() >= complen_mltl(f),
    ensures
        west_match(pi, pad_WEST_reg_spec(f)) <==> west_match(pi, WEST_reg_spec(f)),
        WEST_regex_of_vars(pad_WEST_reg_spec(f), WEST_num_vars_spec(f)),
{
    let unpadded = WEST_reg_spec(f);
    let padded = pad_WEST_reg_spec(f);
    let c = complen_mltl(f);
    let n = WEST_num_vars_spec(f);
    WEST_reg_of_vars(f);
    assert forall|k: int| 0 <= k < padded.len() implies
        (match_regex(pi, #[trigger] padded[k]) <==> match_regex(pi, unpadded[k])) && trace_regex_of_vars(padded[k], n) by {
        assert(trace_regex_of_vars(unpadded[k], n));
        if unpadded[k].len() < c {
            pad_match(pi, unpadded[k], n, (c - unpadded[k].len()) as nat);
        }
    }
    if west_match(pi, padded) {
        let k = choose|k: int| 0 <= k < padded.len() && #[trigger] match_regex(pi, padded[k]);
        assert(match_regex(pi, unpadded[k]));
    }
    if west_match(pi, unpadded) {
        let k = choose|k: int| 0 <= k < unpadded.len() && #[trigger] match_regex(pi, unpadded[k]);
        assert(match_regex(pi, padded[k]));
    }
}

/// `intervals_welldef φ ⟹ complen_mltl φ ≤ length π ⟹
/// (match π (simp_pad_WEST_reg φ) ⟷ π ⊨ φ)` (Isabelle: `WEST_correct_pad`).
pub proof fn WEST_correct_pad(pi: WestTrace, f: Mltl<usize>)
    requires
        intervals_welldef(f),
        pi.len() >= complen_mltl(f),
    ensures
        west_match(pi, simp_pad_WEST_reg_spec(f)) <==> semantics_mltl(pi, f),
{
    pad_WEST_reg_correct(pi, f);
    simp_correct(pi, pad_WEST_reg_spec(f), WEST_num_vars_spec(f));
    WEST_correct_v2(pi, f);
}

} // verus!
