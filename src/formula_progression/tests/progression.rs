//! Runtime checks of the verified formula progression (complements the
//! proofs: catches build/erasure surprises and documents expected values).
use formula_progression::algorithm::{formula_progression, formula_progression_len1};
use formula_progression::extended::prog;
use mltl_core::mltl::Mltl;
use mltl_eval::mltl_eval;
use std::collections::HashSet;

fn p(i: usize) -> Mltl<usize> { Mltl::Prop(i) }
fn bx(f: Mltl<usize>) -> Box<Mltl<usize>> { Box::new(f) }
fn tr(steps: &[&[usize]]) -> Vec<HashSet<usize>> {
    steps.iter().map(|s| s.iter().copied().collect()).collect()
}

/// Truth value of a formula that progression has made atom-free (it is the
/// same on every trace, so evaluate it on the empty one).
fn value(f: &Mltl<usize>) -> bool { mltl_eval(f, &[]) }

/// Unverified test helper: `complen_mltl`.
fn complen(f: &Mltl<usize>) -> usize {
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(g) => complen(g),
        Mltl::And(g, h) | Mltl::Or(g, h) => complen(g).max(complen(h)),
        Mltl::Future(_, b, g) | Mltl::Global(_, b, g) => b + complen(g),
        Mltl::Until(g, _, b, h) | Mltl::Release(g, _, b, h) => b + (complen(g).saturating_sub(1)).max(complen(h)),
    }
}

/// The examples of AFP `MLTL_Formula_Progression.thy`, subsection Examples.
#[test]
fn afp_examples() {
    let g2 = Mltl::Global(0, 2, bx(p(0)));
    let g1 = Mltl::Global(0, 1, bx(p(0)));
    let g0 = Mltl::Global(0, 0, bx(p(0)));
    // "simplifies to False_mltl"
    assert!(!value(&formula_progression(&g2, &tr(&[&[0], &[0], &[1]]))));
    // the one-step progression of G[0,2] p0 over {0} behaves like G[0,1] p0
    let one = formula_progression_len1(&g2, &tr(&[&[0]])[0]);
    for t in [tr(&[&[0], &[1]]), tr(&[&[0], &[0]]), tr(&[&[1]]), tr(&[])] {
        assert_eq!(mltl_eval(&one, &t), mltl_eval(&g1, &t));
    }
    // "Still false"
    assert!(!value(&formula_progression(&g1, &tr(&[&[0], &[1]]))));
    assert!(!value(&formula_progression(&g0, &tr(&[&[1]]))));
    // the one-step progression of G[0,1] p0 over {0} behaves like G[0,0] p0
    let one = formula_progression_len1(&g1, &tr(&[&[0]])[0]);
    for t in [tr(&[&[0]]), tr(&[&[1]]), tr(&[])] {
        assert_eq!(mltl_eval(&one, &t), mltl_eval(&g0, &t));
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> usize { (self.next() % n) as usize }
}

/// Random formula with well-defined intervals (the theorems assume them).
fn random_formula(r: &mut Rng, depth: usize) -> Mltl<usize> {
    if depth == 0 || r.below(4) == 0 {
        return match r.below(5) { 0 => Mltl::True, 1 => Mltl::False, _ => p(r.below(3)) };
    }
    let a = r.below(3);
    let b = a + r.below(3);
    let sub = |r: &mut Rng| bx(random_formula(r, depth - 1));
    match r.below(7) {
        0 => Mltl::Not(sub(r)),
        1 => Mltl::And(sub(r), sub(r)),
        2 => Mltl::Or(sub(r), sub(r)),
        3 => Mltl::Future(a, b, sub(r)),
        4 => Mltl::Global(a, b, sub(r)),
        5 => Mltl::Until(sub(r), a, b, sub(r)),
        _ => Mltl::Release(sub(r), a, b, sub(r)),
    }
}

/// Theorem 2 (`satisfiability_preservation`) and Theorem 3
/// (`formula_progression_correctness`), checked against the evaluator.
#[test]
fn theorems_hold_on_random_inputs() {
    let mut r = Rng(0x9E3779B97F4A7C15);
    let mut long_enough = 0;
    for _ in 0..5_000 {
        let f = random_formula(&mut r, 3);
        let len = r.below(10);
        let t: Vec<HashSet<usize>> =
            (0..len).map(|_| (0..3).filter(|_| r.below(2) == 0).collect()).collect();
        let expected = mltl_eval(&f, &t);
        for k in 1..len {
            let g = formula_progression(&f, &t[..k]);
            assert_eq!(mltl_eval(&g, &t[k..]), expected);
        }
        if len >= complen(&f) {
            long_enough += 1;
            assert_eq!(value(&formula_progression(&f, &t)), expected);
        }
    }
    assert!(long_enough > 1_000);
}

fn size(f: &Mltl<usize>) -> usize {
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => 1 + size(g),
        Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) => 1 + size(g) + size(h),
    }
}

/// The `prog` examples of `Formula_Progression_Extended.thy`: the result
/// keeps the original shape (`G[0,3] p` becomes `G[0,2] p`, ...) and is
/// decided as soon as the trace decides it.
#[test]
fn extended_examples() {
    let g3 = Mltl::Global(0, 3, bx(p(0)));
    let f3 = Mltl::Future(0, 3, bx(p(0)));
    let shape = |f: &Mltl<usize>| match f {
        Mltl::Global(a, b, g) => format!("G[{a},{b}]{}", matches!(**g, Mltl::Prop(0))),
        Mltl::Future(a, b, g) => format!("F[{a},{b}]{}", matches!(**g, Mltl::Prop(0))),
        Mltl::True => "T".into(),
        Mltl::False => "F".into(),
        _ => "?".into(),
    };
    assert_eq!(shape(&prog(&g3, &tr(&[&[0]]))), "G[0,2]true");
    assert_eq!(shape(&prog(&g3, &tr(&[&[0], &[0]]))), "G[0,1]true");
    assert_eq!(shape(&prog(&g3, &tr(&[&[0], &[0], &[0]]))), "G[0,0]true");
    assert_eq!(shape(&prog(&g3, &tr(&[&[0], &[0], &[0], &[0]]))), "T");
    assert_eq!(shape(&prog(&f3, &tr(&[&[]]))), "F[0,2]true");
    assert_eq!(shape(&prog(&f3, &tr(&[&[], &[]]))), "F[0,1]true");
    assert_eq!(shape(&prog(&f3, &tr(&[&[], &[], &[]]))), "F[0,0]true");
    assert_eq!(shape(&prog(&f3, &tr(&[&[], &[], &[], &[0]]))), "T");
    // early exit: a violation decides G at once
    assert_eq!(shape(&prog(&g3, &tr(&[&[1], &[0]]))), "F");
}

/// `prog_early_eval` and agreement with plain progression on non-empty
/// continuations, checked against the evaluator; also that the simplified
/// output is never larger than the plain one.
#[test]
fn prog_agrees_on_random_inputs() {
    let mut r = Rng(0xD1B54A32D192ED03);
    let (mut decided, mut plain_total, mut prog_total) = (0, 0, 0);
    for _ in 0..5_000 {
        let f = random_formula(&mut r, 3);
        let steps = |r: &mut Rng, n: usize| -> Vec<HashSet<usize>> {
            (0..n).map(|_| (0..3).filter(|_| r.below(2) == 0).collect()).collect()
        };
        let (n, m) = (r.below(8), 1 + r.below(6));
        let t = steps(&mut r, n);
        let rho = steps(&mut r, m);
        let g = prog(&f, &t);
        let whole: Vec<HashSet<usize>> = t.iter().chain(rho.iter()).cloned().collect();
        assert_eq!(mltl_eval(&g, &rho), mltl_eval(&f, &whole));
        match g {
            Mltl::True => { decided += 1; assert!(mltl_eval(&f, &whole)); },
            Mltl::False => { decided += 1; assert!(!mltl_eval(&f, &whole)); },
            _ => {},
        }
        plain_total += size(&formula_progression(&f, &t));
        prog_total += size(&g);
    }
    assert!(decided > 500);
    assert!(prog_total < plain_total);
}
