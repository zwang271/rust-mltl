//! Runtime checks of the verified WEST (complements the proofs: catches
//! build/erasure surprises and documents expected values).
use mltl_core::mltl::Mltl;
use mltl_eval::mltl_eval;
use std::collections::HashSet;
use west::algorithms::WestBit;
use west::exec::{simp_pad_WEST_reg, WEST_reg, ExecRegex};

fn bx(f: Mltl<usize>) -> Box<Mltl<usize>> { Box::new(f) }
fn p(i: usize) -> Mltl<usize> { Mltl::Prop(i) }
fn not(f: Mltl<usize>) -> Mltl<usize> { Mltl::Not(bx(f)) }
fn and(f: Mltl<usize>, g: Mltl<usize>) -> Mltl<usize> { Mltl::And(bx(f), bx(g)) }
fn or(f: Mltl<usize>, g: Mltl<usize>) -> Mltl<usize> { Mltl::Or(bx(f), bx(g)) }
fn fut(a: usize, b: usize, f: Mltl<usize>) -> Mltl<usize> { Mltl::Future(a, b, bx(f)) }
fn glob(a: usize, b: usize, f: Mltl<usize>) -> Mltl<usize> { Mltl::Global(a, b, bx(f)) }
fn until(f: Mltl<usize>, a: usize, b: usize, g: Mltl<usize>) -> Mltl<usize> { Mltl::Until(bx(f), a, b, bx(g)) }
fn release(f: Mltl<usize>, a: usize, b: usize, g: Mltl<usize>) -> Mltl<usize> { Mltl::Release(bx(f), a, b, bx(g)) }

/// Isabelle's `show` of a `WEST_regex`, e.g. `[[[S,One]],[[Zero,S]]]`.
fn show(r: &ExecRegex) -> String {
    let bit = |b: &WestBit| match b { WestBit::Zero => "Zero", WestBit::One => "One", WestBit::S => "S" };
    let list = |xs: Vec<String>| format!("[{}]", xs.join(","));
    list(r.iter().map(|t| list(t.iter().map(|s| list(s.iter().map(|b| bit(b).to_string()).collect())).collect())).collect())
}

/// Fully parenthesised text of a formula.
fn fmt(f: &Mltl<usize>) -> String {
    match f {
        Mltl::True => "true".into(),
        Mltl::False => "false".into(),
        Mltl::Prop(i) => format!("p{i}"),
        Mltl::Not(g) => format!("!{}", fmt(g)),
        Mltl::And(g, h) => format!("({} & {})", fmt(g), fmt(h)),
        Mltl::Or(g, h) => format!("({} | {})", fmt(g), fmt(h)),
        Mltl::Future(a, b, g) => format!("F[{a},{b}] {}", fmt(g)),
        Mltl::Global(a, b, g) => format!("G[{a},{b}] {}", fmt(g)),
        Mltl::Until(g, a, b, h) => format!("({} U[{a},{b}] {})", fmt(g), fmt(h)),
        Mltl::Release(g, a, b, h) => format!("({} R[{a},{b}] {})", fmt(g), fmt(h)),
    }
}

/// Unverified reference `match` (Isabelle's definition, read literally).
fn matches(trace: &[HashSet<usize>], r: &ExecRegex) -> bool {
    r.iter().any(|t| {
        trace.len() >= t.len()
            && t.iter().enumerate().all(|(time, s)| {
                s.iter().enumerate().all(|(x, b)| match b {
                    WestBit::One => trace[time].contains(&x),
                    WestBit::Zero => !trace[time].contains(&x),
                    WestBit::S => true,
                })
            })
    })
}

fn complen(f: &Mltl<usize>) -> usize {
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(g) => complen(g),
        Mltl::And(g, h) | Mltl::Or(g, h) => complen(g).max(complen(h)),
        Mltl::Future(_, b, g) | Mltl::Global(_, b, g) => b + complen(g),
        Mltl::Until(g, _, b, h) | Mltl::Release(g, _, b, h) => b + (complen(g).saturating_sub(1)).max(complen(h)),
    }
}

fn num_vars(f: &Mltl<usize>) -> usize {
    match f {
        Mltl::True | Mltl::False => 1,
        Mltl::Prop(i) => i + 1,
        Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => num_vars(g),
        Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) => num_vars(g).max(num_vars(h)),
    }
}

/// Every trace of length `len` over atoms `0..n`.
fn all_traces(n: usize, len: usize) -> Vec<Vec<HashSet<usize>>> {
    let bits = n * len;
    (0u64..(1u64 << bits))
        .map(|m| (0..len).map(|t| (0..n).filter(|&x| m >> (t * n + x) & 1 == 1).collect()).collect())
        .collect()
}

/// The theorem in `WEST_reg`'s `ensures`, checked exhaustively at lengths
/// `complen` and `complen + 1`.
fn check_exhaustive(f: &Mltl<usize>) {
    let r = WEST_reg(f);
    let rp = simp_pad_WEST_reg(f);
    let (n, c) = (num_vars(f), complen(f));
    for len in [c, c + 1] {
        for t in all_traces(n, len) {
            let want = mltl_eval(f, &t);
            assert_eq!(matches(&t, &r), want, "WEST_reg {} on {t:?}", fmt(f));
            assert_eq!(matches(&t, &rp), want, "simp_pad_WEST_reg {} on {t:?}", fmt(f));
        }
    }
}

/// The `value` examples at the end of `WEST_Algorithms.thy`. Expected
/// strings: output of Isabelle's Haskell export (differential/driver.hs).
#[test]
fn afp_value_examples() {
    use Mltl::*;
    assert_eq!(show(&WEST_reg(&True)), "[[[S]]]");
    assert_eq!(show(&WEST_reg(&False)), "[]");
    assert_eq!(show(&WEST_reg(&p(1))), "[[[S,One]]]");
    assert_eq!(show(&WEST_reg(&not(p(0)))), "[[[Zero]]]");
    assert_eq!(show(&WEST_reg(&and(not(p(0)), p(1)))), "[[[Zero,One]]]");
    assert_eq!(show(&WEST_reg(&fut(0, 2, p(1)))), "[[[S,S],[S,S],[S,One]],[[S,S],[S,One]],[[S,One]]]");
    assert_eq!(show(&WEST_reg(&or(not(p(0)), p(0)))), "[[[S]]]");
    assert_eq!(show(&simp_pad_WEST_reg(&until(p(0), 0, 2, p(0)))), "[[[One],[One],[One]],[[One],[S],[S]]]");
    // pad_WEST_reg (p0 U[0,2] p0) pads each regex of WEST_reg to length 3:
    assert_eq!(show(&WEST_reg(&until(p(0), 0, 2, p(0)))), "[[[One]],[[One],[One]],[[One],[One],[One]]]");
}

#[test]
fn exhaustive_small_formulas() {
    use Mltl::*;
    let fs = vec![
        True, False, p(0), not(p(1)),
        and(p(0), not(p(0))), or(p(0), p(1)),
        fut(0, 2, p(0)), fut(1, 3, not(p(1))), glob(0, 2, or(p(0), p(1))), glob(2, 2, p(0)),
        until(p(0), 0, 2, p(1)), until(p(0), 1, 3, p(0)), until(fut(0, 1, p(0)), 0, 1, p(1)),
        release(p(0), 0, 2, p(1)), release(p(0), 0, 0, p(1)), release(p(1), 1, 2, not(p(0))),
        release(glob(0, 2, p(0)), 0, 0, p(1)),
        not(until(p(0), 0, 2, p(1))), not(release(p(0), 1, 2, p(1))),
        not(and(fut(0, 1, p(0)), glob(1, 2, p(1)))),
        glob(0, 1, fut(0, 1, p(0))), fut(0, 1, glob(0, 1, until(p(0), 0, 1, p(1)))),
        or(glob(0, 1, p(1)), until(not(p(0)), 0, 2, and(p(0), p(1)))),
    ];
    for f in &fs {
        check_exhaustive(f);
    }
}

/// Deterministic pseudo-random formulas (no extra crates).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self, m: u64) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.0 >> 33) % m
    }
}

fn random_formula(g: &mut Lcg, depth: u32, atoms: u64) -> Mltl<usize> {
    if depth == 0 || g.next(4) == 0 {
        return match g.next(6) { 0 => Mltl::True, 1 => Mltl::False, _ => p(g.next(atoms) as usize) };
    }
    let a = g.next(2) as usize;
    let b = a + g.next(2) as usize;
    match g.next(8) {
        0 => not(random_formula(g, depth - 1, atoms)),
        1 => and(random_formula(g, depth - 1, atoms), random_formula(g, depth - 1, atoms)),
        2 => or(random_formula(g, depth - 1, atoms), random_formula(g, depth - 1, atoms)),
        3 => fut(a, b, random_formula(g, depth - 1, atoms)),
        4 => glob(a, b, random_formula(g, depth - 1, atoms)),
        5 => until(random_formula(g, depth - 1, atoms), a, b, random_formula(g, depth - 1, atoms)),
        6 => release(random_formula(g, depth - 1, atoms), a, b, random_formula(g, depth - 1, atoms)),
        _ => not(random_formula(g, depth - 1, atoms)),
    }
}

#[test]
fn exhaustive_random_formulas() {
    let mut g = Lcg(2026);
    let mut checked = 0;
    while checked < 300 {
        let f = random_formula(&mut g, 3, 3);
        if num_vars(&f) * (complen(&f) + 1) > 14 {
            continue;
        }
        check_exhaustive(&f);
        checked += 1;
    }
}
