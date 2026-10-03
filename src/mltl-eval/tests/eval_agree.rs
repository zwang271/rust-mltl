//! Runtime cross-checks of the two verified evaluators (complements the proofs:
//! catches build/erasure surprises and documents expected values).
use mltl_eval::{mltl_eval, mltl_eval_bottom_up, mltl_eval_bottom_up_bits, BitTrace};
use mltl_core::mltl::Mltl;
use std::collections::HashSet;

fn p(i: usize) -> Mltl<usize> { Mltl::Prop(i) }
fn bx(f: Mltl<usize>) -> Box<Mltl<usize>> { Box::new(f) }
fn tr(steps: &[&[usize]]) -> Vec<HashSet<usize>> {
    steps.iter().map(|s| s.iter().copied().collect()).collect()
}

/// The examples of AFP `MLTL_Encoding.thy` (`[{0}]` is a one-step trace).
#[test]
fn afp_examples() {
    let t = tr(&[&[0]]);
    let cases = [
        (Mltl::Not(bx(Mltl::Future(0, 2, bx(p(0))))), false),
        (Mltl::Future(0, 2, bx(Mltl::Not(bx(p(0))))), true),
        (Mltl::Global(0, 2, bx(p(0))), false),
    ];
    for (f, expected) in cases {
        assert_eq!(mltl_eval(&f, &t), expected);
        assert_eq!(mltl_eval_bottom_up(&f, &t), expected);
        assert_eq!(mltl_eval_bottom_up_bits(&f, &BitTrace::from_sets(&t, 1)), expected);
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

fn random_formula(r: &mut Rng, depth: usize) -> Mltl<usize> {
    let leaf = depth == 0 || r.below(4) == 0;
    if leaf {
        return match r.below(5) { 0 => Mltl::True, 1 => Mltl::False, _ => p(r.below(3)) };
    }
    let (a, w) = (r.below(4), r.below(4));
    // occasionally an ill-formed interval (a > b), which both must treat as AFP does
    let b = if r.below(10) == 0 && a > 0 { a - 1 } else { a + w };
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

#[test]
fn evaluators_agree_on_random_inputs() {
    let mut r = Rng(0x9E3779B97F4A7C15);
    for _ in 0..20_000 {
        let f = random_formula(&mut r, 4);
        let len = r.below(9);
        let t: Vec<HashSet<usize>> =
            (0..len).map(|_| (0..3).filter(|_| r.below(2) == 0).collect()).collect();
        let expected = mltl_eval(&f, &t);
        assert_eq!(mltl_eval_bottom_up(&f, &t), expected);
        assert_eq!(mltl_eval_bottom_up_bits(&f, &BitTrace::from_sets(&t, 3)), expected);
    }
}
