//! Runtime check of the executable monitor against `mltl-eval`'s verified
//! evaluator on random formulas and traces (the proofs already guarantee
//! agreement; this exercises the plumbing).
use mltl_core::mltl::Mltl;
use r2u2::exec_engine::{monitor_trace, wpd_ex, Monitor};
use std::collections::HashSet;

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: u64) -> usize {
        (self.next() % n) as usize
    }
}

fn formula(r: &mut Lcg, depth: usize) -> Mltl<usize> {
    if depth == 0 || r.below(5) == 0 {
        return match r.below(10) {
            0 => Mltl::True,
            1 => Mltl::False,
            _ => Mltl::Prop(r.below(3)),
        };
    }
    let sub = |r: &mut Lcg| Box::new(formula(r, depth - 1));
    let a = r.below(4);
    let b = a + r.below(4);
    match r.below(9) {
        0 => Mltl::Not(sub(r)),
        1 => Mltl::And(sub(r), sub(r)),
        2 => Mltl::Or(sub(r), sub(r)),
        3 => Mltl::Future(a, b, sub(r)),
        4 => Mltl::Global(a, b, sub(r)),
        5 | 6 => Mltl::Until(sub(r), a, b, sub(r)),
        _ => Mltl::Release(sub(r), a, b, sub(r)),
    }
}

#[test]
fn monitor_agrees_with_evaluator() {
    let mut r = Lcg(42);
    let mut checked = 0usize;
    for case in 0..3000 {
        let f = formula(&mut r, 4);
        let len = 1 + r.below(30);
        let trace: Vec<HashSet<usize>> =
            (0..len).map(|_| (0..3).filter(|_| r.below(2) == 0).collect()).collect();
        let out = monitor_trace(&f, &trace).expect("no overflow on small bounds");
        // expand the compacted verdicts and compare each step
        let mut next = 0usize;
        for v in &out {
            for t in next..=v.time {
                assert_eq!(v.val, mltl_eval::top_down::mltl_eval(&f, &trace[t..]), "case {} step {}", case, t);
                checked += 1;
            }
            next = v.time + 1;
        }
        // promptness: every step t with t + wpd < len is covered
        let w = wpd_ex(&f).unwrap();
        assert!(next + w >= len || w >= len, "case {}: covered {} of {} (wpd {})", case, next, len, w);
    }
    assert!(checked > 10000);
}

#[test]
fn online_steps() {
    // p0 U[0,2] p1 on {p0}, {p0}, {p1}: true at steps 0..2
    let f = Mltl::Until(Box::new(Mltl::Prop(0)), 0, 2, Box::new(Mltl::Prop(1)));
    let mut m = Monitor::new(&f).unwrap();
    for s in [vec![0], vec![0], vec![1]] {
        assert!(m.step(&s.into_iter().collect()));
    }
    let out = m.verdicts();
    assert_eq!(out.last().map(|v| (v.val, v.time)), Some((true, 2)));
}
