//! The examples in README.md.
use mltl_core::mltl::Mltl;
use r2u2::exec_engine::Monitor;
use std::collections::HashSet;

fn run(f: &Mltl<usize>, trace: &[&[usize]]) -> Vec<(bool, usize)> {
    let mut m = Monitor::new(f).unwrap();
    for s in trace {
        assert!(m.step(&s.iter().copied().collect::<HashSet<usize>>()));
    }
    m.verdicts().iter().map(|v| (v.val, v.time)).collect()
}

#[test]
fn not_example() {
    let f = Mltl::Not(Box::new(Mltl::Prop(0)));
    assert_eq!(run(&f, &[&[0], &[0], &[]]), vec![(false, 0), (false, 1), (true, 2)]);
}

#[test]
fn r2u2_core_counterexample() {
    // p0 U[0,0] ((p1 U[1,1] p0) U[0,2] p1) on {}, {p0}, {p1}: false at steps 0 and 1, true at 2
    let p = |i| Box::new(Mltl::Prop(i));
    let inner = Mltl::Until(p(1), 1, 1, p(0));
    let mid = Mltl::Until(Box::new(inner), 0, 2, p(1));
    let f = Mltl::Until(p(0), 0, 0, Box::new(mid));
    let out = run(&f, &[&[], &[0], &[1]]);
    let mut per_step = Vec::new();
    let mut next = 0;
    for (v, t) in out {
        while next <= t { per_step.push(v); next += 1; }
    }
    assert_eq!(per_step, vec![false, false, true]);
}
