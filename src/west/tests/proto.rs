//! The unverified fast prototype (benchmarks/proto.rs) agrees with the
//! verified evaluator on every short trace, for random formulas.
#[path = "../benchmarks/proto.rs"]
mod proto;

use mltl_core::mltl::Mltl;
use mltl_eval::mltl_eval;
use std::collections::HashSet;

fn complen(f: &Mltl<usize>) -> usize {
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(g) => complen(g),
        Mltl::And(g, h) | Mltl::Or(g, h) => complen(g).max(complen(h)),
        Mltl::Future(_, b, g) | Mltl::Global(_, b, g) => b + complen(g),
        Mltl::Until(g, _, b, h) | Mltl::Release(g, _, b, h) => b + (complen(g).saturating_sub(1)).max(complen(h)),
    }
}

fn matches(trace: &[HashSet<usize>], r: &proto::Regex) -> bool {
    (0..r.count()).any(|i| {
        let t = proto::decode(r, i);
        trace.len() >= t.len() && t.iter().enumerate().all(|(s, st)| st.iter().enumerate().all(|(x, b)| match b {
            0b10 => trace[s].contains(&x),
            0b01 => !trace[s].contains(&x),
            0b11 => true,
            _ => false,
        }))
    })
}

struct Lcg(u64);
impl Lcg {
    fn next(&mut self, m: u64) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.0 >> 33) % m
    }
}

fn bx(f: Mltl<usize>) -> Box<Mltl<usize>> { Box::new(f) }

fn random_formula(g: &mut Lcg, depth: u32, atoms: u64) -> Mltl<usize> {
    if depth == 0 || g.next(4) == 0 {
        return match g.next(6) { 0 => Mltl::True, 1 => Mltl::False, _ => Mltl::Prop(g.next(atoms) as usize) };
    }
    let a = g.next(3) as usize;
    let b = a + g.next(2) as usize;
    let mut sub = |g: &mut Lcg| random_formula(g, depth - 1, atoms);
    match g.next(8) {
        0 | 7 => Mltl::Not(bx(sub(g))),
        1 => { let x = sub(g); Mltl::And(bx(x), bx(sub(g))) }
        2 => { let x = sub(g); Mltl::Or(bx(x), bx(sub(g))) }
        3 => Mltl::Future(a, b, bx(sub(g))),
        4 => Mltl::Global(a, b, bx(sub(g))),
        5 => { let x = sub(g); Mltl::Until(bx(x), a, b, bx(sub(g))) }
        _ => { let x = sub(g); Mltl::Release(bx(x), a, b, bx(sub(g))) }
    }
}

#[test]
fn proto_agrees_with_semantics() {
    let mut g = Lcg(7);
    let mut checked = 0;
    while checked < 500 {
        let f = random_formula(&mut g, 3, 3);
        let (n, c) = (proto::num_vars(&f), complen(&f));
        if n * (c + 1) > 14 { continue; }
        let r = proto::fast_reg(&f);
        assert_eq!(r.len, c, "{}", fmt(&f));
        for len in [c, c + 1] {
            for m in 0u64..(1 << (n * len)) {
                let t: Vec<HashSet<usize>> = (0..len).map(|s| (0..n).filter(|&x| m >> (s * n + x) & 1 == 1).collect()).collect();
                assert_eq!(matches(&t, &r), mltl_eval(&f, &t));
            }
        }
        checked += 1;
    }
}

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
