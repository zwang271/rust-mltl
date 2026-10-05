//! Runtime checks of the verified fast WEST (`fast_reg_checked`): agrees
//! with the verified evaluator on every short trace, for many random
//! formulas; text output in WEST's format.
use mltl_core::mltl::Mltl;
use mltl_eval::mltl_eval;
use std::collections::HashSet;
use west::api::{fast_reg_checked, trace_to_text};
use west::fast::Packed;

fn texts(r: &Packed) -> Vec<String> {
    (0..r.traces.len()).map(|i| String::from_utf8(trace_to_text(r, i)).unwrap()).collect()
}

/// Reference `match` on WEST text (`s1,0s`), read literally.
fn matches(trace: &[HashSet<usize>], rs: &[String]) -> bool {
    rs.iter().any(|r| {
        let states: Vec<&str> = r.split(',').collect();
        trace.len() >= states.len()
            && states.iter().enumerate().all(|(t, s)| s.chars().enumerate().all(|(x, c)| match c {
                '1' => trace[t].contains(&x),
                '0' => !trace[t].contains(&x),
                _ => true,
            }))
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
fn text_examples() {
    use Mltl::*;
    let p = |i| Prop(i);
    // F[0,2] p1: three regexes, each three states long.
    let mut t = texts(&fast_reg_checked(&Future(0, 2, bx(p(1)))).unwrap());
    t.sort();
    assert_eq!(t, vec!["s1,ss,ss", "ss,s1,ss", "ss,ss,s1"]);
    // p0 U[0,2] p0: the same two regexes as Isabelle's simp_pad_WEST_reg
    // (simplification merges, it does not drop subsumed regexes).
    let mut u = texts(&fast_reg_checked(&Until(bx(p(0)), 0, 2, bx(p(0)))).unwrap());
    u.sort();
    assert_eq!(u, vec!["1,1,1", "1,s,s"]);
    // G[0,15] (p0 & !p1): one 16-state regex (upstream Rust WEST returns none).
    let g = Global(0, 15, bx(And(bx(p(0)), bx(Not(bx(p(1)))))));
    assert_eq!(texts(&fast_reg_checked(&g).unwrap()), vec![vec!["10"; 16].join(",")]);
    assert!(fast_reg_checked(&False).unwrap().traces.is_empty());
}

#[test]
fn fast_agrees_with_semantics() {
    let mut g = Lcg(11);
    let mut checked = 0;
    while checked < 600 {
        let f = random_formula(&mut g, 3, 3);
        let (n, c) = (num_vars(&f), complen(&f));
        if n * (c + 1) > 14 { continue; }
        let r = fast_reg_checked(&f).unwrap();
        assert_eq!((r.n, r.len), (n, c));
        let rs = texts(&r);
        for len in [c, c + 1] {
            for m in 0u64..(1 << (n * len)) {
                let t: Vec<HashSet<usize>> = (0..len).map(|s| (0..n).filter(|&x| m >> (s * n + x) & 1 == 1).collect()).collect();
                assert_eq!(matches(&t, &rs), mltl_eval(&f, &t));
            }
        }
        checked += 1;
    }
}
