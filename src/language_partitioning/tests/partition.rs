//! Runtime checks of the verified language partitioning (complements the
//! proofs: catches build/erasure surprises and documents expected values).
use language_partitioning::exec::{check_lp_input, Global_mltl_decomp, LP_mltl, LP_mltl_aux, MltlExtExec};
use mltl_core::mltl::Mltl;
use mltl_core::parse_tree::MltlParseTree as T;
use mltl_eval::mltl_eval;
use std::collections::HashSet;

fn bx<X>(f: X) -> Box<X> { Box::new(f) }

// Extended formulas (Isabelle's constructors; `[]` off temporal nodes).
fn tt() -> MltlExtExec { T::True(vec![]) }
fn p(i: usize) -> MltlExtExec { T::Prop(vec![], i) }
fn or(x: MltlExtExec, y: MltlExtExec) -> MltlExtExec { T::Or(vec![], bx(x), bx(y)) }
fn fut(a: usize, b: usize, l: &[usize], x: MltlExtExec) -> MltlExtExec { T::Future(l.to_vec(), a, b, bx(x)) }
fn glob(a: usize, b: usize, l: &[usize], x: MltlExtExec) -> MltlExtExec { T::Global(l.to_vec(), a, b, bx(x)) }
fn until(x: MltlExtExec, a: usize, b: usize, l: &[usize], y: MltlExtExec) -> MltlExtExec { T::Until(l.to_vec(), bx(x), a, b, bx(y)) }
fn release(x: MltlExtExec, a: usize, b: usize, l: &[usize], y: MltlExtExec) -> MltlExtExec { T::Release(l.to_vec(), bx(x), a, b, bx(y)) }

/// Fully parenthesised text of a formula.
fn show(f: &Mltl<usize>) -> String {
    match f {
        Mltl::True => "true".into(),
        Mltl::False => "false".into(),
        Mltl::Prop(i) => format!("p{i}"),
        Mltl::Not(g) => format!("!{}", show(g)),
        Mltl::And(g, h) => format!("({} & {})", show(g), show(h)),
        Mltl::Or(g, h) => format!("({} | {})", show(g), show(h)),
        Mltl::Future(a, b, g) => format!("F[{a},{b}] {}", show(g)),
        Mltl::Global(a, b, g) => format!("G[{a},{b}] {}", show(g)),
        Mltl::Until(g, a, b, h) => format!("({} U[{a},{b}] {})", show(g), show(h)),
        Mltl::Release(g, a, b, h) => format!("({} R[{a},{b}] {})", show(g), show(h)),
    }
}

/// Like `show`, with the composition after each temporal operator.
fn show_ext(f: &MltlExtExec) -> String {
    let c = |l: &Vec<usize>| l.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    match f {
        T::True(_) => "true".into(),
        T::False(_) => "false".into(),
        T::Prop(_, i) => format!("p{i}"),
        T::Not(_, g) => format!("!{}", show_ext(g)),
        T::And(_, g, h) => format!("({} & {})", show_ext(g), show_ext(h)),
        T::Or(_, g, h) => format!("({} | {})", show_ext(g), show_ext(h)),
        T::Future(l, a, b, g) => format!("F[{a},{b}]<{}> {}", c(l), show_ext(g)),
        T::Global(l, a, b, g) => format!("G[{a},{b}]<{}> {}", c(l), show_ext(g)),
        T::Until(l, g, a, b, h) => format!("({} U[{a},{b}]<{}> {})", show_ext(g), c(l), show_ext(h)),
        T::Release(l, g, a, b, h) => format!("({} R[{a},{b}]<{}> {})", show_ext(g), c(l), show_ext(h)),
    }
}

fn lp(f: &MltlExtExec, k: usize) -> Vec<String> {
    assert!(check_lp_input(f));
    LP_mltl(f, k).iter().map(show).collect()
}

/// The `value` examples of `MLTL_Language_Partition_Algorithm.thy`
/// (`interval_times` is checked by the proof `composition::example_interval_times`).
#[test]
fn afp_examples() {
    // Global_mltl_decomp [True_c, Prop_c 0] 0 2 [3]
    let d = vec![tt(), p(0)];
    let gd: Vec<String> = Global_mltl_decomp(&d, 0, 2, &vec![3]).iter().map(show_ext).collect();
    let mut expected = vec![];
    for x0 in ["true", "p0"] {
        for x1 in ["true", "p0"] {
            for x2 in ["true", "p0"] {
                expected.push(format!("((G[0,0]<1> {x0} & G[1,1]<1> {x1}) & G[2,2]<1> {x2})"));
            }
        }
    }
    assert_eq!(gd, expected);

    // LP_mltl_aux (F_c[0,9] <[3,3,3]> (p0 Or_c p1)) 1
    let f = fut(0, 9, &[3, 3, 3], or(p(0), p(1)));
    let aux: Vec<String> = LP_mltl_aux(&f, 1).iter().map(show_ext).collect();
    assert_eq!(aux, [
        "F[0,2]<3> (p0 | p1)",
        "(G[0,2]<3> !(p0 | p1) & F[3,5]<3> (p0 | p1))",
        "(G[0,5]<6> !(p0 | p1) & F[6,8]<3> (p0 | p1))",
    ]);

    // LP_mltl (True_c Or_c p0) 1
    assert_eq!(lp(&or(tt(), p(0)), 1), ["(true & p0)", "(false & p0)", "(true & !p0)"]);

    // LP_mltl (p0 U_c[2,5] <[4]> p1) 1
    assert_eq!(lp(&until(p(0), 2, 5, &[4], p(1)), 1), ["(p0 U[2,5] p1)"]);

    // LP_mltl (p0 R_c[2,5] <[2,2]> p1) 1
    assert_eq!(lp(&release(p(0), 2, 5, &[2, 2], p(1)), 1), [
        "G[2,5] (!p0 & p1)",
        "((p0 R[2,3] p1) & F[2,3] p0)",
        "(G[2,3] (!p0 & p1) & ((p0 R[4,5] p1) & F[4,5] p0))",
    ]);

    // LP_mltl ((F_c[0,3] <[1,1,1,1]> p0) Or_c (G_c[0,3] <[1,1,1,1]> p1)) 3
    let f = or(fut(0, 3, &[1, 1, 1, 1], p(0)), glob(0, 3, &[1, 1, 1, 1], p(1)));
    assert_eq!(lp(&f, 3), [
        "(F[0,0] p0 & G[0,3] p1)",
        "((G[0,0] !p0 & F[1,1] p0) & G[0,3] p1)",
        "((G[0,1] !p0 & F[2,2] p0) & G[0,3] p1)",
        "((G[0,2] !p0 & F[3,3] p0) & G[0,3] p1)",
        "(G[0,3] !p0 & G[0,3] p1)",
        "(F[0,0] p0 & F[0,3] !p1)",
        "((G[0,0] !p0 & F[1,1] p0) & F[0,3] !p1)",
        "((G[0,1] !p0 & F[2,2] p0) & F[0,3] !p1)",
        "((G[0,2] !p0 & F[3,3] p0) & F[0,3] !p1)",
    ]);
}

#[test]
fn input_check() {
    assert!(check_lp_input(&fut(2, 7, &[2, 3, 1], p(0))));
    assert!(!check_lp_input(&fut(2, 7, &[2, 3], p(0)))); // sums to 5, not 6
    assert!(!check_lp_input(&fut(2, 7, &[6, 0], p(0)))); // zero width
    assert!(!check_lp_input(&fut(3, 2, &[1], p(0)))); // a > b
    assert!(check_lp_input(&fut(0, usize::MAX - 1, &[usize::MAX], p(0))));
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

/// A random composition of `n` (all ones if `ones`).
fn composition(r: &mut Rng, n: usize, ones: bool) -> Vec<usize> {
    if ones {
        return vec![1; n];
    }
    let mut l = vec![];
    let mut rem = n;
    while rem > 0 {
        let x = 1 + r.below(rem as u64);
        l.push(x);
        rem -= x;
    }
    l
}

fn random_ext(r: &mut Rng, depth: usize, ones: bool) -> MltlExtExec {
    if depth == 0 || (depth < 3 && r.below(5) == 0) {
        return match r.below(5) { 0 => tt(), 1 => T::False(vec![]), _ => p(r.below(2)) };
    }
    let a = r.below(2);
    let b = a + r.below(3);
    let l = composition(r, b - a + 1, ones);
    let sub = |r: &mut Rng| random_ext(r, depth - 1, ones);
    match r.below(7) {
        0 => T::Not(vec![], bx(sub(r))),
        1 => T::And(vec![], bx(sub(r)), bx(sub(r))),
        2 => or(sub(r), sub(r)),
        3 => fut(a, b, &l, sub(r)),
        4 => glob(a, b, &l, sub(r)),
        5 => until(sub(r), a, b, &l, sub(r)),
        _ => release(sub(r), a, b, &l, sub(r)),
    }
}

/// Unverified test helper: `wpd_mltl`.
fn wpd(f: &Mltl<usize>) -> usize {
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(g) => wpd(g),
        Mltl::And(g, h) | Mltl::Or(g, h) => wpd(g).max(wpd(h)),
        Mltl::Future(_, b, g) | Mltl::Global(_, b, g) => b + wpd(g),
        Mltl::Until(g, _, b, h) | Mltl::Release(g, _, b, h) => b + wpd(g).max(wpd(h)),
    }
}

fn random_trace(r: &mut Rng, len: usize) -> Vec<HashSet<usize>> {
    (0..len).map(|_| (0..2).filter(|_| r.below(2) == 0).collect()).collect()
}

/// The guarantees of `LP_mltl`, checked with the verified evaluator: on
/// traces of length ≥ wpd exactly as many partition formulas hold as the
/// formula itself (1 or 0) when the partition is disjoint, and at least one
/// exactly when the formula holds otherwise.
#[test]
fn random_union_and_disjointness() {
    let mut r = Rng(0x9e3779b97f4a7c15);
    let mut checked = 0;
    let (mut total, mut maxd) = (0usize, 0usize);
    for round in 0..1000 {
        let ones = round % 2 == 0;
        let f = random_ext(&mut r, 3, ones);
        assert!(check_lp_input(&f));
        let k = 1 + r.below(if ones { 3 } else { 2 });
        let d = LP_mltl(&f, k);
        total += d.len();
        maxd = maxd.max(d.len());
        let plain = mltl_core::parse_tree::mltl_parse_tree_to_mltl(&f);
        let w = wpd(&plain);
        for _ in 0..10 {
            let extra = r.below(3);
            let t = random_trace(&mut r, w + extra);
            let holds = mltl_eval(&plain, &t);
            let n = d.iter().filter(|g| mltl_eval(g, &t)).count();
            assert_eq!(holds, n > 0, "union: {} on {:?}", show(&plain), t);
            if ones || k == 1 {
                // formulas are compared structurally, so count distinct ones
                let distinct: HashSet<String> = d.iter().filter(|g| mltl_eval(g, &t)).map(show).collect();
                assert!(distinct.len() <= 1, "disjointness: {} on {:?}", show(&plain), t);
            }
            checked += 1;
        }
    }
    assert_eq!(checked, 10000);
    assert!(total > 3000 && maxd > 100, "random formulas too small: {total} {maxd}");
}
