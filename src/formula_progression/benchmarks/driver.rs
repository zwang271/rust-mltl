//! Benchmark driver for the verified Rust formula progression.
//!
//!   fp_bench <mode> formulas.txt traces.txt min_seconds
//!   mode: prog       `prog(f, trace)` per (formula, trace) pair
//!         prog-step  `prog` over one state at a time, feeding each result
//!                    back, stopping at True/False (what the deployed API does)
//!         plain      `formula_progression(f, trace)` (AFP, no simplification)
//!
//! Built with `--cfg fp_bench_mimalloc`, the mode is reported as `rust-mi-<mode>`.
//!
//! Prints `rust-<mode>,formulas,traces,reps,total_s,ns_per_call,hash`; the
//! hash (FNV-1a over every result in prefix notation) matches the Haskell
//! driver's, so answers can be compared. Formats: `gen_workloads.py`.
use formula_progression::algorithm::formula_progression;
use formula_progression::extended::{prog, prog_owned};
use mltl_core::mltl::Mltl;
use std::collections::HashSet;
use std::hint::black_box;
use std::time::Instant;

// `run.py` also builds this driver with `--cfg fp_bench_mimalloc` to measure
// the same code under a faster allocator (the library itself is unchanged).
#[cfg(fp_bench_mimalloc)]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn parse<'a>(t: &mut impl Iterator<Item = &'a str>) -> Mltl<usize> {
    let tok = t.next().expect("formula ends early");
    let num = |t: &mut dyn Iterator<Item = &'a str>| -> usize { t.next().unwrap().parse().unwrap() };
    let bx = |f: Mltl<usize>| Box::new(f);
    match tok {
        "true" => Mltl::True,
        "false" => Mltl::False,
        "!" => Mltl::Not(bx(parse(t))),
        "&" => { let a = parse(t); Mltl::And(bx(a), bx(parse(t))) }
        "|" => { let a = parse(t); Mltl::Or(bx(a), bx(parse(t))) }
        "F" => { let (a, b) = (num(t), num(t)); Mltl::Future(a, b, bx(parse(t))) }
        "G" => { let (a, b) = (num(t), num(t)); Mltl::Global(a, b, bx(parse(t))) }
        "U" => { let (a, b) = (num(t), num(t)); let f = parse(t); Mltl::Until(bx(f), a, b, bx(parse(t))) }
        "R" => { let (a, b) = (num(t), num(t)); let f = parse(t); Mltl::Release(bx(f), a, b, bx(parse(t))) }
        p => Mltl::Prop(p.strip_prefix('p').expect("atom").parse().unwrap()),
    }
}

fn pr(f: &Mltl<usize>, out: &mut String) {
    use std::fmt::Write;
    match f {
        Mltl::True => out.push_str("true"),
        Mltl::False => out.push_str("false"),
        Mltl::Prop(p) => { write!(out, "p{p}").unwrap(); }
        Mltl::Not(g) => { out.push_str("! "); pr(g, out) }
        Mltl::And(g, h) => { out.push_str("& "); pr(g, out); out.push(' '); pr(h, out) }
        Mltl::Or(g, h) => { out.push_str("| "); pr(g, out); out.push(' '); pr(h, out) }
        Mltl::Future(a, b, g) => { write!(out, "F {a} {b} ").unwrap(); pr(g, out) }
        Mltl::Global(a, b, g) => { write!(out, "G {a} {b} ").unwrap(); pr(g, out) }
        Mltl::Until(g, a, b, h) => { write!(out, "U {a} {b} ").unwrap(); pr(g, out); out.push(' '); pr(h, out) }
        Mltl::Release(g, a, b, h) => { write!(out, "R {a} {b} ").unwrap(); pr(g, out); out.push(' '); pr(h, out) }
    }
}

fn stepwise(f: &Mltl<usize>, t: &[HashSet<usize>]) -> Mltl<usize> {
    let mut cur = prog(f, &t[..0]);
    for i in 0..t.len() {
        cur = prog_owned(cur, &t[i..i + 1]);
        if matches!(cur, Mltl::True | Mltl::False) {
            break;
        }
    }
    cur
}

fn run(mode: &str, f: &Mltl<usize>, t: &[HashSet<usize>]) -> Mltl<usize> {
    match mode {
        "prog" => prog(f, t),
        "prog-step" => stepwise(f, t),
        "plain" => formula_progression(f, t),
        _ => panic!("unknown mode {mode}"),
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let (mode, min_s): (&str, f64) = (&a[1], a[4].parse().unwrap());
    let fs: Vec<Mltl<usize>> = std::fs::read_to_string(&a[2]).unwrap().lines().filter(|l| !l.is_empty())
        .map(|l| parse(&mut l.split_whitespace())).collect();
    let ts: Vec<Vec<HashSet<usize>>> = std::fs::read_to_string(&a[3]).unwrap().lines().filter(|l| !l.is_empty())
        .map(|l| l.split_whitespace()
            .map(|s| s.bytes().enumerate().filter(|(_, c)| *c == b'1').map(|(i, _)| i).collect()).collect())
        .collect();
    let start = Instant::now();
    let mut reps = 0u64;
    loop {
        for f in &fs {
            for t in &ts {
                black_box(run(mode, black_box(f), black_box(t)));
            }
        }
        reps += 1;
        if start.elapsed().as_secs_f64() >= min_s {
            break;
        }
    }
    let total = start.elapsed().as_secs_f64();
    let mut h: u64 = 14695981039346656037;
    let mut s = String::new();
    for f in &fs {
        for t in &ts {
            s.clear();
            pr(&run(mode, f, t), &mut s);
            s.push('\n');
            for b in s.bytes() {
                h = (h ^ b as u64).wrapping_mul(1099511628211);
            }
        }
    }
    let calls = (reps as usize * fs.len() * ts.len()) as f64;
    let name = if cfg!(fp_bench_mimalloc) { "rust-mi" } else { "rust" };
    println!("{name}-{mode},{},{},{reps},{total},{},{h:x}", fs.len(), ts.len(), total * 1e9 / calls);
}
