//! Benchmark driver for the two verified evaluators (crate `mltl-eval`).
//!
//! Usage: bench_driver <topdown|bottomup> <formulas.txt> <traces.txt> <min_seconds>
//!
//! formulas.txt: one formula per line in libmltl syntax (`!`, `&`, `|`,
//!   `F[a,b]`, `G[a,b]`, `U[a,b]`, `R[a,b]`, `true`, `false`, `p<N>`).
//! traces.txt: one trace per line; time steps separated by spaces, each step a
//!   bit string whose N-th character is atom pN (libmltl's trace format).
//!
//! Prints one CSV line: evaluator,formulas,traces,reps,total_s,ns_per_eval,trues,hash
//! where `hash` is an FNV-1a hash of all results in (formula, trace) order.
//!
//! NOT verified: the parser below is benchmark scaffolding (milestone 3 is
//! the verified parser).
use mltl_eval::{mltl_eval, mltl_eval_bottom_up};
use mltl_eval::bottom_up::mltl_eval_bottom_up_bits;
use mltl_eval::bit_trace::BitTrace as VerifiedBitTrace;
#[path = "proto.rs"]
mod proto;
use proto::{eval_bottom_up as proto_eval, BitTrace, StepMasks};
use mltl_core::mltl::Mltl;
use std::collections::HashSet;
use std::time::Instant;

struct P<'a> { s: &'a [u8], i: usize }
impl<'a> P<'a> {
    fn peek(&self) -> u8 { *self.s.get(self.i).unwrap_or(&0) }
    fn eat(&mut self, c: u8) -> bool { if self.peek() == c { self.i += 1; true } else { false } }
    fn num(&mut self) -> usize {
        let st = self.i;
        while self.peek().is_ascii_digit() { self.i += 1; }
        std::str::from_utf8(&self.s[st..self.i]).unwrap().parse().expect("number")
    }
    fn interval(&mut self) -> (usize, usize) {
        assert!(self.eat(b'['));
        let a = self.num();
        assert!(self.eat(b','));
        let b = self.num();
        assert!(self.eat(b']'));
        (a, b)
    }
    fn or(&mut self) -> Mltl<usize> {
        let mut l = self.and();
        while self.eat(b'|') { l = Mltl::Or(Box::new(l), Box::new(self.and())); }
        l
    }
    fn and(&mut self) -> Mltl<usize> {
        let mut l = self.ur();
        while self.eat(b'&') { l = Mltl::And(Box::new(l), Box::new(self.ur())); }
        l
    }
    fn ur(&mut self) -> Mltl<usize> {
        let mut l = self.unary();
        loop {
            if self.eat(b'U') { let (a, b) = self.interval(); l = Mltl::Until(Box::new(l), a, b, Box::new(self.unary())); }
            else if self.eat(b'R') { let (a, b) = self.interval(); l = Mltl::Release(Box::new(l), a, b, Box::new(self.unary())); }
            else { return l; }
        }
    }
    fn unary(&mut self) -> Mltl<usize> {
        if self.eat(b'!') { return Mltl::Not(Box::new(self.unary())); }
        if self.eat(b'F') { let (a, b) = self.interval(); return Mltl::Future(a, b, Box::new(self.unary())); }
        if self.eat(b'G') { let (a, b) = self.interval(); return Mltl::Global(a, b, Box::new(self.unary())); }
        if self.eat(b'(') { let f = self.or(); assert!(self.eat(b')'), "missing )"); return f; }
        if self.s[self.i..].starts_with(b"true") { self.i += 4; return Mltl::True; }
        if self.s[self.i..].starts_with(b"false") { self.i += 5; return Mltl::False; }
        assert!(self.eat(b'p'), "unexpected input at {}", self.i);
        Mltl::Prop(self.num())
    }
}

fn parse(line: &str) -> Mltl<usize> {
    let s: String = line.chars().filter(|c| !c.is_whitespace()).collect();
    let mut p = P { s: s.as_bytes(), i: 0 };
    let f = p.or();
    assert_eq!(p.i, p.s.len(), "trailing input in {line}");
    f
}

fn parse_trace(line: &str) -> Vec<HashSet<usize>> {
    line.split_whitespace()
        .map(|step| step.bytes().enumerate().filter(|(_, c)| *c == b'1').map(|(i, _)| i).collect())
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert!(args.len() == 5, "usage: bench_driver <topdown|bottomup> <formulas> <traces> <min_seconds>");
    let which = args[1].as_str();
    let formulas: Vec<Mltl<usize>> = std::fs::read_to_string(&args[2]).unwrap()
        .lines().filter(|l| !l.trim().is_empty()).map(parse).collect();
    let traces: Vec<Vec<HashSet<usize>>> = std::fs::read_to_string(&args[3]).unwrap()
        .lines().filter(|l| !l.trim().is_empty()).map(parse_trace).collect();
    let min_s: f64 = args[4].parse().unwrap();
    // Unverified prototypes (T10.4). "proto-bits" converts every trace to the
    // bit-row representation once, before timing; the conversion cost is
    // reported separately on stderr.
    let conv = Instant::now();
    let bits: Vec<BitTrace> = if which == "proto-bits" {
        traces.iter().map(|t| BitTrace::from_sets(t)).collect()
    } else {
        Vec::new()
    };
    let vbits: Vec<VerifiedBitTrace> = if which == "bottomup-bits" {
        traces.iter().map(|t| {
            let atoms = t.iter().flat_map(|s| s.iter().copied()).max().map_or(0, |m| m + 1);
            VerifiedBitTrace::from_sets(t, atoms)
        }).collect()
    } else {
        Vec::new()
    };
    let masks: Vec<StepMasks> = if which == "proto-masks" {
        traces.iter().map(|t| StepMasks::from_sets(t)).collect()
    } else {
        Vec::new()
    };
    eprintln!("conversion_s={:.6}", conv.elapsed().as_secs_f64());
    let eval: Box<dyn Fn(&Mltl<usize>, usize) -> bool> = match which {
        "topdown" => Box::new(|f, j| mltl_eval(f, &traces[j])),
        "bottomup" => Box::new(|f, j| mltl_eval_bottom_up(f, &traces[j])),
        "bottomup-bits" => Box::new(|f, j| mltl_eval_bottom_up_bits(f, &vbits[j])),
        "proto-hash" => Box::new(|f, j| proto_eval(f, traces[j].as_slice())),
        "proto-bits" => Box::new(|f, j| proto_eval(f, &bits[j])),
        "proto-masks" => Box::new(|f, j| proto_eval(f, &masks[j])),
        _ => panic!("unknown evaluator {which}"),
    };
    let (mut reps, mut trues, mut hash) = (0u64, 0u64, 0u64);
    let start = Instant::now();
    loop {
        trues = 0;
        hash = 0xcbf29ce484222325;
        for f in &formulas {
            for j in 0..traces.len() {
                let r = eval(f, j);
                trues += r as u64;
                hash = (hash ^ r as u64).wrapping_mul(0x100000001b3);
            }
        }
        reps += 1;
        if start.elapsed().as_secs_f64() >= min_s { break; }
    }
    let total = start.elapsed().as_secs_f64();
    let evals = reps as f64 * formulas.len() as f64 * traces.len() as f64;
    println!("{which},{},{},{reps},{total:.6},{:.3},{trues},{hash:016x}",
             formulas.len(), traces.len(), total * 1e9 / evals);
}
