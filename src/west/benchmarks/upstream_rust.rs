//! Timing harness for upstream WEST's Rust implementation
//! (WEST/src/west_rust, `west_rust::compile`). Same output as driver.rs.
//! Built by run.py in build/upstream_rust (a generated Cargo project).
//! Usage: upstream_rust <file> [start-index]
use std::io::Write;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let text = std::fs::read_to_string(&args[1]).unwrap();
    let start: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(0);
    let out = std::io::stdout();
    let mut out = out.lock();
    for (i, line) in text.lines().enumerate().skip(start) {
        if line.trim().is_empty() { continue; }
        let f = west_rust::MLTL::parse(line).unwrap_or_else(|e| panic!("parse error {e}: {line}"));
        let t0 = Instant::now();
        let r = west_rust::compile(f);
        let us = t0.elapsed().as_micros();
        writeln!(out, "{i}\t{us}\t{}", r.len()).unwrap();
        out.flush().unwrap();
    }
}
