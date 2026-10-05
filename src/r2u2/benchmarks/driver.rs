//! Benchmark driver for the verified monitor: reads a formula (AFP syntax,
//! atoms `pN`) and a trace file (one line per step, one `0`/`1` per atom),
//! times only the monitoring loop, prints `microseconds<TAB>verdicts<TAB>covered`
//! and writes the expanded per-step verdicts (`0`/`1` per line) to the output file.
//! Usage: r2u2_bench <formula> <trace-file> <out-file>
use std::collections::HashSet;
use std::io::Write;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (f, _) = mltl_parse::parse_numbered(args[1].as_bytes()).unwrap_or_else(|_| panic!("parse error: {}", args[1]));
    let text = std::fs::read_to_string(&args[2]).unwrap();
    let trace: Vec<HashSet<usize>> = text
        .lines()
        .map(|l| l.bytes().enumerate().filter(|(_, b)| *b == b'1').map(|(i, _)| i).collect())
        .collect();
    let mut m = r2u2::exec_engine::Monitor::new(&f).expect("bounds overflow");
    let t0 = Instant::now();
    for s in &trace {
        assert!(m.step(s), "overflow");
    }
    let us = t0.elapsed().as_micros();
    let out = m.verdicts();
    let mut w = std::io::BufWriter::new(std::fs::File::create(&args[3]).unwrap());
    let mut next = 0usize;
    for v in out {
        for _ in next..=v.time {
            writeln!(w, "{}", if v.val { 1 } else { 0 }).unwrap();
        }
        next = v.time + 1;
    }
    println!("{us}\t{}\t{next}", out.len());
}
