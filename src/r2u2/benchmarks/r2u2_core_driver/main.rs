//! Benchmark driver for R2U2's `r2u2_core` (same inputs and outputs as
//! ../driver.rs, but the formula comes compiled by C2PO). Built by run.py
//! with R2U2's pinned toolchain. Usage: driver <spec.bin> <trace-file> <out-file>
use std::io::Write;
use std::time::Instant;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let spec = std::fs::read(&a[1]).unwrap();
    let text = std::fs::read_to_string(&a[2]).unwrap();
    let trace: Vec<Vec<bool>> = text.lines().map(|l| l.bytes().map(|b| b == b'1').collect()).collect();
    let mut m = r2u2_core::get_monitor(&spec);
    let mut verdicts: Vec<(bool, u32)> = Vec::new();
    let mut count = 0usize;
    let t0 = Instant::now();
    for row in &trace {
        for (i, v) in row.iter().enumerate() {
            r2u2_core::load_bool_signal(&mut m, i, *v);
        }
        r2u2_core::monitor_step(&mut m);
        for o in r2u2_core::get_output_buffer(&m) {
            verdicts.push((o.verdict.truth, o.verdict.time));
            count += 1;
        }
    }
    let us = t0.elapsed().as_micros();
    let mut w = std::io::BufWriter::new(std::fs::File::create(&a[3]).unwrap());
    let mut next = 0u32;
    for (val, t) in verdicts {
        while next <= t {
            writeln!(w, "{}", if val { 1 } else { 0 }).unwrap();
            next += 1;
        }
    }
    println!("{us}\t{count}\t{next}");
}
