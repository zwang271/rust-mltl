//! WEST benchmark driver: reads one formula per line (WEST/libmltl syntax),
//! runs one implementation, prints `index<TAB>microseconds<TAB>regexes` per
//! formula (flushed, so run.py can enforce per-formula timeouts).
//! Implementations: `faithful` (verified `simp_pad_WEST_reg`), `fast`
//! (verified `fast_reg_checked`), `proto` (the unverified prototype it was
//! designed from, benchmarks/proto.rs).
//! Usage: west_bench <impl> <file> [start-index]
#[path = "proto.rs"]
mod proto;

use std::io::Write;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let which = args[1].as_str();
    let text = std::fs::read_to_string(&args[2]).unwrap();
    let start: usize = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(0);
    let out = std::io::stdout();
    let mut out = out.lock();
    for (i, line) in text.lines().enumerate().skip(start) {
        if line.trim().is_empty() { continue; }
        let (f, _) = mltl_parse::parse_numbered(line.as_bytes()).unwrap_or_else(|_| panic!("parse error: {line}"));
        let t0 = Instant::now();
        let count = match which {
            "faithful" => west::exec::simp_pad_WEST_reg(&f).len(),
            "proto" => proto::fast_reg(&f).count(),
            "fast" => west::api::fast_reg_checked(&f).expect("too large").traces.len(),
            _ => panic!("unknown implementation {which}"),
        };
        let us = t0.elapsed().as_micros();
        writeln!(out, "{i}\t{us}\t{count}").unwrap();
        out.flush().unwrap();
    }
}
