//! Benchmark driver for R2U2, same output format as `../driver.rs`:
//!   r2u2_driver <specs_dir> <traces.txt> <min_seconds>
//! `specs_dir` holds `COUNT` (number of formulas) and `0.bin`, `1.bin`, ...:
//! one C2PO-compiled spec per formula (formulas.txt order) over atoms a0, a1, ...
//! A missing `<i>.bin` means C2PO rejected the formula (constant formulas are
//! not supported); it is skipped in timing, counted as false in the hash, and
//! reported as `unsupported` on stderr.
//!
//! R2U2 is an online monitor: each trace is streamed step by step and
//! streaming stops as soon as the verdict for time 0 is out. R2U2 has no
//! end-of-trace flush, so when the trace ends first the result is
//! "undecided" (reported on stderr; counted as false in the hash).
//!
//! Timing covers only the stepping loop. Re-initialising the monitor between
//! traces (`update_binary_file`) costs time proportional to the configured
//! queue memory, not to the formula, and is excluded.
use std::time::{Duration, Instant};

fn run() {
    let args: Vec<String> = std::env::args().collect();
    assert!(args.len() == 4, "usage: r2u2_driver <specs_dir> <traces.txt> <min_seconds>");
    let dir = std::path::Path::new(&args[1]);
    let count: usize = std::fs::read_to_string(dir.join("COUNT")).unwrap().trim().parse().unwrap();
    let specs: Vec<Option<Vec<u8>>> = (0..count).map(|i| std::fs::read(dir.join(format!("{i}.bin"))).ok()).collect();
    let unsupported = specs.iter().filter(|s| s.is_none()).count();
    let traces: Vec<Vec<Vec<bool>>> = std::fs::read_to_string(&args[2]).unwrap()
        .lines().filter(|l| !l.trim().is_empty())
        .map(|l| l.split_whitespace().map(|s| s.bytes().map(|c| c == b'1').collect()).collect())
        .collect();
    let min_s: f64 = args[3].parse().unwrap();
    let first = specs.iter().flatten().next().expect("no supported formula");
    let mut monitor = Box::new(r2u2_core::get_monitor(first));
    let (mut reps, mut trues, mut hash, mut undecided, mut overflow) = (0u64, 0u64, 0u64, 0u64, false);
    let mut timed = Duration::ZERO;
    let wall = Instant::now();
    loop {
        trues = 0;
        undecided = 0;
        hash = 0xcbf29ce484222325;
        for spec in &specs {
            for t in &traces {
                let Some(spec) = spec else {
                    hash = hash.wrapping_mul(0x100000001b3);
                    continue;
                };
                // Workaround for an R2U2 bug (external/r2u2 @ 5573897): `Monitor::reset`
                // clears `bz_program_count.max_program_count` twice and never
                // `mltl_program_count.max_program_count`, so reloading a spec
                // appends to the instruction table until it overflows.
                monitor.mltl_program_count.max_program_count = 0;
                r2u2_core::update_binary_file(spec, &mut monitor);
                let start = Instant::now();
                let mut verdict = None;
                'steps: for step in t {
                    for (i, &v) in step.iter().enumerate() {
                        r2u2_core::load_bool_signal(&mut monitor, i, v);
                    }
                    r2u2_core::monitor_step(&mut monitor);
                    for out in r2u2_core::get_output_buffer(&monitor) {
                        // The first verdict covers times 0..=out.verdict.time.
                        verdict = Some(out.verdict.truth);
                        break 'steps;
                    }
                }
                timed += start.elapsed();
                overflow |= r2u2_core::get_overflow_error(&monitor);
                let r = verdict.unwrap_or(false);
                undecided += verdict.is_none() as u64;
                trues += r as u64;
                hash = (hash ^ r as u64).wrapping_mul(0x100000001b3);
            }
        }
        reps += 1;
        if timed.as_secs_f64() >= min_s || wall.elapsed().as_secs_f64() >= 20.0 { break; }
    }
    let total = timed.as_secs_f64();
    let evals = reps as f64 * (count - unsupported) as f64 * traces.len() as f64;
    eprintln!("undecided={undecided} unsupported={unsupported} overflow={overflow} max_queue_slots={}",
              r2u2_core::R2U2_MAX_QUEUE_SLOTS);
    println!("r2u2,{},{},{reps},{total:.6},{:.3},{trues},{hash:016x}", specs.len(), traces.len(), total * 1e9 / evals);
}

fn main() {
    // The monitor is a large fixed-size struct built on the stack.
    std::thread::Builder::new().stack_size(1 << 30).spawn(run).unwrap().join().unwrap();
}
