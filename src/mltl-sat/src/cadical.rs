//! Running CaDiCaL as an external process (unverified glue, and needs no
//! trust: `Encoding::decide` checks whatever comes back).
//!
//! The CNF is written as DIMACS to a temporary directory; CaDiCaL is run as
//! `cadical -q --lrat --binary=false in.cnf proof.lrat`. Exit code 10 means
//! SAT (model on stdout, `v` lines), 20 means UNSAT (LRAT proof in the file).
use crate::solve::SolverOutput;
use propositional::lrat_text::parse_lrat;
use std::io::Write;
use std::process::Command;
use std::time::Instant;

/// Monotonic clock in nanoseconds (behind `solve::now_ns`).
pub fn clock_ns() -> u64 {
    use std::sync::OnceLock;
    static START: OnceLock<Instant> = OnceLock::new();
    START.get_or_init(Instant::now).elapsed().as_nanos() as u64
}

static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Run CaDiCaL (binary `cadical` on `PATH`, or `$CADICAL`) on a CNF.
pub fn run_cadical(cnf: &[Vec<i32>]) -> SolverOutput {
    let dir = std::env::temp_dir().join(format!(
        "mltl-sat-{}-{}",
        std::process::id(),
        COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    if std::fs::create_dir_all(&dir).is_err() {
        return SolverOutput::Unknown;
    }
    let cnf_path = dir.join("in.cnf");
    let proof_path = dir.join("proof.lrat");
    let nvars = cnf.iter().flatten().map(|l| l.unsigned_abs() as usize).max().unwrap_or(0);
    {
        let mut out = std::io::BufWriter::new(match std::fs::File::create(&cnf_path) {
            Ok(f) => f,
            Err(_) => return SolverOutput::Unknown,
        });
        let _ = writeln!(out, "p cnf {} {}", nvars, cnf.len());
        for c in cnf {
            for l in c {
                let _ = write!(out, "{} ", l);
            }
            let _ = writeln!(out, "0");
        }
    }
    let bin = std::env::var("CADICAL").unwrap_or_else(|_| "cadical".to_string());
    let result = Command::new(bin)
        .args(["-q", "--lrat", "--binary=false"])
        .arg(&cnf_path)
        .arg(&proof_path)
        .output();
    let out = match result {
        Ok(o) => o,
        Err(_) => {
            let _ = std::fs::remove_dir_all(&dir);
            return SolverOutput::Unknown;
        }
    };
    let answer = match out.status.code() {
        Some(10) => {
            let mut model = vec![false; nvars + 1];
            for line in String::from_utf8_lossy(&out.stdout).lines().filter(|l| l.starts_with('v')) {
                for t in line[1..].split_whitespace() {
                    if let Ok(l) = t.parse::<i64>() {
                        if l > 0 && (l as usize) <= nvars {
                            model[l as usize] = true;
                        }
                    }
                }
            }
            SolverOutput::Sat(model)
        }
        Some(20) => match std::fs::read_to_string(&proof_path).ok().and_then(|t| parse_lrat(&t)) {
            Some(steps) => SolverOutput::Unsat(steps),
            None => SolverOutput::Unknown,
        },
        _ => SolverOutput::Unknown,
    };
    let _ = std::fs::remove_dir_all(&dir);
    answer
}
