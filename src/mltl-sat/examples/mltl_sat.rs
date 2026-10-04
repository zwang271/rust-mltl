//! `mltl_sat FORMULA` or `mltl_sat --file FORMULAS.txt`: decide MLTL
//! satisfiability (on traces of length complen) with CaDiCaL, every answer
//! checked by verified code. Needs `cadical` on PATH (or `$CADICAL`).
use mltl_sat::solve::solve;
use mltl_sat::solve::Answer;

fn run(text: &str, verbose: bool) {
    let (f, names) = match mltl_parse::parse_numbered(text.trim().as_bytes()) {
        Ok(r) => r,
        Err(e) => {
            println!("PARSE ERROR {:?}", e);
            return;
        }
    };
    let name = |a: usize| {
        names
            .iter()
            .find(|(_, n)| *n == a)
            .map(|(s, _)| String::from_utf8_lossy(s).to_string())
            .unwrap_or_else(|| format!("p{}", a))
    };
    match solve(&f) {
        None => println!("NOT ENCODABLE"),
        Some((ans, t)) => {
            let verdict = match &ans {
                Answer::Sat(_) => "SAT",
                Answer::Unsat => "UNSAT",
                Answer::Unknown => "UNKNOWN",
            };
            println!(
                "{} vars={} clauses={} encode={:.3}s solve={:.3}s check={:.3}s",
                verdict,
                t.vars,
                t.clauses,
                t.encode_ns as f64 * 1e-9,
                t.solve_ns as f64 * 1e-9,
                t.check_ns as f64 * 1e-9
            );
            if verbose {
                if let Answer::Sat(trace) = ans {
                    for (k, s) in trace.iter().enumerate() {
                        let mut v: Vec<String> = s.iter().map(|a| name(*a)).collect();
                        v.sort();
                        println!("t={}: {{{}}}", k, v.join(", "));
                    }
                }
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 3 && args[1] == "--file" {
        let text = std::fs::read_to_string(&args[2]).expect("read file");
        for (i, line) in text.lines().filter(|l| !l.trim().is_empty()).enumerate() {
            print!("{} ", i + 1);
            run(line, false);
        }
    } else if args.len() == 2 {
        run(&args[1], true);
    } else {
        eprintln!("usage: mltl_sat FORMULA | mltl_sat --file FORMULAS.txt");
        std::process::exit(2);
    }
}
