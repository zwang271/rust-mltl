//! `lrat_check FILE.cnf PROOF.lrat`: check a text LRAT proof with the
//! verified checker. Prints `VERIFIED UNSAT` or `NOT VERIFIED`.
use propositional::lrat::check_lrat;
use propositional::lrat_text::{parse_dimacs, parse_lrat};
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: lrat_check FILE.cnf PROOF.lrat");
        std::process::exit(2);
    }
    let cnf = parse_dimacs(&std::fs::read_to_string(&args[1]).expect("read cnf")).expect("parse cnf");
    let t0 = Instant::now();
    let steps = parse_lrat(&std::fs::read_to_string(&args[2]).expect("read proof")).expect("parse proof");
    let t1 = Instant::now();
    let ok = check_lrat(&cnf, &steps);
    let t2 = Instant::now();
    println!(
        "{} (steps {}, parse {:.3}s, check {:.3}s)",
        if ok { "VERIFIED UNSAT" } else { "NOT VERIFIED" },
        steps.len(),
        (t1 - t0).as_secs_f64(),
        (t2 - t1).as_secs_f64()
    );
    std::process::exit(if ok { 0 } else { 1 });
}
