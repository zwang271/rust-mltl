//! A short tour of the `mltl` crate, using one formula and one trace throughout:
//! read them, check the trace against the formula,
//! then run each verified algorithm on them and print what it gives.
//!
//! Run it with `cargo run` from this directory.
//! The dependency line is in `Cargo.toml`.

// `Box<dyn Error>` lets `?` pass on both the library's errors and file errors.
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // A context remembers the atom names you use, like `p` and `q`.
    // Read every formula and trace through the same context,
    // so that a name means the same thing in all of them.
    let mut cx = mltl::Context::new();

    // A formula: "at some step from 0 to 3, `p` and `q` are both true".
    // Reading fails on bad text, so `?` passes the error on.
    // Try it: uncomment the next line to see the error this formula gives.
    // cx.parse_formula("F[3,0] (p & q)")?;
    let formula = cx.parse_formula("F[0,3] (p & q)")?;

    // A trace: the atoms that are true at each step.
    // Here `p` is true at step 0, `q` at step 1, neither at step 2, and both at step 3.
    // Try it: uncomment the next line to see the error this trace gives.
    // cx.parse_trace("[{p}, {q}, {}, {p, q}, ]")?;
    let trace = cx.parse_trace("[{p}, {q}, {}, {p, q}]")?;

    // A trace can also be built in code, from the names that are true at each step.
    // (`vec!` lets the steps list different numbers of names.)
    let built = cx.trace([vec!["p"], vec!["q"], vec![], vec!["p", "q"]])?;
    assert_eq!(built, trace);

    // Or read from a file in R2U2's CSV format: a header naming the atoms,
    // then one row per step, with `1` for true and `0` for false.
    // `trace.csv`, next to `Cargo.toml`, holds the same trace again.
    let csv = std::fs::read_to_string("trace.csv")
        .map_err(|e| format!("can't read trace.csv ({e}); run from the example directory"))?;
    let from_file = cx.parse_csv(&csv)?;
    assert_eq!(from_file, trace);

    // Does the trace satisfy the formula?
    // `eval` is proved to agree with the definition of MLTL,
    // so this answer is guaranteed to be right.
    let satisfied = mltl::eval(&formula, &trace);

    // `cx.display` turns a formula or trace into text, using the names from the context.
    println!("evaluation:");
    println!("  formula:   {}", cx.display(&formula));
    println!("  trace:     {}", cx.display(&trace));
    println!("  satisfied: {}", satisfied);

    // Formula progression reads the trace one step at a time.
    // After each step, it gives the formula that the rest of the trace still has to satisfy.
    // `progress` is proved right: the rest of a trace satisfies the progressed formula
    // exactly when the whole trace satisfies the original one.
    // `true` or `false` means the answer is already settled, whatever comes next.
    // (`nnf` only rewrites the formula into an easier-to-read form with the same meaning.)
    println!("\nformula progression:");
    println!("  formula: {}", cx.display(&formula));
    println!("  trace:   {}", cx.display(&trace));
    for step in 0..trace.len() {
        let seen = &trace[..=step];
        let rest = mltl::progress(&formula, seen);
        println!("  after {}: {}", cx.display(seen), cx.display(&mltl::nnf(&rest)));
    }

    // Language partitioning splits the formula into pieces that never hold together.
    // You say how to cut each interval: one list of block lengths per `F`, `G`, `U` or `R`.
    // Here the interval [0,3] of `F` (4 steps) is cut into blocks of 1, 2 and 1 steps,
    // giving "`p & q` first happens at step 0", "... at step 1 or 2", and "... at step 3".
    // Proved: a trace satisfies the formula exactly when it satisfies one of the pieces,
    // and no trace satisfies two of them.
    // (`mltl::partition(&formula, 1, 1)` would cut every interval into 1-step blocks.)
    // The labels say when `p & q` first holds in each piece; they are ours, not the library's.
    println!("\nlanguage partitioning:");
    let splits = [[1, 2, 1]];
    println!("  formula: {}", cx.display(&formula));
    println!("  splits:  {splits:?}");
    let pieces = mltl::partition_with(&formula, splits, 1)?;
    let labels = ["holds immediately (step 0)", "holds in the middle (steps 1-2)", "holds at the end (step 3)"];
    for (label, piece) in labels.iter().zip(&pieces) {
        println!("  {:<33} {}", format!("{label}:"), cx.display(piece));
    }

    // WEST lists patterns that together describe every trace satisfying the formula.
    // There is one column per atom (here `p,q`) and the steps are separated by commas:
    // `1` means true, `0` false, and `s` either.
    // Proved: a long enough trace satisfies the formula exactly when it matches a line.
    // Ours matches the first line, `ss,ss,ss,11`.
    println!("\nWEST:");
    println!("  formula: {}", cx.display(&formula));
    for line in cx.west(&formula)?.lines() {
        println!("  {line}");
    }

    // R2U2 is a runtime monitor: it reads the trace as it happens, one step at a time,
    // and gives a verdict as soon as the answer is known.
    // A verdict `(value, t)` gives `value` for every step after the previous verdict, up to step `t`.
    // Proved: every verdict is right, and none comes later than it has to.
    // We give it a longer trace: ours, followed by six more steps.
    // At step 3, `p & q` is true: the verdict `(true, 3)` settles steps 0 to 3 at once.
    // Step 4 is only settled at step 7, by `(false, 4)`: the monitor has to see steps 4 to 7
    // without `p & q` before it knows the answer is false. It never has to wait more than 3 steps.
    let long_trace = cx.parse_trace("[{p}, {q}, {}, {p, q}, {}, {}, {}, {}, {}, {p, q}]")?;
    println!("\nR2U2 monitor:");
    println!("  formula: {}", cx.display(&formula));
    println!("  trace:   {}", cx.display(&long_trace));
    let mut monitor = mltl::Monitor::new(&formula)?;
    println!("  step  reads   new verdicts");
    for (step, state) in long_trace.iter().enumerate() {
        let before = monitor.verdicts().len();
        monitor.step(state)?;
        let new: Vec<String> = monitor.verdicts()[before..].iter().map(|v| format!("({}, {})", v.val, v.time)).collect();
        let reads = cx.display(&long_trace[step..=step]).to_string();
        let reads = reads.trim_matches(['[', ']']);
        println!("  {step:>4}  {reads:<7} {}", if new.is_empty() { "-".to_string() } else { new.join(", ") });
    }

    // SAT asks whether any trace at all satisfies a formula, using the SAT solver CaDiCaL.
    // The solver isn't trusted: verified code checks each answer before it is returned.
    // Our formula can be satisfied; adding "`p` is never true" makes it impossible.
    println!("\nSAT:");
    let impossible = cx.parse_formula("F[0,3] (p & q) & G[0,3] !p")?;
    for f in [&formula, &impossible] {
        match mltl::sat(f) {
            Ok(mltl::Sat::Sat(example)) => println!("  {}: satisfied by {}", cx.display(f), cx.display(&example)),
            Ok(mltl::Sat::Unsat) => println!("  {}: unsatisfiable", cx.display(f)),
            Ok(mltl::Sat::Unknown) => println!("  {}: the solver's answer could not be checked", cx.display(f)),
            // Without CaDiCaL installed, say so and carry on.
            Err(e @ mltl::Error::SolverMissing) => {
                println!("  skipped:\n{e}");
                break;
            }
            Err(e) => return Err(e.into()),
        }
    }

    Ok(())
}
