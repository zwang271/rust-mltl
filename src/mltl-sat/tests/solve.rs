//! End-to-end runs with CaDiCaL (skipped when `cadical` is not installed).
use mltl_sat::solve::solve;
use mltl_sat::solve::Answer;

fn have_cadical() -> bool {
    std::process::Command::new(std::env::var("CADICAL").unwrap_or_else(|_| "cadical".into()))
        .arg("--version")
        .output()
        .is_ok()
}

fn answer(text: &str) -> &'static str {
    let (f, _) = mltl_parse::parse_numbered(text.as_bytes()).unwrap();
    match solve(&f).expect("encodable").0 {
        Answer::Sat(_) => "SAT",
        Answer::Unsat => "UNSAT",
        Answer::Unknown => "UNKNOWN",
    }
}

#[test]
fn small_formulas() {
    if !have_cadical() {
        eprintln!("cadical not found; skipping");
        return;
    }
    let cases = [
        ("G[0,3] (p0 | p1)", "SAT"),
        ("F[0,3] p0 & G[0,3] !p0", "UNSAT"),
        ("p0 U[1,3] p1 & G[0,4] !p1", "UNSAT"),
        ("p0 U[1,3] p1", "SAT"),
        ("p0 R[0,2] p1 & F[0,2] !p1 & G[0,2] !p0", "UNSAT"),
        ("true", "SAT"),
        ("false", "UNSAT"),
        ("p0 & !p0", "UNSAT"),
        // G[1,1] false is satisfiable only on short traces, so not at complen.
        ("G[1,1] false", "UNSAT"),
        ("F[2,5] (p0 & F[1,1] !p0)", "SAT"),
    ];
    for (text, want) in cases {
        assert_eq!(answer(text), want, "{}", text);
    }
}

#[test]
fn ill_formed_interval_is_rejected() {
    // The parser rejects a > b, so build the formula directly.
    use mltl_core::mltl::Mltl;
    let f = Mltl::Future(3, 1, Box::new(Mltl::Prop(0usize)));
    assert!(solve(&f).is_none());
}
