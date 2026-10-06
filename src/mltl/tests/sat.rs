//! The SAT wrapper end to end (needs CaDiCaL; skipped without it).
use mltl::{Context, Sat};

fn have_cadical() -> bool {
    let bin = std::env::var("CADICAL").unwrap_or_else(|_| "cadical".to_string());
    std::process::Command::new(bin).arg("--version").output().is_ok()
}

#[test]
fn sat_and_unsat() {
    if !have_cadical() {
        eprintln!("cadical not found; skipped");
        return;
    }
    let mut cx = Context::new();
    let f = cx.parse_formula("F[0,3] (request & G[1,2] !grant)").unwrap();
    match mltl::sat(&f).unwrap() {
        Sat::Sat(t) => assert!(mltl::eval(&f, &t)),
        other => panic!("expected Sat, got {other:?}"),
    }
    let g = cx.parse_formula("request & !request").unwrap();
    assert_eq!(mltl::sat(&g).unwrap(), Sat::Unsat);
    let h = cx.parse_formula("G[0,4] grant & F[2,3] !grant").unwrap();
    assert_eq!(mltl::sat(&h).unwrap(), Sat::Unsat);
}

#[test]
fn monitor_step_by_step() {
    let mut cx = Context::new();
    let f = cx.parse_formula("request -> F[0,2] grant").unwrap();
    let t = cx.parse_trace("[{request}, {}, {grant}, {}, {}]").unwrap();
    let mut m = mltl::Monitor::new(&f).unwrap();
    for s in &t {
        m.step(s).unwrap();
    }
    assert_eq!(m.verdicts(), mltl::monitor(&f, &t).unwrap().as_slice());
    for k in 0..t.len() {
        if let Some(v) = m.value_at(k) {
            assert_eq!(v, mltl::eval(&f, &t[k..]), "step {k}");
        }
    }
    assert_eq!(m.value_at(0), Some(true));
}

#[test]
fn bad_intervals_rejected() {
    use mltl::Mltl;
    let f = Mltl::Future(3, 1, Box::new(Mltl::Prop(0)));
    assert!(matches!(mltl::monitor(&f, &[]), Err(mltl::Error::BadInterval)));
    assert!(matches!(Context::new().west(&f), Err(mltl::Error::BadInterval)));
    assert!(matches!(mltl::sat(&f), Err(mltl::Error::BadInterval)));
}
