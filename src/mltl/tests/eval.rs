//! `mltl::eval` packs the trace into bits first; check it against the
//! set-based evaluator on edge cases.
use mltl::Context;

#[test]
fn eval_matches_set_evaluator() {
    let mut cx = Context::new();
    let formulas = ["F[0,3] (p & q)", "G[0,2] (p | r)", "!p U[1,4] q", "true", "G[0,0] r"];
    let traces = ["[]", "[{}]", "[{p}, {q}, {}, {p, q}]", "[{x}, {p, x}, {q}]", "[{q}, {q}, {q}, {q}, {q}, {q}]"];
    let formulas: Vec<_> = formulas.iter().map(|f| cx.parse_formula(f).unwrap()).collect();
    for t in traces {
        let t = cx.parse_trace(t).unwrap();
        for f in &formulas {
            assert_eq!(mltl::eval(f, &t), mltl::mltl_eval::mltl_eval_bottom_up(f, &t), "{} on {}", cx.display(f), cx.display(&t));
        }
    }
}
