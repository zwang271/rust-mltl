//! Runtime tests of the verified LRAT checker and model check. Proof files
//! in `tests/data` were produced by CaDiCaL 3.0.1 (`--lrat --binary=false`).
use propositional::dimacs::check_model;
use propositional::lrat::{check_lrat, LratStep};
use propositional::lrat_text::{parse_dimacs, parse_lrat};

fn add(id: u64, clause: &[i32], hints: &[i64]) -> LratStep {
    LratStep::Add { id, clause: clause.to_vec(), hints: hints.to_vec() }
}

/// `(x∨y)(x∨¬y)(¬x∨y)(¬x∨¬y)`
fn four() -> Vec<Vec<i32>> {
    vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]]
}

#[test]
fn small_refutation() {
    let proof = vec![add(5, &[1], &[1, 2]), add(6, &[], &[5, 3, 4])];
    assert!(check_lrat(&four(), &proof));
}

#[test]
fn wrong_hints_rejected() {
    // Hint 3 does not become unit under ¬x.
    assert!(!check_lrat(&four(), &vec![add(5, &[1], &[3, 2]), add(6, &[], &[5, 3, 4])]));
    // Unknown clause id.
    assert!(!check_lrat(&four(), &vec![add(5, &[1], &[1, 9])]));
    // RAT-style negative hint is unsupported.
    assert!(!check_lrat(&four(), &vec![add(5, &[1], &[-1, 2])]));
    // No empty clause: not a refutation.
    assert!(!check_lrat(&four(), &vec![add(5, &[1], &[1, 2])]));
}

#[test]
fn deleted_clause_cannot_be_used() {
    let proof = vec![LratStep::Delete { ids: vec![2] }, add(5, &[1], &[1, 2])];
    assert!(!check_lrat(&four(), &proof));
}

#[test]
fn tautology_is_accepted_without_hints() {
    // A tautology is entailed; adding it does not refute anything.
    let proof = vec![add(5, &[1, -1], &[])];
    assert!(!check_lrat(&four(), &proof));
    let proof = vec![add(5, &[1, -1], &[]), add(6, &[1], &[1, 2]), add(7, &[], &[6, 3, 4])];
    assert!(check_lrat(&four(), &proof));
}

#[test]
fn satisfiable_formula_never_refuted() {
    // Drop clause 4: satisfiable (x = y = true). Any proof must fail.
    let mut f = four();
    f[3] = vec![1, -1];
    assert!(!check_lrat(&f, &vec![add(5, &[1], &[1, 2]), add(6, &[], &[5, 3, 4])]));
}

#[test]
fn cadical_pigeonhole_proof() {
    let cnf = parse_dimacs(include_str!("data/php5.cnf")).unwrap();
    let proof = parse_lrat(include_str!("data/php5.lrat")).unwrap();
    assert!(check_lrat(&cnf, &proof));
    // Pigeon 0 may sit nowhere: satisfiable, so the proof must be rejected.
    let mut weak = cnf.clone();
    weak[0] = vec![1, -1];
    assert!(!check_lrat(&weak, &proof));
}

#[test]
fn cadical_model() {
    let cnf = parse_dimacs(include_str!("data/r3_4.cnf")).unwrap();
    let mut model = vec![false; 151];
    for line in include_str!("data/r3_4.model").lines().filter(|l| l.starts_with('v')) {
        for t in line[1..].split_whitespace() {
            let l: i32 = t.parse().unwrap();
            if l > 0 {
                model[l as usize] = true;
            }
        }
    }
    assert!(check_model(&cnf, &model));
    model[1..].iter_mut().for_each(|b| *b = !*b);
    assert!(!check_model(&cnf, &model));
}
