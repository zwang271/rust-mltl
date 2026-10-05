//! Runtime checks of the shared atom table (`Atoms`).
use mltl_core::mltl::Mltl;
use mltl_parse::{Atoms, ErrorKind};

fn names(steps: &[&[&str]]) -> Vec<Vec<Vec<u8>>> {
    steps.iter().map(|s| s.iter().map(|n| n.as_bytes().to_vec()).collect()).collect()
}

#[test]
fn shared_numbers() {
    let mut atoms = Atoms::new();
    let f = atoms.parse(b"a & p3").unwrap();
    assert!(matches!(f, Mltl::And(ref x, ref y) if matches!(**x, Mltl::Prop(4)) && matches!(**y, Mltl::Prop(3))));
    let g = atoms.parse(b"b | a | p1").unwrap();
    assert_eq!(atoms.print(&g), b"b | a | p1");
    assert_eq!(atoms.atom(&b"a".to_vec()), Some(4));
    assert_eq!(atoms.atom(&b"b".to_vec()), Some(5));
    assert_eq!(atoms.atom(&b"p3".to_vec()), Some(3));
    assert_eq!(atoms.atom(&b"c".to_vec()), None);
    // a `pN` at or above the first named number may clash: rejected
    let e = atoms.parse(b"p4").unwrap_err();
    assert!(matches!(e.kind, ErrorKind::NumberTaken));
    assert!(e.render(b"p4", "<input>").contains("clash"));
    // the failed parse added nothing
    assert_eq!(atoms.atom(&b"p4".to_vec()), None);
}

#[test]
fn pn_first_raises_the_floor() {
    let mut atoms = Atoms::new();
    atoms.parse(b"p0 & p9").unwrap();
    let f = atoms.parse(b"x").unwrap();
    assert!(matches!(f, Mltl::Prop(10)));
}

#[test]
fn traces() {
    let mut atoms = Atoms::new();
    atoms.parse(b"G[0,2] (req -> F[0,1] ack)").unwrap();
    let t = atoms.trace(&names(&[&["req"], &["ack", "req"], &[]])).unwrap();
    assert_eq!(t.len(), 3);
    assert!(t[0].contains(&0) && !t[0].contains(&1));
    assert!(t[1].contains(&0) && t[1].contains(&1));
    assert!(t[2].is_empty());
    assert_eq!(atoms.trace(&names(&[&["req"], &["typo"]])).unwrap_err(), (1, 0));
}

#[test]
fn print_round_trip() {
    let mut atoms = Atoms::new();
    for text in ["p2 & z ^ p0", "G[0,10] (request -> F[0,5] grant)", "x U[1,2] (y R[0,3] !x) | p1"] {
        let f = atoms.parse(text.as_bytes()).unwrap();
        let printed = atoms.print(&f);
        let g = atoms.parse(&printed).unwrap();
        assert!(mltl_core::mltl::eq_mltl(&f, &g), "{text}");
    }
}
