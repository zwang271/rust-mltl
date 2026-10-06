//! Runtime checks of the verified parser against the examples in GRAMMAR.md §4.
use mltl_core::mltl::Mltl;
use mltl_parse::parse_str;

/// Fully parenthesised rendering, for comparing against expected trees.
fn show(f: &Mltl<Vec<u8>>) -> String {
    match f {
        Mltl::True => "True".into(),
        Mltl::False => "False".into(),
        Mltl::Prop(n) => String::from_utf8(n.clone()).unwrap(),
        Mltl::Not(g) => format!("Not({})", show(g)),
        Mltl::And(g, h) => format!("And({}, {})", show(g), show(h)),
        Mltl::Or(g, h) => format!("Or({}, {})", show(g), show(h)),
        Mltl::Future(a, b, g) => format!("F[{a},{b}]({})", show(g)),
        Mltl::Global(a, b, g) => format!("G[{a},{b}]({})", show(g)),
        Mltl::Until(g, a, b, h) => format!("U[{a},{b}]({}, {})", show(g), show(h)),
        Mltl::Release(g, a, b, h) => format!("R[{a},{b}]({}, {})", show(g), show(h)),
    }
}

fn p(s: &str) -> Option<String> {
    parse_str(s).ok().map(|f| show(&f))
}

#[test]
fn accepted() {
    let cases = [
        ("p & q | r", "Or(And(p, q), r)"),
        ("p | q & r", "Or(p, And(q, r))"),
        ("p & q & r", "And(And(p, q), r)"),
        ("p ^ q", "Or(And(p, Not(q)), And(Not(p), q))"),
        ("!p & q", "And(Not(p), q)"),
        ("!(p & q)", "Not(And(p, q))"),
        ("F[0,3] p & q", "And(F[0,3](p), q)"),
        ("F[0,3] (p & q)", "F[0,3](And(p, q))"),
        ("F[0,2] !p", "F[0,2](Not(p))"),
        ("p U[0,2] q & r", "And(U[0,2](p, q), r)"),
        ("!p U[1,4] G[0,2] q", "U[1,4](Not(p), G[0,2](q))"),
        ("F[0,1] p U[0,2] q", "U[0,2](F[0,1](p), q)"),
        ("p -> q", "Or(Not(p), q)"),
        ("(p -> q) -> r", "Or(Not(Or(Not(p), q)), r)"),
        ("p <-> q", "And(Or(Not(p), q), Or(Not(q), p))"),
        ("G[0,2] t", "G[0,2](True)"),
        ("tt & ff | f", "Or(And(True, False), False)"),
        ("G[0,10] (request -> F[0,5] grant) & !fault",
         "And(G[0,10](Or(Not(request), F[0,5](grant))), Not(fault))"),
        ("  Fuel_low\tU[ 0 , 3 ]\nrefuel ", "U[0,3](Fuel_low, refuel)"),
        ("F[0,18446744073709551615] p", "F[0,18446744073709551615](p)"),
    ];
    for (text, expected) in cases {
        assert_eq!(p(text).as_deref(), Some(expected), "parsing {text:?}");
    }
}

#[test]
fn rejected() {
    for text in [
        "", "p &", "p U[0,2] q U[0,3] r", "p -> q -> r", "p -> q <-> r", "G[3,1] p",
        "F[0,18446744073709551616] p", "F p", "F[0,3]", "F & q", "(p", "p)", "~p", "p = q",
        "p q", "pUq U", "é", "p - q", "p < q",
    ] {
        assert_eq!(p(text), None, "{text:?} should be rejected");
    }
}

use mltl_parse::parse_numbered;
use mltl_parse::printer::print;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: u64) -> usize { (self.next() % n) as usize }
}

fn random_formula(r: &mut Rng, depth: usize) -> Mltl<Vec<u8>> {
    const NAMES: [&str; 6] = ["p", "q", "req", "Fuel_low", "p0", "p12"];
    if depth == 0 || r.below(4) == 0 {
        return match r.below(6) {
            0 => Mltl::True,
            1 => Mltl::False,
            _ => Mltl::Prop(NAMES[r.below(6)].as_bytes().to_vec()),
        };
    }
    let a = r.below(5);
    let b = a + r.below(5);
    let mut sub = |r: &mut Rng| Box::new(random_formula(r, depth - 1));
    match r.below(8) {
        0 => Mltl::Not(sub(r)),
        1 => Mltl::And(sub(r), sub(r)),
        2 => Mltl::Or(sub(r), sub(r)),
        3 => Mltl::Future(a, b, sub(r)),
        4 => Mltl::Global(a, b, sub(r)),
        5 => Mltl::Until(sub(r), a, b, sub(r)),
        6 => Mltl::Release(sub(r), a, b, sub(r)),
        _ => Mltl::And(Box::new(Mltl::And(sub(r), sub(r))), sub(r)),
    }
}

/// Printing then parsing gives back the same formula (the proved round trip),
/// and the printed text uses the minimal-parentheses style.
#[test]
fn round_trip_random() {
    let mut r = Rng(0x243F6A8885A308D3);
    for _ in 0..20_000 {
        let f = random_formula(&mut r, 5);
        let text = print(&f);
        let back = mltl_parse::parse(&text).expect("printed text must parse");
        assert_eq!(show(&back), show(&f), "text {:?}", String::from_utf8_lossy(&text));
    }
    let f = parse_str("(p & q) & r | !(a U[0,2] b)").unwrap();
    assert_eq!(String::from_utf8(print(&f)).unwrap(), "p & q & r | !(a U[0,2] b)");
}

/// GRAMMAR.md §5: `p2` is atom 2, then `request` 3 and `grant` 4.
#[test]
fn numbering_example() {
    let (g, table) = parse_numbered(b"request & p2 | grant & request").unwrap();
    let names: Vec<(String, usize)> = table.iter().map(|(n, i)| (String::from_utf8(n.clone()).unwrap(), *i)).collect();
    assert_eq!(names, vec![("request".to_string(), 3), ("grant".to_string(), 4)]);
    match g {
        Mltl::Or(l, r) => match (*l, *r) {
            (Mltl::And(a, b), Mltl::And(c, d)) => {
                assert!(matches!((*a, *b, *c, *d), (Mltl::Prop(3), Mltl::Prop(2), Mltl::Prop(4), Mltl::Prop(3))));
            }
            _ => panic!("shape"),
        },
        _ => panic!("shape"),
    }
    assert!(parse_numbered(b"p18446744073709551615").is_err());
}
