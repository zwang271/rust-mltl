//! Runtime checks of the trace readers and printer against GRAMMAR.md §6.
use std::collections::HashSet;
use mltl_parse::{csv::parse_csv, trace::{parse_trace, print_trace}, Atoms, ErrorKind};

fn steps(text: &str) -> Vec<Vec<String>> {
    parse_trace(text.as_bytes()).unwrap().into_iter()
        .map(|s| s.into_iter().map(|n| String::from_utf8(n).unwrap()).collect()).collect()
}

fn csv_steps(text: &str) -> Vec<Vec<String>> {
    parse_csv(text.as_bytes()).unwrap().into_iter()
        .map(|s| s.into_iter().map(|n| String::from_utf8(n).unwrap()).collect()).collect()
}

fn title(text: &str) -> String {
    let e = parse_trace(text.as_bytes()).unwrap_err();
    e.title(text.as_bytes())
}

fn csv_title(text: &str) -> String {
    let e = parse_csv(text.as_bytes()).unwrap_err();
    e.title(text.as_bytes())
}

#[test]
fn sets_accepted() {
    assert_eq!(steps("[{request}, {grant, ok}, {}]"), [vec!["request"], vec!["grant", "ok"], vec![]]);
    assert_eq!(steps("[]"), Vec::<Vec<String>>::new());
    assert_eq!(steps("[{}]"), [Vec::<String>::new()]);
    assert_eq!(steps("[{a, a}]"), [vec!["a", "a"]]);
    assert_eq!(steps(" [\n  {p3},\n  {}\n]\n"), [vec!["p3"], vec![]]);
}

#[test]
fn sets_rejected() {
    for text in ["", "{a}, {b}", "[{a},]", "[{a,}]", "[{a b}]", "[{!a}]", "[{1}]", "[{true}]", "[", "[{a}", "[{a}] x", "[{a}{b}]", "[,]", "[{a}, {b}"] {
        assert!(parse_trace(text.as_bytes()).is_err(), "{text:?} should be rejected");
    }
    assert_eq!(title("[{a},]"), "trailing comma");
    assert_eq!(title("[{a,}]"), "trailing comma");
    assert_eq!(title("{a}"), "expected `[` to start a trace, found `{`");
    assert_eq!(title("[{a b}]"), "expected `,` or `}`, found `b`");
    assert_eq!(title("[{a}{b}]"), "expected `,` or `]`, found `{`");
    assert_eq!(title("[{a}] x"), "unexpected `x` after the end of the trace");
    assert_eq!(title("[{a}"), "expected `,` or `]`, found end of input");
    let e = parse_trace(b"[{a}] x").unwrap_err();
    assert_eq!((e.at.start, e.at.end), (6, 7));
}

#[test]
fn print_round_trip() {
    for text in ["[{request}, {grant, ok}, {}]", "[]", "[{}]", "[{a}, {}, {b, c, d}]"] {
        let s = parse_trace(text.as_bytes()).unwrap();
        let printed = print_trace(&s);
        assert_eq!(String::from_utf8(printed.clone()).unwrap(), text);
        assert_eq!(parse_trace(&printed).unwrap(), s);
    }
}

#[test]
fn csv_accepted() {
    assert_eq!(csv_steps("# request,grant\n1,0\n0,1\n0,0\n"), [vec!["request"], vec!["grant"], vec![]]);
    assert_eq!(csv_steps("\n  # a , b \r\n\n 1 , 1\r\n\t0,1"), [vec!["a", "b"], vec!["b"]]);
    assert_eq!(csv_steps("# a"), Vec::<Vec<String>>::new());
    assert_eq!(csv_steps("#b0,b1\n0,0\n1,0\n0,1\n"), [vec![], vec!["b0"], vec!["b1"]]);
}

#[test]
fn csv_rejected() {
    assert_eq!(csv_title(""), "empty CSV trace: no header line");
    assert_eq!(csv_title(" \n\t\n"), "empty CSV trace: no header line");
    assert_eq!(csv_title("a,b\n1,0"), "bad CSV header");
    assert_eq!(csv_title("#\n"), "bad CSV header");
    assert_eq!(csv_title("# a,,b\n"), "bad CSV header");
    assert_eq!(csv_title("# a,true\n"), "bad CSV header");
    assert_eq!(csv_title("# a,b,a\n"), "an atom is named twice in the CSV header");
    assert_eq!(csv_title("# a,b\n1\n"), "row has 1 value, the header names 2 atoms");
    assert_eq!(csv_title("# a,b\n1,0,1\n"), "row has 3 values, the header names 2 atoms");
    assert_eq!(csv_title("# a,b\n1,2\n"), "CSV values must be `0` or `1`");
    assert_eq!(csv_title("# a,b\n1,00\n"), "CSV values must be `0` or `1`");
    let text = b"# a,b\n1,0\n1,x\n";
    let e = parse_csv(text).unwrap_err();
    assert_eq!((e.at.start, e.at.end), (10, 13));
    assert!(matches!(e.kind, ErrorKind::Csv(_)));
}

#[test]
fn atoms_traces() {
    let mut atoms = Atoms::new();
    atoms.parse(b"G[0,2] (req -> F[0,1] ack)").unwrap();
    let t = atoms.parse_trace(b"[{req}, {ack, req}, {extra}]").unwrap();
    assert_eq!(t[0], HashSet::from([0]));
    assert_eq!(t[1], HashSet::from([0, 1]));
    assert_eq!(atoms.atom(&b"extra".to_vec()), Some(2));
    assert_eq!(t[2], HashSet::from([2]));
    let c = atoms.parse_csv(b"# ack,req\n0,1\n1,1\n").unwrap();
    assert_eq!(c, t[..2].to_vec());
    assert_eq!(atoms.print_trace(&t, 3), b"[{req}, {req, ack}, {extra}]");
    // only atoms below the bound are printed
    assert_eq!(atoms.print_trace(&t, 1), b"[{req}, {req}, {}]");
    // unnamed numbers print as `pN`
    assert_eq!(atoms.print_trace(&vec![HashSet::from([7])], 8), b"[{p7}]");
    // a `pN` that may clash with a name is a numbering error
    let e = atoms.parse_trace(b"[{p9}]").unwrap_err();
    assert!(matches!(e.kind, ErrorKind::NumberTaken));
}

#[test]
fn formulas_still_reject_braces() {
    assert!(mltl_parse::parse(b"{p}").is_err());
    assert!(mltl_parse::parse(b"p & {q}").is_err());
}
