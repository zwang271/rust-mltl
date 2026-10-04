//! Error reports: what they say for typical mistakes, and that every
//! rejected text gets a report.
use mltl_parse::{parse, parse_str};

fn report(text: &str) -> String {
    match parse_str(text) {
        Ok(_) => panic!("{text:?} should be rejected"),
        Err(e) => e.render(text.as_bytes(), "<input>"),
    }
}

#[test]
fn show_reports() {
    // Run with `--nocapture` to see every report.
    for text in [
        "p U[0,2] q U[0,3] r", "p0U[0,2] p1", "F[5,2] p", "p & (q | )", "(p & q", "p & q)",
        "G p", "G[0 2] p", "p q", "", "~p", "p -> q <-> r", "()", "& p", "F[0,99999999999999999999] p",
        "a & b &\n  (c U[0,3] d", "p ∧ q",
    ] {
        println!("{}\n", report(text));
    }
}

#[test]
fn chain() {
    assert_eq!(report("p U[0,2] q U[0,3] r"), "\
error: `U` and `R` can't be chained without parentheses
 --> <input>:1:12
  |
1 | p U[0,2] q U[0,3] r
  |   -        ^ second `U`
  |   |
  |   first `U`
  |
  = help: say which one you mean: `(p U[0,2] q) U[0,3] r` or `p U[0,2] (q U[0,3] r)`
");
}

#[test]
fn glued() {
    assert_eq!(report("p0U[0,2] p1"), "\
error: expected an operator, found `[`
 --> <input>:1:4
  |
1 | p0U[0,2] p1
  | ---^
  | |
  | `p0U` is read as one name
  |
  = help: add a space: `p0 U[0,2] p1`
");
}

#[test]
fn bad_interval() {
    assert_eq!(report("F[5,2] p"), "\
error: interval ends before it starts
 --> <input>:1:3
  |
1 | F[5,2] p
  |   ^^^ 5 is greater than 2
  |
  = note: an interval `[a,b]` needs a ≤ b
");
}

#[test]
fn unclosed() {
    assert_eq!(report("(p & q"), "\
error: unclosed `(`
 --> <input>:1:7
  |
1 | (p & q
  | -     ^ expected `)`
  | |
  | this `(` is never closed
");
}

#[test]
fn second_line() {
    let r = report("a & b &\n  (c U[0,3] d");
    assert!(r.contains(" --> <input>:2:14\n"), "{r}");
    assert!(r.contains("2 |   (c U[0,3] d\n"), "{r}");
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: u64) -> usize { (self.next() % n) as usize }
}

/// Random texts built from formula pieces: every rejected one gets a report
/// with a title, and the reported position is inside the text.
#[test]
fn every_rejection_is_reported() {
    const PIECES: [&str; 24] = [
        "p", "q", "p0U", "true", "f", "(", ")", "!", "&", "|", "^", "->", "<->", "F", "G", "U", "R",
        "[", "]", ",", "0", "3", "[0,2]", " ",
    ];
    let mut r = Rng(0x9E3779B97F4A7C15);
    let (mut rejected, mut accepted) = (0, 0);
    for _ in 0..200_000 {
        let n = 1 + r.below(10);
        let sep = if r.below(2) == 0 { " " } else { "" };
        let text: String = (0..n).map(|_| PIECES[r.below(PIECES.len() as u64)]).collect::<Vec<_>>().join(sep);
        match parse(text.as_bytes()) {
            Ok(_) => accepted += 1,
            Err(e) => {
                rejected += 1;
                assert!(e.at.end <= text.len());
                let out = e.render(text.as_bytes(), "<input>");
                assert!(out.starts_with("error: ") && out.len() > 8, "{text:?}: {out}");
            }
        }
    }
    assert!(accepted > 1000 && rejected > 1000, "{accepted} accepted, {rejected} rejected");
}
