//! Cargo-style error reports for [`ParseError`].
//!
//! Plain Rust, not verified: this only words and lays out an error for
//! people. Which texts are rejected, and where the parser stopped, come from
//! the verified lexer and parser (`error.rs`); this file re-runs the
//! verified lexer to see the tokens around that spot.
//!
//! ```text
//! error: `U` and `R` can't be chained without parentheses
//!  --> <input>:1:12
//!   |
//! 1 | p U[0,2] q U[0,3] r
//!   |   -        ^ second `U`
//!   |   |
//!   |   first `U`
//!   |
//!   = help: say which one you mean: `(p U[0,2] q) U[0,3] r` or `p U[0,2] (q U[0,3] r)`
//! ```
use std::fmt;
use crate::error::{ErrorKind, ParseError};
use crate::lexer::{lex, Span, Token};
use crate::parser::Expected;

/// One underlined part of the text.
struct Label {
    start: usize,
    end: usize,
    primary: bool,
    text: String,
}

/// An error, ready to print: title, underlined parts, notes and help lines.
struct Diagnostic {
    title: String,
    labels: Vec<Label>,
    notes: Vec<String>,
}

fn primary(start: usize, end: usize, text: impl Into<String>) -> Label {
    Label { start, end, primary: true, text: text.into() }
}

fn secondary(start: usize, end: usize, text: impl Into<String>) -> Label {
    Label { start, end, primary: false, text: text.into() }
}

fn slice(src: &[u8], start: usize, end: usize) -> String {
    let end = end.min(src.len());
    let start = start.min(end);
    String::from_utf8_lossy(&src[start..end]).into_owned()
}

/// The tokens of `src` and their positions, from the verified lexer (empty
/// if `src` does not split into tokens).
struct Tokens {
    ts: Vec<Token<Vec<u8>>>,
    sp: Vec<Span>,
    n: usize,
}

impl Tokens {
    fn new(src: &[u8]) -> Tokens {
        let mut sp = Vec::new();
        let mut bad = Span { start: 0, end: 0 };
        let ts = lex(src, &mut sp, &mut bad).unwrap_or_default();
        if ts.is_empty() {
            sp.clear();
        }
        Tokens { ts, sp, n: src.len() }
    }
    fn len(&self) -> usize {
        self.ts.len()
    }
    /// The token starting at byte `pos` (`len()` for the end).
    fn index(&self, pos: usize) -> usize {
        self.sp.iter().position(|s| s.start == pos).unwrap_or(self.ts.len())
    }
    fn start(&self, k: usize) -> usize {
        self.sp.get(k).map_or(self.n, |s| s.start)
    }
    fn end(&self, k: usize) -> usize {
        self.sp.get(k).map_or(self.n, |s| s.end)
    }
    fn tok(&self, k: usize) -> Option<&Token<Vec<u8>>> {
        self.ts.get(k)
    }
    fn is(&self, k: usize, f: fn(&Token<Vec<u8>>) -> bool) -> bool {
        self.tok(k).is_some_and(f)
    }
}

fn is_ur(t: &Token<Vec<u8>>) -> bool {
    matches!(t, Token::KwU | Token::KwR)
}
fn is_imp(t: &Token<Vec<u8>>) -> bool {
    matches!(t, Token::Implies | Token::Iff)
}
fn is_bool_op(t: &Token<Vec<u8>>) -> bool {
    matches!(t, Token::And | Token::Or | Token::Xor | Token::Implies | Token::Iff)
}

/// Scanning from token `k` in direction `step`, the first token at the same
/// parenthesis depth for which `stop` holds, or the token just past the
/// enclosing group (an unmatched bracket or the end).
fn scan(t: &Tokens, k: usize, back: bool, stop: fn(&Token<Vec<u8>>) -> bool) -> Option<usize> {
    let mut depth = 0i64;
    let mut i = k as i64;
    while i >= 0 && (i as usize) < t.len() {
        let tok = t.tok(i as usize).unwrap();
        let (open, close) = if back { (matches!(tok, Token::RParen), matches!(tok, Token::LParen)) }
                            else { (matches!(tok, Token::LParen), matches!(tok, Token::RParen)) };
        if close {
            if depth == 0 { return None; }
            depth -= 1;
        } else if open {
            depth += 1;
        } else if depth == 0 && stop(tok) {
            return Some(i as usize);
        }
        i += if back { -1 } else { 1 };
    }
    None
}

/// The first token of the operand group that ends just before token `k`
/// (scanning back over a unary/temporal operand or a whole `->` side).
fn group_start(t: &Tokens, k: usize, stop: fn(&Token<Vec<u8>>) -> bool) -> usize {
    if k == 0 {
        return 0;
    }
    let mut depth = 0i64;
    let mut i = k as i64 - 1;
    while i >= 0 {
        match t.tok(i as usize).unwrap() {
            Token::RParen => depth += 1,
            Token::LParen if depth == 0 => return i as usize + 1,
            Token::LParen => depth -= 1,
            tok if depth == 0 && stop(tok) => return i as usize + 1,
            _ => {}
        }
        i -= 1;
    }
    0
}

/// The end (byte) of the operand group starting at token `k`.
fn group_end(t: &Tokens, k: usize, stop: fn(&Token<Vec<u8>>) -> bool) -> usize {
    let mut depth = 0i64;
    let mut i = k;
    let mut last = None;
    while i < t.len() {
        match t.tok(i).unwrap() {
            Token::LParen => depth += 1,
            Token::RParen if depth == 0 => break,
            Token::RParen => depth -= 1,
            tok if depth == 0 && stop(tok) => break,
            _ => {}
        }
        last = Some(i);
        i += 1;
    }
    last.map_or(t.start(k), |l| t.end(l))
}

/// How a token is named in a message: `` `&` ``, or "end of input".
fn shown(src: &[u8], t: &Tokens, k: usize) -> String {
    if k >= t.len() {
        "end of input".to_string()
    } else {
        format!("`{}`", slice(src, t.start(k), t.end(k)))
    }
}

fn is_binary(tok: &str) -> bool {
    matches!(tok, "&" | "|" | "^" | "->" | "<->" | "U" | "R")
}

fn interval_example(op: &str) -> &'static str {
    match op {
        "U" => "`p U[0,5] q`",
        "R" => "`p R[0,5] q`",
        "F" => "`F[0,5] p`",
        _ => "`G[0,5] p`",
    }
}

fn parses(text: &str) -> bool {
    crate::parse(text.as_bytes()).is_ok()
}

/// A complete formula ends before token `k`, and token `k` cannot continue
/// it. `open` is the unclosed `(`, if inside one.
fn after_formula(src: &[u8], t: &Tokens, k: usize, open: Option<usize>, d: &mut Diagnostic) {
    let (ks, ke) = (t.start(k), t.end(k));
    // `p0U[0,2]`: longest match made `p0U` one name.
    if k > 0 && t.is(k, |x| matches!(x, Token::LBrack)) && t.is(k - 1, |x| matches!(x, Token::Name(_))) {
        let (ns, ne) = (t.start(k - 1), t.end(k - 1));
        let name = slice(src, ns, ne);
        if ne == ks && name.len() >= 2 && (name.ends_with('U') || name.ends_with('R')) {
            let (head, op) = name.split_at(name.len() - 1);
            d.title = "expected an operator, found `[`".to_string();
            d.labels.push(primary(ks, ke, ""));
            d.labels.push(secondary(ns, ne, format!("`{name}` is read as one name")));
            let fixed = format!("{}{head} {op}{}", slice(src, 0, ns), slice(src, ne, src.len()));
            d.notes.push(format!("help: add a space: `{}`", fixed.trim()));
            return;
        }
    }
    // Two `U`/`R`, or two `->`/`<->`, without parentheses.
    let chain: Option<(fn(&Token<Vec<u8>>) -> bool, fn(&Token<Vec<u8>>) -> bool, usize)> =
        if t.is(k, is_ur) { Some((is_ur, is_bool_op, 6)) }
        else if t.is(k, is_imp) { Some((is_imp, |_| false, 1)) }
        else { None };
    if let Some((same, outer, width)) = chain {
        if let Some(first) = k.checked_sub(1).and_then(|j| scan(t, j, true, same)) {
            let a = slice(src, t.start(first), t.end(first));
            let b = slice(src, ks, ke);
            d.title = if t.is(first, is_ur) {
                "`U` and `R` can't be chained without parentheses".to_string()
            } else {
                "`->` and `<->` can't be chained without parentheses".to_string()
            };
            let (la, lb) = if a == b { (format!("first `{a}`"), format!("second `{b}`")) }
                           else { (format!("`{a}`"), format!("`{b}`")) };
            d.labels.push(secondary(t.start(first), t.end(first), la));
            d.labels.push(primary(ks, ke, lb));
            let stop_right: fn(&Token<Vec<u8>>) -> bool = if width == 6 { |x| is_bool_op(x) || is_ur(x) } else { is_imp };
            let left = t.start(group_start(t, first, outer));
            let mid_start = t.start(first + width);
            let mid_end = t.end(k - 1);
            let right = group_end(t, k + width, stop_right);
            let one = format!("({}){}", slice(src, left, mid_end), slice(src, mid_end, right));
            let two = format!("{}({})", slice(src, left, mid_start), slice(src, mid_start, right));
            if parses(&one) && parses(&two) {
                d.notes.push(format!("help: say which one you mean: `{one}` or `{two}`"));
            } else {
                d.notes.push("help: add parentheses to say which one applies first".to_string());
            }
            return;
        }
    }
    let f = shown(src, t, k);
    match open {
        None if t.is(k, |x| matches!(x, Token::RParen)) => {
            d.title = "unexpected `)`".to_string();
            d.labels.push(primary(ks, ke, "no `(` to close"));
            return;
        }
        Some(o) if k >= t.len() => {
            d.title = "unclosed `(`".to_string();
            d.labels.push(primary(ks, ke, "expected `)`"));
            d.labels.push(secondary(t.start(o), t.end(o), "this `(` is never closed"));
            return;
        }
        Some(o) => {
            d.title = format!("expected an operator or `)`, found {f}");
            d.labels.push(primary(ks, ke, "expected an operator or `)` here"));
            d.labels.push(secondary(t.start(o), t.end(o), "inside this `(`"));
        }
        None => {
            d.title = format!("expected an operator, found {f}");
            d.labels.push(primary(ks, ke, "expected an operator here"));
        }
    }
    let ft = slice(src, ks, ke);
    if k < t.len() && ft != "]" && ft != "," && ft != "[" {
        d.notes.push("help: two formulas need an operator between them, e.g. `p & q`".to_string());
    }
}

impl ParseError {
    fn diagnostic(&self, src: &[u8]) -> Diagnostic {
        let mut d = Diagnostic { title: String::new(), labels: Vec::new(), notes: Vec::new() };
        let at = &self.at;
        match &self.kind {
            ErrorKind::UnknownChar => {
                // Extend to the whole UTF-8 character.
                let mut end = at.end;
                while end < src.len() && (src[end] & 0xC0) == 0x80 {
                    end += 1;
                }
                let ch = slice(src, at.start, end);
                d.title = format!("unknown character `{ch}`");
                d.labels.push(primary(at.start, end, "not part of MLTL syntax"));
                let hint = match ch.as_str() {
                    "~" | "¬" => Some("negation is written `!`"),
                    "∧" => Some("conjunction is written `&`"),
                    "∨" => Some("disjunction is written `|`"),
                    "→" | "⇒" => Some("implication is written `->`"),
                    "↔" | "⇔" => Some("equivalence is written `<->`"),
                    "=" => Some("MLTL has no `=`; for equivalence write `<->`"),
                    "-" => Some("implication is written `->`"),
                    "<" => Some("equivalence is written `<->`"),
                    _ => None,
                };
                if let Some(h) = hint {
                    d.notes.push(format!("help: {h}"));
                }
            }
            ErrorKind::NumberTooLarge => {
                d.title = "number too large".to_string();
                d.labels.push(primary(at.start, at.end, format!("larger than {}", usize::MAX)));
            }
            ErrorKind::NumberingFailed => {
                d.title = "atom numbers ran out".to_string();
                d.notes.push("note: a `pN` atom has N ≥ usize::MAX, or there are more names than numbers".to_string());
            }
            ErrorKind::Expected(e) => {
                let t = Tokens::new(src);
                let k = t.index(at.start);
                let rel = self.related.as_ref().map(|r| t.index(r.start));
                match e {
                    Expected::Formula => {
                        let f = shown(src, &t, k);
                        let prev = k.checked_sub(1).map(|p| (p, slice(src, t.start(p), t.end(p))));
                        match &prev {
                            Some((p, s)) if s == "(" && f == "`)`" => {
                                d.title = "empty parentheses".to_string();
                                d.labels.push(primary(t.start(*p), at.end, "expected a formula inside"));
                            }
                            _ => {
                                d.title = format!("expected a formula, found {f}");
                                d.labels.push(primary(at.start, at.end, "expected a formula here"));
                                match &prev {
                                    Some((p, s)) if is_binary(s) || s == "!" => {
                                        d.labels.push(secondary(t.start(*p), t.end(*p), format!("`{s}` needs a formula after it")));
                                    }
                                    Some((p, s)) if s == "]" => {
                                        d.labels.push(secondary(t.start(*p), t.end(*p), "the interval needs a formula after it"));
                                    }
                                    _ => {}
                                }
                                let ft = slice(src, at.start, at.end);
                                if prev.is_none() && is_binary(&ft) {
                                    d.notes.push(format!("help: `{ft}` needs a formula on its left too, e.g. `p {ft} q`"));
                                }
                            }
                        }
                    }
                    Expected::IntervalOrder => {
                        let lo = slice(src, t.start(k), t.end(k));
                        let hi = slice(src, t.start(k + 2), t.end(k + 2));
                        d.title = "interval ends before it starts".to_string();
                        d.labels.push(primary(t.start(k), t.end(k + 2), format!("{lo} is greater than {hi}")));
                        d.notes.push("note: an interval `[a,b]` needs a ≤ b".to_string());
                    }
                    Expected::IntervalOpen | Expected::IntervalLo | Expected::IntervalComma
                    | Expected::IntervalHi | Expected::IntervalClose => {
                        let op = rel.unwrap_or(k);
                        let o = slice(src, t.start(op), t.end(op));
                        let f = shown(src, &t, k);
                        let (title, label) = match e {
                            Expected::IntervalOpen => (format!("expected `[` after `{o}`"), "expected an interval `[a,b]` here"),
                            Expected::IntervalComma => (format!("expected `,`, found {f}"), "expected `,` here"),
                            Expected::IntervalClose => (format!("expected `]`, found {f}"), "expected `]` here"),
                            _ => (format!("expected a number, found {f}"), "expected a number here"),
                        };
                        d.title = title;
                        d.labels.push(primary(at.start, at.end, label));
                        let owner = if matches!(e, Expected::IntervalOpen) { format!("`{o}` needs an interval") }
                                    else { format!("in the interval of this `{o}`") };
                        d.labels.push(secondary(t.start(op), t.end(op), owner));
                        d.notes.push(format!(
                            "note: intervals are written `[a,b]` with whole numbers a ≤ b, e.g. {}",
                            interval_example(&o)
                        ));
                    }
                    Expected::CloseParen => after_formula(src, &t, k, rel, &mut d),
                    Expected::End => after_formula(src, &t, k, None, &mut d),
                }
            }
        }
        d
    }

    /// The one-line summary, e.g. "expected a formula, found `)`".
    pub fn title(&self, text: &[u8]) -> String {
        self.diagnostic(text).title
    }

    /// The full cargo-style report for `text`. `origin` names the source in
    /// the `-->` line (e.g. `"<input>"` or `"formulas.txt"`).
    pub fn render(&self, text: &[u8], origin: &str) -> String {
        self.render_at(text, origin, 1, false)
    }

    /// [`ParseError::render`] with terminal colours, as cargo prints them.
    pub fn render_colored(&self, text: &[u8], origin: &str) -> String {
        self.render_at(text, origin, 1, true)
    }

    /// For a formula that starts on line `first_line` of the file `origin`:
    /// line numbers are counted from there.
    pub fn render_at(&self, text: &[u8], origin: &str, first_line: usize, color: bool) -> String {
        render(&self.diagnostic(text), text, origin, first_line, color)
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl fmt::Debug for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match &self.kind {
            ErrorKind::UnknownChar => "UnknownChar",
            ErrorKind::NumberTooLarge => "NumberTooLarge",
            ErrorKind::NumberingFailed => "NumberingFailed",
            ErrorKind::Expected(e) => match e {
                Expected::Formula => "Expected(Formula)",
                Expected::IntervalOpen => "Expected(IntervalOpen)",
                Expected::IntervalLo => "Expected(IntervalLo)",
                Expected::IntervalComma => "Expected(IntervalComma)",
                Expected::IntervalHi => "Expected(IntervalHi)",
                Expected::IntervalClose => "Expected(IntervalClose)",
                Expected::IntervalOrder => "Expected(IntervalOrder)",
                Expected::CloseParen => "Expected(CloseParen)",
                Expected::End => "Expected(End)",
            },
        };
        write!(f, "{kind} at {:?}", self.at)
    }
}

// ---------------------------------------------------------------------------
// Layout, following rustc: gutter with line numbers, `^^^` under the main
// part, `---` under the others, the rightmost label inline and the others
// hanging below it.
// ---------------------------------------------------------------------------

struct Style {
    on: bool,
}

impl Style {
    fn paint(&self, code: &str, s: &str) -> String {
        if self.on && !s.is_empty() { format!("\x1b[{code}m{s}\x1b[0m") } else { s.to_string() }
    }
    fn error(&self, s: &str) -> String { self.paint("1;31", s) }
    fn bold(&self, s: &str) -> String { self.paint("1", s) }
    fn blue(&self, s: &str) -> String { self.paint("1;34", s) }
    fn mark(&self, primary: bool, s: &str) -> String {
        if primary { self.error(s) } else { self.blue(s) }
    }
}

/// Line number (from 1), the line's byte range, and the column (from 0, in
/// characters) of byte `pos`.
fn locate(src: &[u8], pos: usize) -> (usize, usize, usize, usize) {
    let pos = pos.min(src.len());
    let line_start = src[..pos].iter().rposition(|&c| c == b'\n').map_or(0, |i| i + 1);
    let line_end = src[pos..].iter().position(|&c| c == b'\n').map_or(src.len(), |i| pos + i);
    let line_no = src[..line_start].iter().filter(|&&c| c == b'\n').count() + 1;
    let col = String::from_utf8_lossy(&src[line_start..pos]).chars().count();
    (line_no, line_start, line_end, col)
}

fn chars_between(src: &[u8], a: usize, b: usize) -> usize {
    String::from_utf8_lossy(&src[a.min(b)..b]).chars().count()
}

fn render(d: &Diagnostic, src: &[u8], origin: &str, first_line: usize, color: bool) -> String {
    let shift = first_line.max(1) - 1;
    let st = Style { on: color };
    let mut out = format!("{}{}\n", st.error("error"), st.bold(&format!(": {}", d.title)));
    let main = d.labels.iter().find(|l| l.primary).or(d.labels.first());
    // Lines that carry labels, in order.
    let mut lines: Vec<usize> = d.labels.iter().map(|l| locate(src, l.start).0).collect();
    lines.sort();
    lines.dedup();
    let width = lines.last().map_or(1, |n| (n + shift).to_string().len());
    let pad = " ".repeat(width);
    if let Some(m) = main {
        let (ln, _, _, col) = locate(src, m.start);
        out += &format!("{pad}{} {origin}:{}:{}\n", st.blue("-->"), ln + shift, col + 1);
    }
    if !d.labels.is_empty() {
        out += &format!("{pad} {}\n", st.blue("|"));
    }
    for &ln in &lines {
        let mut labels: Vec<(usize, usize, &Label)> = Vec::new();
        let mut line_range = (0, 0);
        for l in &d.labels {
            let (n, ls, le, col) = locate(src, l.start);
            if n != ln {
                continue;
            }
            line_range = (ls, le);
            let end = l.end.min(le).max(l.start);
            let w = chars_between(src, l.start, end).max(1);
            labels.push((col, w, l));
        }
        labels.sort_by_key(|x| x.0);
        let line_text: String = String::from_utf8_lossy(&src[line_range.0..line_range.1]).replace('\t', " ");
        out += &format!("{} {} {}\n", st.blue(&format!("{:>width$}", ln + shift)), st.blue("|"), line_text);
        // Marker line, with the rightmost label inline.
        let mut marks = String::new();
        let mut pos = 0;
        for (col, w, l) in &labels {
            if *col < pos {
                continue;
            }
            marks += &" ".repeat(col - pos);
            marks += &st.mark(l.primary, &(if l.primary { "^" } else { "-" }).repeat(*w));
            pos = col + w;
        }
        let (_, _, last) = labels.last().unwrap();
        if !last.text.is_empty() {
            marks += &format!(" {}", st.mark(last.primary, &last.text));
        }
        out += &format!("{pad} {} {}\n", st.blue("|"), marks);
        // The other labels hang below, right to left.
        let rest: Vec<&(usize, usize, &Label)> = labels[..labels.len() - 1].iter().filter(|x| !x.2.text.is_empty()).collect();
        if !rest.is_empty() {
            let bars = |upto: usize| {
                let mut s = String::new();
                let mut p = 0;
                for (col, _, l) in rest.iter().take(upto) {
                    s += &" ".repeat(col - p);
                    s += &st.mark(l.primary, "|");
                    p = col + 1;
                }
                (s, p)
            };
            out += &format!("{pad} {} {}\n", st.blue("|"), bars(rest.len()).0);
            for k in (0..rest.len()).rev() {
                let (s, p) = bars(k);
                let (col, _, l) = rest[k];
                out += &format!("{pad} {} {}{}{}\n", st.blue("|"), s, " ".repeat(col - p), st.mark(l.primary, &l.text));
            }
        }
    }
    if !d.notes.is_empty() {
        if !d.labels.is_empty() {
            out += &format!("{pad} {}\n", st.blue("|"));
        }
        for n in &d.notes {
            let (kind, rest) = n.split_once(": ").unwrap_or(("note", n));
            out += &format!("{pad} {} {}: {}\n", st.blue("="), st.bold(kind), rest);
        }
    }
    out
}
