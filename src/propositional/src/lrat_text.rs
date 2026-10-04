//! Text LRAT parser (unverified, and needs no trust: `check_lrat` is sound
//! for any steps, so a parsing bug can only make a check fail).
//!
//! Lines: `id l1 .. lk 0 h1 .. hm 0` (addition) or `id d c1 .. cn 0`
//! (deletion); lines starting with `c` are comments.
use crate::lrat::LratStep;

/// Parse LRAT text into steps. `None` on malformed input.
pub fn parse_lrat(text: &str) -> Option<Vec<LratStep>> {
    let mut steps = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let mut toks = line.split_ascii_whitespace();
        let id: u64 = toks.next()?.parse().ok()?;
        let mut toks = toks.peekable();
        if toks.peek() == Some(&"d") {
            toks.next();
            let mut ids = Vec::new();
            loop {
                let t: u64 = toks.next()?.parse().ok()?;
                if t == 0 {
                    break;
                }
                ids.push(t);
            }
            steps.push(LratStep::Delete { ids });
        } else {
            let mut clause = Vec::new();
            loop {
                let l: i32 = toks.next()?.parse().ok()?;
                if l == 0 {
                    break;
                }
                clause.push(l);
            }
            let mut hints = Vec::new();
            loop {
                let h: i64 = toks.next()?.parse().ok()?;
                if h == 0 {
                    break;
                }
                hints.push(h);
            }
            steps.push(LratStep::Add { id, clause, hints });
        }
        let _ = id;
    }
    Some(steps)
}

/// Parse DIMACS CNF text (`p cnf` header and comments are skipped).
pub fn parse_dimacs(text: &str) -> Option<Vec<Vec<i32>>> {
    let mut cnf = Vec::new();
    let mut cur = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') || line.starts_with('p') {
            continue;
        }
        for t in line.split_ascii_whitespace() {
            let l: i32 = t.parse().ok()?;
            if l == 0 {
                cnf.push(std::mem::take(&mut cur));
            } else {
                cur.push(l);
            }
        }
    }
    if !cur.is_empty() {
        return None;
    }
    Some(cnf)
}
