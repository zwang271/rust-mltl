//! Traces in R2U2's CSV format (GRAMMAR.md §6):
//!
//! ```text
//! # request,grant
//! 1,0
//! 0,1
//! ```
//!
//! `csv_trace` is the specification, on bytes: split into lines, the first
//! non-blank line is the header, every other non-blank line is a row.
//! `parse_csv` is proved to return exactly what it gives.
use vstd::prelude::*;
use crate::lexer::*;
use crate::printer::*;
use crate::error::*;
use crate::trace::*;
use crate::numbering::eq_bytes;
use crate::atoms::exec_valid_name;

verus! {

/// What is wrong with a CSV trace.
pub enum CsvError {
    /// No non-blank line, so no header.
    NoHeader,
    /// The header is not `#` followed by names separated by commas.
    BadHeader,
    /// A name appears twice in the header.
    DuplicateName,
    /// A row has a different number of values than the header has names.
    RowLength,
    /// A value other than `0` or `1`.
    BadValue,
}

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// Space or tab.
pub open spec fn is_blank(c: u8) -> bool { c == 32 || c == 9 }

pub open spec fn trim_start(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() > 0 && is_blank(s[0]) { trim_start(s.drop_first()) } else { s }
}

pub open spec fn trim_end(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() > 0 && is_blank(s.last()) { trim_end(s.drop_last()) } else { s }
}

/// `s` without spaces and tabs at either end.
pub open spec fn trim(s: Seq<u8>) -> Seq<u8> {
    trim_end(trim_start(s))
}

/// `s` cut at every `c`: `k` occurrences give `k + 1` pieces.
pub open spec fn split(s: Seq<u8>, c: u8) -> Seq<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![Seq::empty()]
    } else {
        let r = split(s.drop_last(), c);
        if s.last() == c { r.push(Seq::empty()) } else { r.update(r.len() - 1, r.last().push(s.last())) }
    }
}

/// A line without its `\r` (for `\r\n` line ends).
pub open spec fn strip_cr(l: Seq<u8>) -> Seq<u8> {
    if l.len() > 0 && l.last() == 13 { l.drop_last() } else { l }
}

/// The lines of the text.
pub open spec fn lines(s: Seq<u8>) -> Seq<Seq<u8>> {
    split(s, 10).map_values(|l: Seq<u8>| strip_cr(l))
}

pub open spec fn blank(l: Seq<u8>) -> bool {
    trim(l).len() == 0
}

/// The comma-separated items of a line, trimmed.
pub open spec fn cells(l: Seq<u8>) -> Seq<Seq<u8>> {
    split(l, 44).map_values(|c: Seq<u8>| trim(c))
}

/// The header: `#`, then distinct names separated by commas.
pub open spec fn header(l: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    let t = trim(l);
    if t.len() >= 1 && t[0] == 35 {
        let ns = cells(t.drop_first());
        if (forall|k: int| 0 <= k < ns.len() ==> valid_name(#[trigger] ns[k])) && ns.no_duplicates() {
            Some(ns)
        } else {
            None
        }
    } else {
        None
    }
}

pub open spec fn is_value(c: Seq<u8>) -> bool {
    c == seq![48u8] || c == seq![49u8]
}

/// A row of exactly `w` values, each `0` or `1` (`true` for `1`).
pub open spec fn row(l: Seq<u8>, w: nat) -> Option<Seq<bool>> {
    let cs = cells(l);
    if cs.len() == w && forall|k: int| 0 <= k < cs.len() ==> is_value(#[trigger] cs[k]) {
        Some(cs.map_values(|c: Seq<u8>| c == seq![49u8]))
    } else {
        None
    }
}

/// The header names whose value is `1`, in header order.
pub open spec fn true_names(h: Seq<Seq<u8>>, v: Seq<bool>) -> Seq<Seq<u8>>
    decreases h.len(),
{
    if h.len() == 0 || v.len() == 0 {
        Seq::empty()
    } else {
        let r = true_names(h.drop_last(), v.drop_last());
        if v.last() { r.push(h.last()) } else { r }
    }
}

/// The steps of the lines after the header; blank lines are skipped.
pub open spec fn body(ls: Seq<Seq<u8>>, h: Seq<Seq<u8>>) -> Option<SpecSteps>
    decreases ls.len(),
{
    if ls.len() == 0 {
        Some(Seq::empty())
    } else {
        match body(ls.drop_last(), h) {
            Some(r) => {
                if blank(ls.last()) {
                    Some(r)
                } else {
                    match row(ls.last(), h.len()) {
                        Some(v) => Some(r.push(true_names(h, v))),
                        None => None,
                    }
                }
            },
            None => None,
        }
    }
}

/// The first non-blank line at or after `i`.
pub open spec fn first_line(ls: Seq<Seq<u8>>, i: nat) -> Option<nat>
    decreases ls.len() - i,
{
    if i >= ls.len() { None } else if blank(ls[i as int]) { first_line(ls, i + 1) } else { Some(i) }
}

/// The steps of a CSV trace, or `None` if the text is not one.
pub open spec fn csv_trace(s: Seq<u8>) -> Option<SpecSteps> {
    let ls = lines(s);
    match first_line(ls, 0) {
        Some(h) => match header(ls[h as int]) {
            Some(names) => body(ls.subrange((h + 1) as int, ls.len() as int), names),
            None => None,
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Executable reader
// ---------------------------------------------------------------------------

/// Once some lines fail, more lines fail too.
proof fn lemma_body_none(ls: Seq<Seq<u8>>, a: int, k: int, m: int, h: Seq<Seq<u8>>)
    requires
        0 <= a <= k <= m <= ls.len(),
        body(ls.subrange(a, k), h) is None,
    ensures
        body(ls.subrange(a, m), h) is None,
    decreases m - k,
{
    if m > k {
        lemma_body_none(ls, a, k, m - 1, h);
        assert(ls.subrange(a, m).drop_last() =~= ls.subrange(a, m - 1));
    }
}

/// The bytes of line `k` (before removing a `\r`).
fn line_span(starts: &Vec<usize>, raw: &Vec<Vec<u8>>, k: usize, len: usize) -> (sp: Span)
    requires
        k < raw@.len(), starts@.len() == raw@.len(),
        forall|i: int| 0 <= i < raw@.len() ==> #[trigger] starts@[i] + raw@[i]@.len() <= len,
    ensures
        span_ok(sp, len as nat),
{
    proof { assert(starts@[k as int] + raw@[k as int]@.len() <= len); }
    Span { start: starts[k], end: starts[k] + raw[k].len() }
}

proof fn lemma_split_len(s: Seq<u8>, c: u8)
    ensures
        split(s, c).len() >= 1,
    decreases s.len(),
{
    if s.len() > 0 { lemma_split_len(s.drop_last(), c); }
}

/// `split`, with the byte offset where each piece starts.
fn exec_split(s: &[u8], c: u8) -> (r: (Vec<Vec<u8>>, Vec<usize>))
    ensures
        names_view(r.0@) == split(s@, c),
        r.1@.len() == r.0@.len(),
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] r.1@[i] + r.0@[i]@.len() <= s.len(),
{
    let mut done: Vec<Vec<u8>> = Vec::new();
    let mut starts: Vec<usize> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();
    let mut cur_start: usize = 0;
    let mut k: usize = 0;
    proof {
        assert(s@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(names_view(done@).push(cur@) =~= seq![Seq::<u8>::empty()]);
    }
    while k < s.len()
        invariant
            k <= s.len(),
            names_view(done@).push(cur@) == split(s@.subrange(0, k as int), c),
            starts@.len() == done@.len(),
            forall|i: int| 0 <= i < done@.len() ==> #[trigger] starts@[i] + done@[i]@.len() <= k,
            cur_start + cur@.len() == k,
        decreases s.len() - k,
    {
        let b = s[k];
        let ghost pre = s@.subrange(0, k as int);
        let ghost next = s@.subrange(0, k + 1);
        proof {
            assert(next.drop_last() =~= pre);
            assert(next.last() == b);
            lemma_split_len(pre, c);
        }
        if b == c {
            let ghost dv = names_view(done@);
            let ghost cv = cur@;
            let ghost st0 = starts@;
            let ghost dn0 = done@;
            done.push(cur);
            cur = Vec::new();
            starts.push(cur_start);
            cur_start = k + 1;
            proof {
                assert(names_view(done@) =~= dv.push(cv));
                assert(names_view(done@).push(cur@) =~= split(pre, c).push(Seq::<u8>::empty()));
                assert forall|i: int| 0 <= i < done@.len() implies #[trigger] starts@[i] + done@[i]@.len() <= k + 1 by {
                    if i < dn0.len() { assert(starts@[i] == st0[i] && done@[i] == dn0[i]); }
                }
            }
        } else {
            let ghost dv = names_view(done@);
            let ghost cv = cur@;
            cur.push(b);
            proof {
                let r = split(pre, c);
                assert(r == dv.push(cv));
                assert(r.update(r.len() - 1, r.last().push(b)) =~= dv.push(cur@));
            }
        }
        k = k + 1;
    }
    proof { assert(s@.subrange(0, s.len() as int) =~= s@); }
    let ghost dv = names_view(done@);
    let ghost cv = cur@;
    done.push(cur);
    starts.push(cur_start);
    proof { assert(names_view(done@) =~= dv.push(cv)); }
    (done, starts)
}

/// `trim`.
fn exec_trim(s: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == trim(s@),
{
    let n = s.len();
    let mut a: usize = 0;
    proof { assert(s@.subrange(0, n as int) =~= s@); }
    while a < n && (s[a] == 32 || s[a] == 9)
        invariant
            a <= n, n == s.len(),
            trim_start(s@) == trim_start(s@.subrange(a as int, n as int)),
        decreases n - a,
    {
        proof { assert(s@.subrange(a as int, n as int).drop_first() =~= s@.subrange(a + 1, n as int)); }
        a = a + 1;
    }
    let ghost t = s@.subrange(a as int, n as int);
    proof { assert(trim_start(s@) == t); }
    let mut b: usize = n;
    proof { assert(t.subrange(0, (n - a) as int) =~= t); }
    while b > a && (s[b - 1] == 32 || s[b - 1] == 9)
        invariant
            a <= b <= n, n == s.len(), t == s@.subrange(a as int, n as int),
            trim_end(t) == trim_end(t.subrange(0, (b - a) as int)),
        decreases b,
    {
        proof {
            let u = t.subrange(0, (b - a) as int);
            assert(u.last() == s[b - 1]);
            assert(u.drop_last() =~= t.subrange(0, (b - 1 - a) as int));
        }
        b = b - 1;
    }
    let mut r: Vec<u8> = Vec::new();
    let mut k = a;
    while k < b
        invariant
            a <= k <= b <= n, n == s.len(),
            r@ == s@.subrange(a as int, k as int),
        decreases b - k,
    {
        r.push(s[k]);
        k = k + 1;
        proof { assert(r@ =~= s@.subrange(a as int, k as int)); }
    }
    proof { assert(t.subrange(0, (b - a) as int) =~= s@.subrange(a as int, b as int)); }
    r
}

fn exec_strip_cr(l: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == strip_cr(l@),
{
    let mut r = l.clone();
    if r.len() > 0 && r[r.len() - 1] == 13 {
        r.pop();
    }
    proof { if l@.len() > 0 && l@.last() == 13 { assert(r@ =~= l@.drop_last()); } }
    r
}

fn exec_cells(l: &[u8]) -> (r: Vec<Vec<u8>>)
    ensures
        names_view(r@) == cells(l@),
{
    let (pieces, _) = exec_split(l, 44);
    let ghost pv = names_view(pieces@);
    let mut r: Vec<Vec<u8>> = Vec::new();
    let mut k = 0;
    while k < pieces.len()
        invariant
            k <= pieces.len(), pv == names_view(pieces@),
            names_view(r@) == pv.subrange(0, k as int).map_values(|c: Seq<u8>| trim(c)),
        decreases pieces.len() - k,
    {
        let ghost before = names_view(r@);
        r.push(exec_trim(pieces[k].as_slice()));
        proof {
            assert(names_view(r@) =~= before.push(trim(pv[k as int])));
            assert(pv.subrange(0, k + 1).map_values(|c: Seq<u8>| trim(c)) =~= before.push(trim(pv[k as int])));
        }
        k = k + 1;
    }
    proof { assert(pv.subrange(0, pieces.len() as int) =~= pv); }
    r
}

fn exec_blank(l: &[u8]) -> (r: bool)
    ensures
        r == blank(l@),
{
    exec_trim(l).len() == 0
}

/// `header(l)`, or which rule the header breaks.
fn exec_header(l: &Vec<u8>) -> (r: Result<Vec<Vec<u8>>, CsvError>)
    ensures
        match r {
            Ok(ns) => header(l@) == Some(names_view(ns@)),
            Err(_) => header(l@) is None,
        },
{
    let t = exec_trim(l.as_slice());
    if t.len() == 0 || t[0] != 35 {
        return Err(CsvError::BadHeader);
    }
    let ghost tv = t@;
    let rest = slice_from(&t, 1);
    proof { assert(rest@ == tv.drop_first()); }
    let ns = exec_cells(rest.as_slice());
    let ghost nv = names_view(ns@);
    let mut k = 0;
    while k < ns.len()
        invariant
            k <= ns.len(), nv == names_view(ns@),
            tv == trim(l@), tv.len() >= 1, nv == cells(tv.drop_first()),
            forall|m: int| 0 <= m < k ==> valid_name(#[trigger] nv[m]),
        decreases ns.len() - k,
    {
        if !exec_valid_name(&ns[k]) {
            proof {
                assert(nv[k as int] == ns@[k as int]@);
                assert(!valid_name(nv[k as int]));
                assert(tv == trim(l@));
                assert(nv == cells(tv.drop_first()));
                assert(!(forall|m: int| 0 <= m < nv.len() ==> valid_name(#[trigger] nv[m])));
            }
            return Err(CsvError::BadHeader);
        }
        k = k + 1;
    }
    let mut i = 0;
    while i < ns.len()
        invariant
            i <= ns.len(), nv == names_view(ns@),
            tv == trim(l@), tv.len() >= 1, tv[0] == 35, nv == cells(tv.drop_first()),
            forall|m: int| 0 <= m < nv.len() ==> valid_name(#[trigger] nv[m]),
            forall|a: int, b: int| 0 <= a < i && 0 <= b < nv.len() && a != b ==> nv[a] != nv[b],
        decreases ns.len() - i,
    {
        let mut j = 0;
        while j < ns.len()
            invariant
                i < ns.len(), j <= ns.len(), nv == names_view(ns@),
                tv == trim(l@), tv.len() >= 1, tv[0] == 35, nv == cells(tv.drop_first()),
                forall|a: int, b: int| 0 <= a < i && 0 <= b < nv.len() && a != b ==> nv[a] != nv[b],
                forall|b: int| 0 <= b < j && b != i ==> nv[i as int] != nv[b],
            decreases ns.len() - j,
        {
            if j != i && eq_bytes(&ns[i], &ns[j]) {
                proof {
                    assert(nv[i as int] == ns@[i as int]@ && nv[j as int] == ns@[j as int]@);
                    assert(nv[i as int] == nv[j as int]);
                    assert(!nv.no_duplicates());
                    assert(tv == trim(l@));
                    assert(nv == cells(tv.drop_first()));
                }
                return Err(CsvError::DuplicateName);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    Ok(ns)
}

fn slice_from(v: &Vec<u8>, a: usize) -> (r: Vec<u8>)
    requires
        a <= v.len(),
    ensures
        r@ == v@.subrange(a as int, v.len() as int),
{
    let mut r: Vec<u8> = Vec::new();
    let mut k = a;
    while k < v.len()
        invariant
            a <= k <= v.len(),
            r@ == v@.subrange(a as int, k as int),
        decreases v.len() - k,
    {
        r.push(v[k]);
        k = k + 1;
        proof { assert(r@ =~= v@.subrange(a as int, k as int)); }
    }
    r
}

/// The step of row `l` under header `h`: `true_names(h, row(l, |h|))`.
fn exec_row(l: &Vec<u8>, h: &Vec<Vec<u8>>) -> (r: Result<Vec<Vec<u8>>, CsvError>)
    ensures
        match r {
            Ok(ns) => row(l@, h.len() as nat) matches Some(v) && names_view(ns@) == true_names(names_view(h@), v),
            Err(_) => row(l@, h.len() as nat) is None,
        },
{
    let cs = exec_cells(l.as_slice());
    let ghost cv = names_view(cs@);
    let ghost hv = names_view(h@);
    if cs.len() != h.len() {
        return Err(CsvError::RowLength);
    }
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut k = 0;
    proof { assert(names_view(out@) =~= Seq::<Seq<u8>>::empty()); }
    while k < cs.len()
        invariant
            k <= cs.len(), cs.len() == h.len(), cv == names_view(cs@), hv == names_view(h@),
            cv == cells(l@),
            forall|m: int| 0 <= m < k ==> is_value(#[trigger] cv[m]),
            names_view(out@) == true_names(hv.subrange(0, k as int),
                cv.subrange(0, k as int).map_values(|c: Seq<u8>| c == seq![49u8])),
        decreases cs.len() - k,
    {
        let c = &cs[k];
        let one = c.len() == 1 && c[0] == 49;
        let zero = c.len() == 1 && c[0] == 48;
        proof {
            assert(one <==> cv[k as int] == seq![49u8]) by {
                if cv[k as int] == seq![49u8] { assert(c@ == cv[k as int]); }
                if one { assert(c@ =~= seq![49u8]); }
            }
            assert(zero <==> cv[k as int] == seq![48u8]) by {
                if cv[k as int] == seq![48u8] { assert(c@ == cv[k as int]); }
                if zero { assert(c@ =~= seq![48u8]); }
            }
        }
        if !one && !zero {
            proof {
                assert(!is_value(cv[k as int]));
                assert(cv == cells(l@));
                assert(!(forall|m: int| 0 <= m < cv.len() ==> is_value(#[trigger] cv[m])));
            }
            return Err(CsvError::BadValue);
        }
        let ghost before = names_view(out@);
        let ghost hs = hv.subrange(0, k + 1);
        let ghost vs = cv.subrange(0, k + 1).map_values(|c: Seq<u8>| c == seq![49u8]);
        proof {
            assert(hs.drop_last() =~= hv.subrange(0, k as int));
            assert(vs.drop_last() =~= cv.subrange(0, k as int).map_values(|c: Seq<u8>| c == seq![49u8]));
            assert(vs.last() == one);
            assert(hs.last() == hv[k as int]);
        }
        if one {
            out.push(h[k].clone());
            proof { assert(names_view(out@) =~= before.push(hv[k as int])); }
        }
        k = k + 1;
    }
    proof {
        assert(hv.subrange(0, h.len() as int) =~= hv);
        assert(cv.subrange(0, cs.len() as int) =~= cv);
    }
    Ok(out)
}

/// Parse a CSV trace (GRAMMAR.md §6).
///
/// - **Sound and complete:** `Ok(steps)` exactly when the text is a CSV
///   trace, and then `steps` are its steps (each the names whose value is
///   `1`, in header order).
/// - **Errors** point at the offending line; every position is inside the text.
pub fn parse_csv(text: &[u8]) -> (r: Result<ExecSteps, ParseError>)
    ensures
        r is Ok ==> csv_trace(text@) == Some(steps_view((r->Ok_0)@)),
        r is Err ==> csv_trace(text@) is None && error_ok(r->Err_0, text.len() as nat),
{
    let (raw, starts) = exec_split(text, 10);
    let ghost rv = names_view(raw@);
    let ghost ls = lines(text@);
    let n = raw.len();
    let mut ln: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n, n == raw.len(), rv == names_view(raw@), rv == split(text@, 10), ls == lines(text@),
            names_view(ln@) == ls.subrange(0, i as int),
        decreases n - i,
    {
        let ghost before = names_view(ln@);
        ln.push(exec_strip_cr(&raw[i]));
        proof {
            assert(names_view(ln@) =~= before.push(strip_cr(rv[i as int])));
            assert(ls.subrange(0, i + 1) =~= before.push(ls[i as int]));
        }
        i = i + 1;
    }
    let ghost lv = names_view(ln@);
    proof { assert(lv =~= ls); }
    // the header
    let mut h = 0;
    while h < n && exec_blank(ln[h].as_slice())
        invariant
            h <= n, n == ln.len(), lv == names_view(ln@), lv == ls,
            first_line(ls, 0) == first_line(ls, h as nat),
        decreases n - h,
    {
        proof { assert(lv[h as int] == ln@[h as int]@); }
        h = h + 1;
    }
    if h == n {
        return Err(ParseError { kind: ErrorKind::Csv(CsvError::NoHeader), at: Span { start: text.len(), end: text.len() }, related: None });
    }
    proof { assert(lv[h as int] == ln@[h as int]@); assert(first_line(ls, h as nat) == Some(h as nat)); }
    let names = match exec_header(&ln[h]) {
        Ok(ns) => ns,
        Err(e) => {
            return Err(ParseError { kind: ErrorKind::Csv(e), at: line_span(&starts, &raw, h, text.len()), related: None });
        },
    };
    let ghost hv = names_view(names@);
    proof { assert(lv[h as int] == ln@[h as int]@); }
    // the rows
    let mut out: ExecSteps = Vec::new();
    let mut k = h + 1;
    proof {
        assert(ls.subrange(h + 1, h + 1) =~= Seq::<Seq<u8>>::empty());
        assert(steps_view(out@) =~= Seq::<Seq<Seq<u8>>>::empty());
    }
    while k < n
        invariant
            h < k <= n, n == ln.len(), lv == names_view(ln@), lv == ls, hv == names_view(names@),
            n == starts@.len(), n == raw@.len(),
            forall|i: int| 0 <= i < raw@.len() ==> #[trigger] starts@[i] + raw@[i]@.len() <= text.len(),
            n == ls.len(), ls == lines(text@),
            first_line(ls, 0) == Some(h as nat),
            header(ls[h as int]) == Some(hv),
            body(ls.subrange(h + 1, k as int), hv) == Some(steps_view(out@)),
        decreases n - k,
    {
        let ghost pre = ls.subrange(h + 1, k as int);
        let ghost next = ls.subrange(h + 1, k + 1);
        proof {
            assert(next.drop_last() =~= pre);
            assert(next.last() == ls[k as int]);
            assert(lv[k as int] == ln@[k as int]@);
        }
        if !exec_blank(ln[k].as_slice()) {
            match exec_row(&ln[k], &names) {
                Ok(step) => {
                    let ghost before = steps_view(out@);
                    let ghost sv = names_view(step@);
                    out.push(step);
                    proof { assert(steps_view(out@) =~= before.push(sv)); }
                },
                Err(e) => {
                    proof {
                        assert(body(next, hv) is None);
                        lemma_body_none(ls, (h + 1) as int, (k + 1) as int, ls.len() as int, hv);
                    }
                    return Err(ParseError { kind: ErrorKind::Csv(e), at: line_span(&starts, &raw, k, text.len()), related: None });
                },
            }
        }
        k = k + 1;
    }
    proof { assert(ls.subrange(h + 1, n as int) == ls.subrange(h + 1, ls.len() as int)); }
    Ok(out)
}

} // verus!
