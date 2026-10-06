//! Traces in the sets syntax (GRAMMAR.md §6): `[{request}, {grant, ok}, {}]`.
//!
//! `trace_tokens` is the specification, one definition per grammar rule,
//! read left to right. `parse_trace` is proved to return exactly what it
//! gives, and `print_trace` to write text that reads back as the same steps.
use vstd::prelude::*;
use crate::lexer::*;
use crate::printer::*;
use crate::error::*;

verus! {

/// Names as written, one list per step (repeats kept; the step means the
/// set of them).
pub type ExecSteps = Vec<Vec<Vec<u8>>>;
pub type SpecSteps = Seq<Seq<Seq<u8>>>;

pub open spec fn names_view(ns: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    ns.map_values(|n: Vec<u8>| n@)
}

pub open spec fn steps_view(ss: Seq<Vec<Vec<u8>>>) -> SpecSteps {
    ss.map_values(|s: Vec<Vec<u8>>| names_view(s@))
}

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// `name { "," name } "}"` starting at token `i`: the names, and the
/// position after the `}`.
pub open spec fn names_at(ts: Seq<SpecToken>, i: nat) -> Option<(Seq<Seq<u8>>, nat)>
    decreases ts.len() - i,
{
    if i + 1 < ts.len() && ts[i as int] is Name {
        let n = ts[i as int]->Name_0;
        if ts[(i + 1) as int] is RBrace {
            Some((seq![n], i + 2))
        } else if ts[(i + 1) as int] is Comma {
            match names_at(ts, i + 2) {
                Some((ns, j)) => Some((seq![n] + ns, j)),
                None => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

/// `step = "{" [ name { "," name } ] "}"` starting at token `i`.
pub open spec fn step_at(ts: Seq<SpecToken>, i: nat) -> Option<(Seq<Seq<u8>>, nat)> {
    if i + 1 < ts.len() && ts[i as int] is LBrace {
        if ts[(i + 1) as int] is RBrace { Some((Seq::empty(), i + 2)) } else { names_at(ts, i + 1) }
    } else {
        None
    }
}

/// `step { "," step } "]"` starting at token `i`.
pub open spec fn steps_at(ts: Seq<SpecToken>, i: nat) -> Option<(SpecSteps, nat)>
    decreases ts.len() - i,
    via steps_at_decreases
{
    match step_at(ts, i) {
        Some((s, j)) => {
            if j < ts.len() && ts[j as int] is RBrack {
                Some((seq![s], j + 1))
            } else if j < ts.len() && ts[j as int] is Comma {
                match steps_at(ts, j + 1) {
                    Some((r, k)) => Some((seq![s] + r, k)),
                    None => None,
                }
            } else {
                None
            }
        },
        None => None,
    }
}

proof fn lemma_names_at_end(ts: Seq<SpecToken>, i: nat)
    ensures
        names_at(ts, i) matches Some((ns, j)) ==> i < j <= ts.len(),
    decreases ts.len() - i,
{
    if i + 1 < ts.len() && ts[i as int] is Name && ts[(i + 1) as int] is Comma {
        lemma_names_at_end(ts, i + 2);
    }
}

proof fn lemma_step_at_end(ts: Seq<SpecToken>, i: nat)
    ensures
        step_at(ts, i) matches Some((s, j)) ==> i < j <= ts.len(),
{
    lemma_names_at_end(ts, i + 1);
}

#[via_fn]
proof fn steps_at_decreases(ts: Seq<SpecToken>, i: nat) {
    lemma_step_at_end(ts, i);
}

/// `trace = "[" [ step { "," step } ] "]"`, using all tokens.
pub open spec fn trace_tokens(ts: Seq<SpecToken>) -> Option<SpecSteps> {
    if ts.len() == 2 && ts[0] is LBrack && ts[1] is RBrack {
        Some(Seq::empty())
    } else if ts.len() >= 1 && ts[0] is LBrack {
        match steps_at(ts, 1) {
            Some((r, k)) => if k == ts.len() { Some(r) } else { None },
            None => None,
        }
    } else {
        None
    }
}

/// The text is a trace with these steps.
pub open spec fn trace_denotes(s: Seq<u8>, steps: SpecSteps) -> bool {
    match lex_spec(s) {
        Some(ts) => trace_tokens(ts) == Some(steps),
        None => false,
    }
}

// ---------------------------------------------------------------------------
// Executable parser
// ---------------------------------------------------------------------------

/// What the trace parser expected at the token where it stopped.
pub enum TraceExpected {
    /// `[` at the start.
    Open,
    /// `{` or `]` right after the opening `[`.
    StepOrClose,
    /// `{` after a `,` between steps.
    Step,
    /// A name or `}` right after `{`.
    NameOrClose,
    /// A name after a `,` inside a step.
    Name,
    /// `,` or `}` after a name.
    CommaOrCloseStep,
    /// `,` or `]` after a step.
    CommaOrClose,
    /// Nothing after the closing `]`.
    End,
}

/// `names_at(ts, i0)` is `acc` followed by `names_at(ts, i)`.
pub open spec fn names_split(ts: Seq<SpecToken>, i0: nat, acc: Seq<Seq<u8>>, i: nat) -> bool {
    names_at(ts, i0) == match names_at(ts, i) {
        Some((ns, j)) => Some((acc + ns, j)),
        None => None::<(Seq<Seq<u8>>, nat)>,
    }
}

proof fn lemma_names_split_step(ts: Seq<SpecToken>, i0: nat, acc: Seq<Seq<u8>>, i: nat, n: Seq<u8>)
    requires
        names_split(ts, i0, acc, i),
        i + 1 < ts.len(),
        ts[i as int] == Token::<Seq<u8>>::Name(n),
        ts[(i + 1) as int] is Comma,
    ensures
        names_split(ts, i0, acc.push(n), i + 2),
{
    match names_at(ts, i + 2) {
        Some((ns, j)) => { assert(acc + (seq![n] + ns) =~= acc.push(n) + ns); },
        None => {},
    }
}

/// Reads `name { "," name } "}"` from token `i` into `out` (empty at the
/// start). Returns the position after `}`, or where it stopped and what it
/// expected there.
fn exec_names_at(ts: &Vec<Token<Vec<u8>>>, i: usize, out: &mut Vec<Vec<u8>>, after_open: bool)
    -> (r: Result<usize, (usize, TraceExpected)>)
    requires
        old(out)@.len() == 0,
    ensures
        match r {
            Ok(j) => names_at(tokens_view(ts@), i as nat) == Some((names_view(final(out)@), j as nat)),
            Err((k, _)) => names_at(tokens_view(ts@), i as nat) is None && k <= ts.len(),
        },
{
    let ghost tv = tokens_view(ts@);
    let n = ts.len();
    let mut k = i;
    proof {
        assert(names_view(out@) =~= Seq::<Seq<u8>>::empty());
        match names_at(tv, i as nat) {
            Some((ns, j)) => { assert(Seq::<Seq<u8>>::empty() + ns =~= ns); },
            None => {},
        }
    }
    let mut first = true;
    while k < n
        invariant
            n == ts.len(), tv == tokens_view(ts@),
            i <= k,
            names_split(tv, i as nat, names_view(out@), k as nat),
        decreases n - k,
    {
        proof { assert(tv[k as int] == token_view(ts@[k as int])); }
        let name = match &ts[k] {
            Token::Name(nm) => nm,
            _ => {
                let e = if first && after_open { TraceExpected::NameOrClose } else { TraceExpected::Name };
                return Err((k, e));
            },
        };
        if k + 1 >= n {
            return Err((n, TraceExpected::CommaOrCloseStep));
        }
        proof { assert(tv[k + 1] == token_view(ts@[k + 1])); }
        let ghost acc = names_view(out@);
        out.push(copy_vec(name));
        proof { assert(names_view(out@) =~= acc.push(name@)); }
        match &ts[k + 1] {
            Token::RBrace => {
                proof {
                    assert(names_at(tv, k as nat) == Some((seq![name@], (k + 2) as nat)));
                    assert(acc + seq![name@] =~= acc.push(name@));
                }
                return Ok(k + 2);
            },
            Token::Comma => {
                proof { lemma_names_split_step(tv, i as nat, acc, k as nat, name@); }
                k = k + 2;
            },
            _ => {
                return Err((k + 1, TraceExpected::CommaOrCloseStep));
            },
        }
        first = false;
    }
    let e = if first && after_open { TraceExpected::NameOrClose } else { TraceExpected::Name };
    Err((n, e))
}

fn copy_vec(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == v@,
{
    v.clone()
}

/// `steps_at(ts, i0)` is `acc` followed by `steps_at(ts, i)`.
pub open spec fn steps_split(ts: Seq<SpecToken>, i0: nat, acc: SpecSteps, i: nat) -> bool {
    steps_at(ts, i0) == match steps_at(ts, i) {
        Some((r, k)) => Some((acc + r, k)),
        None => None::<(SpecSteps, nat)>,
    }
}

/// Parse trace tokens: exactly `trace_tokens`. On failure, the token where
/// the parser stopped (`ts.len()` for the end) and what it expected there.
pub fn parse_trace_tokens(ts: &Vec<Token<Vec<u8>>>) -> (r: Result<ExecSteps, (usize, TraceExpected)>)
    ensures
        match r {
            Ok(steps) => trace_tokens(tokens_view(ts@)) == Some(steps_view(steps@)),
            Err((k, _)) => trace_tokens(tokens_view(ts@)) is None && k <= ts.len(),
        },
{
    let ghost tv = tokens_view(ts@);
    let n = ts.len();
    if n == 0 {
        return Err((0, TraceExpected::Open));
    }
    proof { assert(tv[0] == token_view(ts@[0])); }
    if !matches!(ts[0], Token::LBrack) {
        return Err((0, TraceExpected::Open));
    }
    if n == 1 {
        return Err((1, TraceExpected::StepOrClose));
    }
    proof { assert(tv[1] == token_view(ts@[1])); }
    if matches!(ts[1], Token::RBrack) {
        if n == 2 {
            let r: ExecSteps = Vec::new();
            proof { assert(steps_view(r@) =~= Seq::<Seq<Seq<u8>>>::empty()); }
            return Ok(r);
        }
        proof { assert(step_at(tv, 1) is None); }
        return Err((2, TraceExpected::End));
    }
    let mut out: ExecSteps = Vec::new();
    let mut k: usize = 1;
    proof {
        assert(steps_view(out@) =~= Seq::<Seq<Seq<u8>>>::empty());
        match steps_at(tv, 1) {
            Some((r, j)) => { assert(Seq::<Seq<Seq<u8>>>::empty() + r =~= r); },
            None => {},
        }
    }
    let mut first = true;
    while k < n
        invariant
            n == ts.len(), tv == tokens_view(ts@),
            1 <= k,
            steps_split(tv, 1, steps_view(out@), k as nat),
            !(n == 2 && tv[1] is RBrack),
            tv[0] is LBrack,
        decreases n - k,
    {
        proof { assert(tv[k as int] == token_view(ts@[k as int])); }
        if !matches!(ts[k], Token::LBrace) {
            let e = if first { TraceExpected::StepOrClose } else { TraceExpected::Step };
            return Err((k, e));
        }
        if k + 1 >= n {
            return Err((n, TraceExpected::NameOrClose));
        }
        proof { assert(tv[k + 1] == token_view(ts@[k + 1])); }
        let mut names: Vec<Vec<u8>> = Vec::new();
        let j: usize;
        if matches!(ts[k + 1], Token::RBrace) {
            j = k + 2;
            proof { assert(names_view(names@) =~= Seq::<Seq<u8>>::empty()); }
        } else {
            match exec_names_at(ts, k + 1, &mut names, true) {
                Ok(e) => { j = e; },
                Err(e) => { return Err(e); },
            }
        }
        proof {
            assert(step_at(tv, k as nat) == Some((names_view(names@), j as nat)));
            lemma_step_at_end(tv, k as nat);
        }
        let ghost acc = steps_view(out@);
        let ghost s = names_view(names@);
        out.push(names);
        proof { assert(steps_view(out@) =~= acc.push(s)); }
        if j >= n {
            return Err((n, TraceExpected::CommaOrClose));
        }
        proof { assert(tv[j as int] == token_view(ts@[j as int])); }
        match &ts[j] {
            Token::RBrack => {
                proof {
                    assert(steps_at(tv, k as nat) == Some((seq![s], (j + 1) as nat)));
                    assert(acc + seq![s] =~= acc.push(s));
                }
                if j + 1 == n {
                    return Ok(out);
                }
                return Err((j + 1, TraceExpected::End));
            },
            Token::Comma => {
                proof {
                    match steps_at(tv, (j + 1) as nat) {
                        Some((r, m)) => { assert(acc + (seq![s] + r) =~= acc.push(s) + r); },
                        None => {},
                    }
                }
                k = j + 1;
            },
            _ => {
                return Err((j, TraceExpected::CommaOrClose));
            },
        }
        first = false;
    }
    Err((n, TraceExpected::Step))
}

/// Parse a trace in the sets syntax (GRAMMAR.md §6).
///
/// - **Sound and complete:** `Ok(steps)` exactly when the text denotes a
///   trace, and then `steps` are its steps.
/// - **Errors** say where the text stopped being a trace; every position is
///   inside the text.
pub fn parse_trace(text: &[u8]) -> (r: Result<ExecSteps, ParseError>)
    ensures
        r is Ok ==> trace_denotes(text@, steps_view((r->Ok_0)@)),
        forall|s: SpecSteps| #[trigger] trace_denotes(text@, s) ==> r is Ok && steps_view((r->Ok_0)@) == s,
        r is Err ==> error_ok(r->Err_0, text.len() as nat),
{
    let mut spans: Vec<Span> = Vec::new();
    let mut bad = Span { start: 0, end: 0 };
    match lex(text, &mut spans, &mut bad) {
        Some(ts) => {
            match parse_trace_tokens(&ts) {
                Ok(steps) => Ok(steps),
                Err((k, e)) => {
                    let at = if k < spans.len() {
                        proof { assert(spans@[k as int].start < spans@[k as int].end); }
                        Span { start: spans[k].start, end: spans[k].end }
                    } else {
                        Span { start: text.len(), end: text.len() }
                    };
                    Err(ParseError { kind: ErrorKind::Trace(e), at, related: None })
                },
            }
        },
        None => {
            let digit = bad.start < text.len() && 48 <= text[bad.start] && text[bad.start] <= 57;
            let kind = if digit { ErrorKind::NumberTooLarge } else { ErrorKind::UnknownChar };
            Err(ParseError { kind, at: bad, related: None })
        },
    }
}

// ---------------------------------------------------------------------------
// Printer
// ---------------------------------------------------------------------------

/// `n1 , n2 , … , nk` (no braces).
pub open spec fn names_tokens(ns: Seq<Seq<u8>>) -> Seq<SpecToken>
    decreases ns.len(),
{
    if ns.len() == 0 {
        Seq::empty()
    } else if ns.len() == 1 {
        seq![Token::Name(ns[0])]
    } else {
        seq![Token::Name(ns[0]), Token::Comma] + names_tokens(ns.drop_first())
    }
}

pub open spec fn step_tokens(ns: Seq<Seq<u8>>) -> Seq<SpecToken> {
    seq![Token::LBrace] + names_tokens(ns) + seq![Token::RBrace]
}

/// The steps separated by commas.
pub open spec fn steps_tokens(ss: SpecSteps) -> Seq<SpecToken>
    decreases ss.len(),
{
    if ss.len() == 0 {
        Seq::empty()
    } else if ss.len() == 1 {
        step_tokens(ss[0])
    } else {
        step_tokens(ss[0]) + seq![Token::Comma] + steps_tokens(ss.drop_first())
    }
}

pub open spec fn trace_print_tokens(ss: SpecSteps) -> Seq<SpecToken> {
    seq![Token::LBrack] + steps_tokens(ss) + seq![Token::RBrack]
}

/// The printed text of a trace.
pub open spec fn trace_text(ss: SpecSteps) -> Seq<u8> {
    render(trace_print_tokens(ss))
}

/// Every name in every step is a valid name.
pub open spec fn valid_steps(ss: SpecSteps) -> bool {
    forall|i: int, m: int| 0 <= i < ss.len() && 0 <= m < ss[i].len() ==> valid_name(#[trigger] ss[i][m])
}

proof fn lemma_names_tokens(ts: Seq<SpecToken>, i: nat, ns: Seq<Seq<u8>>)
    requires
        ns.len() >= 1,
        i + names_tokens(ns).len() + 1 <= ts.len(),
        ts.subrange(i as int, (i + names_tokens(ns).len() + 1) as int) == names_tokens(ns) + seq![Token::RBrace],
    ensures
        names_at(ts, i) == Some((ns, i + names_tokens(ns).len() + 1)),
    decreases ns.len(),
{
    let x = names_tokens(ns) + seq![Token::<Seq<u8>>::RBrace];
    assert(ts[i as int] == x[0]);
    assert(ts[(i + 1) as int] == x[1]);
    if ns.len() > 1 {
        let rest = ns.drop_first();
        let y = names_tokens(rest) + seq![Token::<Seq<u8>>::RBrace];
        assert(x =~= seq![Token::Name(ns[0]), Token::Comma] + y);
        assert(ts.subrange((i + 2) as int, (i + 2 + y.len()) as int) =~= x.subrange(2, x.len() as int));
        assert(x.subrange(2, x.len() as int) =~= y);
        lemma_names_tokens(ts, i + 2, rest);
        assert(seq![ns[0]] + rest =~= ns);
    } else {
        assert(ns =~= seq![ns[0]]);
    }
}

proof fn lemma_step_tokens(ts: Seq<SpecToken>, i: nat, ns: Seq<Seq<u8>>)
    requires
        i + step_tokens(ns).len() <= ts.len(),
        ts.subrange(i as int, (i + step_tokens(ns).len()) as int) == step_tokens(ns),
    ensures
        step_at(ts, i) == Some((ns, i + step_tokens(ns).len())),
{
    let x = step_tokens(ns);
    assert(ts[i as int] == x[0]);
    assert(ts[(i + 1) as int] == x[1]);
    if ns.len() == 0 {
        assert(names_tokens(ns) =~= Seq::<SpecToken>::empty());
        assert(ns =~= Seq::<Seq<u8>>::empty());
    } else {
        let y = names_tokens(ns) + seq![Token::<Seq<u8>>::RBrace];
        assert(x =~= seq![Token::LBrace] + y);
        assert(ts.subrange((i + 1) as int, (i + 1 + y.len()) as int) =~= x.subrange(1, x.len() as int));
        assert(x.subrange(1, x.len() as int) =~= y);
        assert(names_tokens(ns)[0] == Token::<Seq<u8>>::Name(ns[0]));
        assert(x[1] == names_tokens(ns)[0]);
        lemma_names_tokens(ts, i + 1, ns);
    }
}

proof fn lemma_steps_tokens(ts: Seq<SpecToken>, i: nat, ss: SpecSteps)
    requires
        ss.len() >= 1,
        i + steps_tokens(ss).len() + 1 <= ts.len(),
        ts.subrange(i as int, (i + steps_tokens(ss).len() + 1) as int) == steps_tokens(ss) + seq![Token::RBrack],
    ensures
        steps_at(ts, i) == Some((ss, i + steps_tokens(ss).len() + 1)),
    decreases ss.len(),
{
    let x = steps_tokens(ss) + seq![Token::<Seq<u8>>::RBrack];
    let st = step_tokens(ss[0]);
    let e = i + st.len();
    if ss.len() == 1 {
        assert(x =~= st + seq![Token::RBrack]);
        assert(ts.subrange(i as int, e as int) =~= x.subrange(0, st.len() as int));
        assert(x.subrange(0, st.len() as int) =~= st);
        lemma_step_tokens(ts, i, ss[0]);
        assert(ts[e as int] == x[st.len() as int]);
        assert(ss =~= seq![ss[0]]);
    } else {
        let rest = ss.drop_first();
        let y = steps_tokens(rest) + seq![Token::<Seq<u8>>::RBrack];
        assert(x =~= st + seq![Token::Comma] + y);
        assert(ts.subrange(i as int, e as int) =~= x.subrange(0, st.len() as int));
        assert(x.subrange(0, st.len() as int) =~= st);
        lemma_step_tokens(ts, i, ss[0]);
        assert(ts[e as int] == x[st.len() as int]);
        assert(ts.subrange((e + 1) as int, (e + 1 + y.len()) as int) =~= x.subrange((st.len() + 1) as int, x.len() as int));
        assert(x.subrange((st.len() + 1) as int, x.len() as int) =~= y);
        lemma_steps_tokens(ts, e + 1, rest);
        assert(seq![ss[0]] + rest =~= ss);
    }
}

proof fn lemma_steps_tokens_nonempty(ss: SpecSteps)
    requires
        ss.len() >= 1,
    ensures
        steps_tokens(ss).len() >= 2,
        steps_tokens(ss)[0] is LBrace,
{
    if ss.len() > 1 {
        assert((step_tokens(ss[0]) + seq![Token::<Seq<u8>>::Comma] + steps_tokens(ss.drop_first()))[0] == step_tokens(ss[0])[0]);
    }
}

proof fn lemma_valid_names_tokens(ns: Seq<Seq<u8>>)
    requires
        forall|m: int| 0 <= m < ns.len() ==> valid_name(#[trigger] ns[m]),
    ensures
        valid_tokens(names_tokens(ns)),
    decreases ns.len(),
{
    if ns.len() > 1 {
        let rest = ns.drop_first();
        assert forall|m: int| 0 <= m < rest.len() implies valid_name(#[trigger] rest[m]) by { assert(rest[m] == ns[m + 1]); }
        lemma_valid_names_tokens(rest);
        lemma_valid_concat(seq![Token::Name(ns[0]), Token::Comma], names_tokens(rest));
    }
}

proof fn lemma_valid_steps_tokens(ss: SpecSteps)
    requires
        valid_steps(ss),
    ensures
        valid_tokens(steps_tokens(ss)),
    decreases ss.len(),
{
    if ss.len() >= 1 {
        let ns = ss[0];
        assert forall|m: int| 0 <= m < ns.len() implies valid_name(#[trigger] ns[m]) by { assert(valid_name(ss[0][m])); }
        lemma_valid_names_tokens(ns);
        lemma_valid_concat(seq![Token::LBrace], names_tokens(ns));
        lemma_valid_concat(seq![Token::LBrace] + names_tokens(ns), seq![Token::RBrace]);
        if ss.len() > 1 {
            let rest = ss.drop_first();
            assert forall|i: int, m: int| 0 <= i < rest.len() && 0 <= m < rest[i].len() implies valid_name(#[trigger] rest[i][m]) by {
                assert(rest[i] == ss[i + 1]);
                assert(valid_name(ss[i + 1][m]));
            }
            lemma_valid_steps_tokens(rest);
            lemma_valid_concat(step_tokens(ns), seq![Token::Comma]);
            lemma_valid_concat(step_tokens(ns) + seq![Token::Comma], steps_tokens(rest));
        }
    }
}

/// **Round trip.** The printed text of steps with valid names denotes
/// exactly those steps.
pub proof fn lemma_trace_round_trip(ss: SpecSteps)
    requires
        valid_steps(ss),
    ensures
        trace_denotes(trace_text(ss), ss),
{
    let ts = trace_print_tokens(ss);
    let s = render(ts);
    lemma_valid_steps_tokens(ss);
    lemma_valid_concat(seq![Token::LBrack], steps_tokens(ss));
    lemma_valid_concat(seq![Token::LBrack] + steps_tokens(ss), seq![Token::RBrack]);
    assert(s.subrange(0, s.len() as int) =~= s);
    lemma_lex_render(s, 0, ts);
    if ss.len() == 0 {
        assert(steps_tokens(ss) =~= Seq::<SpecToken>::empty());
        assert(ts =~= seq![Token::LBrack, Token::RBrack]);
        assert(ss =~= Seq::<Seq<Seq<u8>>>::empty());
    } else {
        lemma_steps_tokens_nonempty(ss);
        let y = steps_tokens(ss) + seq![Token::<Seq<u8>>::RBrack];
        assert(ts =~= seq![Token::LBrack] + y);
        assert(ts.subrange(1, (1 + y.len()) as int) =~= y);
        lemma_steps_tokens(ts, 1, ss);
        assert(ts[1] == steps_tokens(ss)[0]);
    }
}

fn push_tok(t: Token<Vec<u8>>, out: &mut Vec<Token<Vec<u8>>>)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@) + seq![token_view(t)],
{
    let ghost before = tokens_view(out@);
    out.push(t);
    proof { assert(tokens_view(out@) =~= before + seq![token_view(t)]); }
}

/// Appends `step_tokens(ns)`.
fn push_step_tokens(ns: &Vec<Vec<u8>>, out: &mut Vec<Token<Vec<u8>>>)
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@) + step_tokens(names_view(ns@)),
{
    let ghost before = tokens_view(out@);
    let ghost nv = names_view(ns@);
    push_tok(Token::LBrace, out);
    let mut m = 0;
    while m < ns.len()
        invariant
            m <= ns.len(), nv == names_view(ns@),
            tokens_view(out@) == before + seq![Token::LBrace] + names_tokens(nv.subrange(0, m as int)),
        decreases ns.len() - m,
    {
        let ghost pre = nv.subrange(0, m as int);
        if m > 0 {
            push_tok(Token::Comma, out);
        }
        push_tok(Token::Name(copy_vec(&ns[m])), out);
        proof { lemma_names_tokens_push(pre, nv[m as int]); assert(nv.subrange(0, m + 1) =~= pre.push(nv[m as int])); }
        m = m + 1;
    }
    push_tok(Token::RBrace, out);
    proof { assert(nv.subrange(0, ns.len() as int) =~= nv); }
}

/// `names_tokens` grows at the end.
proof fn lemma_names_tokens_push(ns: Seq<Seq<u8>>, n: Seq<u8>)
    ensures
        names_tokens(ns.push(n)) == if ns.len() == 0 { seq![Token::Name(n)] } else { names_tokens(ns) + seq![Token::Comma, Token::Name(n)] },
    decreases ns.len(),
{
    if ns.len() == 0 {
        assert(ns.push(n) =~= seq![n]);
    } else if ns.len() == 1 {
        assert(ns.push(n).drop_first() =~= seq![n]);
        assert(ns.push(n)[0] == ns[0]);
        assert(names_tokens(seq![n]) == seq![Token::<Seq<u8>>::Name(n)]);
        assert(names_tokens(ns.push(n)) =~= seq![Token::Name(ns[0]), Token::Comma] + seq![Token::Name(n)]);
        assert(names_tokens(ns) == seq![Token::Name(ns[0])]);
        assert(names_tokens(ns.push(n)) =~= names_tokens(ns) + seq![Token::Comma, Token::Name(n)]);
    } else {
        let rest = ns.drop_first();
        assert(ns.push(n).drop_first() =~= rest.push(n));
        assert(ns.push(n)[0] == ns[0]);
        lemma_names_tokens_push(rest, n);
        assert(names_tokens(ns.push(n)) =~= names_tokens(ns) + seq![Token::Comma, Token::Name(n)]);
    }
}

/// `steps_tokens` grows at the end.
proof fn lemma_steps_tokens_push(ss: SpecSteps, s: Seq<Seq<u8>>)
    ensures
        steps_tokens(ss.push(s)) == if ss.len() == 0 { step_tokens(s) } else { steps_tokens(ss) + seq![Token::Comma] + step_tokens(s) },
    decreases ss.len(),
{
    if ss.len() == 0 {
        assert(ss.push(s) =~= seq![s]);
    } else if ss.len() == 1 {
        assert(ss.push(s).drop_first() =~= seq![s]);
        assert(ss.push(s)[0] == ss[0]);
        assert(steps_tokens(seq![s]) == step_tokens(s));
        assert(steps_tokens(ss) == step_tokens(ss[0]));
    } else {
        let rest = ss.drop_first();
        assert(ss.push(s).drop_first() =~= rest.push(s));
        assert(ss.push(s)[0] == ss[0]);
        lemma_steps_tokens_push(rest, s);
        assert(steps_tokens(ss.push(s)) =~= steps_tokens(ss) + seq![Token::Comma] + step_tokens(s));
    }
}

/// Print steps in the sets syntax: `[{a, b}, {}]`. If every name is valid,
/// the text denotes exactly these steps ([`parse_trace`] returns them).
pub fn print_trace(ss: &ExecSteps) -> (r: Vec<u8>)
    ensures
        r@ == trace_text(steps_view(ss@)),
        valid_steps(steps_view(ss@)) ==> trace_denotes(r@, steps_view(ss@)),
{
    let ghost sv = steps_view(ss@);
    let mut ts: Vec<Token<Vec<u8>>> = Vec::new();
    proof { assert(tokens_view(ts@) =~= Seq::<SpecToken>::empty()); }
    push_tok(Token::LBrack, &mut ts);
    let mut i = 0;
    while i < ss.len()
        invariant
            i <= ss.len(), sv == steps_view(ss@),
            tokens_view(ts@) == seq![Token::LBrack] + steps_tokens(sv.subrange(0, i as int)),
        decreases ss.len() - i,
    {
        let ghost pre = sv.subrange(0, i as int);
        if i > 0 {
            push_tok(Token::Comma, &mut ts);
        }
        push_step_tokens(&ss[i], &mut ts);
        proof {
            assert(sv[i as int] == names_view(ss@[i as int]@));
            lemma_steps_tokens_push(pre, sv[i as int]);
            assert(sv.subrange(0, i + 1) =~= pre.push(sv[i as int]));
            if i == 0 { assert(pre =~= Seq::<Seq<Seq<u8>>>::empty()); }
        }
        i = i + 1;
    }
    push_tok(Token::RBrack, &mut ts);
    proof { assert(sv.subrange(0, ss.len() as int) =~= sv); assert(tokens_view(ts@) =~= trace_print_tokens(sv)); }
    let r = exec_render(&ts);
    proof {
        if valid_steps(sv) { lemma_trace_round_trip(sv); }
    }
    r
}

} // verus!
