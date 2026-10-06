//! The front door to the verified MLTL crates: text in, text out.
//!
//! Every function here calls one verified function, and says which; that
//! function's `ensures` clause is the guarantee.
//!
//! # Example
//!
//! Parse formulas and traces in one [`Context`], so a name means the
//! same atom everywhere, then use any algorithm and print the result:
//!
//! ```
//! use mltl::Context;
//!
//! let mut cx = Context::new();
//! let f = cx.parse_formula("G[0,2] (request -> F[0,1] grant)")?;
//!
//! // The true atoms at each time step.
//! let trace = cx.parse_trace("[{request}, {grant}, {}]")?;
//! assert!(mltl::eval(&f, &trace));
//!
//! // Progression: what the rest of the trace must satisfy after step 0
//! // (shown in negation normal form, which is easier to read).
//! let rest = mltl::progress(&f, &trace[..1]);
//! assert_eq!(cx.display(&mltl::nnf(&rest)).to_string(), "F[0,0] grant & G[0,1] (!request | F[0,1] grant)");
//!
//! // Partitioning: formulas that together say the same as `F[0,2] grant`,
//! // no two of which hold on the same trace.
//! let g = cx.parse_formula("F[0,2] grant")?;
//! let parts: Vec<String> = mltl::partition(&g, 1, 1)?.iter().map(|p| cx.display(p).to_string()).collect();
//! assert_eq!(parts, ["F[0,0] grant", "G[0,0] !grant & F[1,1] grant", "G[0,1] !grant & F[2,2] grant"]);
//! # Ok::<(), mltl::Error>(())
//! ```
//!
//! # Traces
//!
//! Traces are written as one set of true atoms per step, or in R2U2's CSV
//! format; both read into the same trace, and print back as sets:
//!
//! ```
//! let mut cx = mltl::Context::new();
//! let f = cx.parse_formula("G[0,2] (request -> F[0,1] grant)")?;
//! let t = cx.parse_csv("# request,grant,fault\n1,0,0\n0,1,1\n0,0,0\n")?;
//! assert_eq!(cx.display(&t).to_string(), "[{request}, {grant, fault}, {}]");
//! assert_eq!(t, cx.parse_trace("[{request}, {grant, fault}, {}]")?);
//!
//! // `fault` is not in the formula: allowed, with a warning.
//! let w = cx.unused(&f, &t).unwrap();
//! assert_eq!(w.to_string(), "warning: atom `fault` is not used in the formula and doesn't affect the result");
//! # Ok::<(), mltl::Error>(())
//! ```
//!
//! # WEST, satisfiability, monitoring
//!
//! ```
//! let mut cx = mltl::Context::new();
//!
//! // WEST: regular expressions for exactly the traces that satisfy a formula
//! // (one column per atom: `1` true, `0` false, `s` either).
//! let f = cx.parse_formula("F[0,2] grant")?;
//! assert_eq!(cx.west(&f)?, "# grant\ns,s,1\ns,1,s\n1,s,s\n");
//!
//! // Runtime monitoring with R2U2: verdicts arrive as soon as they are
//! // known; `(v, t)` covers every step after the previous verdict up to `t`.
//! let g = cx.parse_formula("!grant")?;
//! let t = cx.parse_trace("[{grant}, {grant}, {}]")?;
//! let v = mltl::monitor(&g, &t)?;
//! assert_eq!(v.iter().map(|x| (x.val, x.time)).collect::<Vec<_>>(), [(false, 0), (false, 1), (true, 2)]);
//! assert_eq!(mltl::value_at(&v, 2), Some(true));
//! # Ok::<(), mltl::Error>(())
//! ```
//!
//! Satisfiability needs the SAT solver CaDiCaL (`cadical` on the `PATH`):
//!
//! ```no_run
//! let mut cx = mltl::Context::new();
//! let f = cx.parse_formula("F[0,3] (request & G[1,2] !grant)")?;
//! match mltl::sat(&f)? {
//!     mltl::Sat::Sat(t) => println!("satisfied by {}", cx.display(&t)),
//!     mltl::Sat::Unsat => println!("unsatisfiable"),
//!     mltl::Sat::Unknown => println!("the solver's answer could not be checked"),
//! }
//! let never = cx.parse_formula("request & !request")?;
//! assert_eq!(mltl::sat(&never)?, mltl::Sat::Unsat);
//! # Ok::<(), mltl::Error>(())
//! ```
//!
//! Errors print like cargo's:
//!
//! ```
//! let mut cx = mltl::Context::new();
//! let Err(e) = cx.parse_formula("p U[0,2] q U[0,3] r") else { unreachable!() };
//! assert!(e.to_string().starts_with("error: `U` and `R` can't be chained without parentheses"));
//! ```
//!
//! # The crates behind it
//!
//! | Here | Verified function | Crate |
//! |---|---|---|
//! | [`Context::parse_formula`], [`Context::trace`], [`Context::display`] | `Atoms::parse`, `Atoms::trace`, `Atoms::print` | [`mltl_parse`] |
//! | [`Context::parse_trace`], [`Context::parse_csv`], [`Context::display`] | `Atoms::parse_trace`, `Atoms::parse_csv`, `Atoms::print_trace` | [`mltl_parse`] |
//! | [`eval`] | `BitTrace::from_sets`, then `mltl_eval_bottom_up_bits` | [`mltl_eval`] |
//! | [`progress`], [`progress_afp`] | `prog`, `formula_progression` | [`formula_progression`] |
//! | [`partition`], [`partition_with`] | `with_width` / `with_compositions`, then `LP_mltl` | [`language_partitioning`] |
//! | [`nnf`], [`bnf`] | `convert_nnf`, `convert_bnf` | [`mltl_core`] |
//! | [`Context::west`] | `fast_reg_checked`, `trace_to_text` | [`west`] |
//! | [`sat`] | `solve` | [`mltl_sat`] |
//! | [`monitor`], [`Monitor`] | `monitor_trace`, `Monitor` | [`r2u2`] |
use std::collections::HashSet;
use std::fmt;

pub use formula_progression;
pub use language_partitioning;
pub use mltl_core;
pub use mltl_eval;
pub use mltl_parse;
pub use mltl_sat;
pub use r2u2;
pub use west;

pub use mltl_core::mltl::Mltl;
pub use mltl_parse::ParseError;
/// An R2U2 verdict: `val` holds at every step after the previous verdict's
/// `time`, up to and including `time`.
pub use r2u2::exec::ExVerdict as Verdict;

/// A formula with numbered atoms, as the algorithms take it.
pub type Formula = Mltl<usize>;

/// A trace: the numbers of the true atoms at each time step.
pub type Trace = Vec<HashSet<usize>>;

/// A formula read by [`Context::parse_formula`], together with the text it was
/// read from. It works wherever a [`Formula`] is expected (`&parsed` turns
/// into `&Formula`), and [`Context::display`] shows the original text.
#[derive(Debug)]
pub struct Parsed {
    text: String,
    formula: Formula,
}

impl Parsed {
    /// The text the formula was read from, exactly as given.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// The formula, without its text.
    pub fn into_formula(self) -> Formula {
        self.formula
    }
}

impl std::ops::Deref for Parsed {
    type Target = Formula;
    fn deref(&self) -> &Formula {
        &self.formula
    }
}

impl AsRef<Formula> for Parsed {
    fn as_ref(&self) -> &Formula {
        &self.formula
    }
}

impl From<Parsed> for Formula {
    fn from(p: Parsed) -> Formula {
        p.formula
    }
}

/// What went wrong.
pub enum Error {
    /// The text is not a formula, or its atoms can't be numbered.
    Parse { text: String, error: ParseError },
    /// A trace's atom can't be numbered: a `pN` that may clash with a named
    /// atom, or the numbers ran out.
    Numbering { step: usize, name: String, error: mltl_parse::ErrorKind },
    /// Partitioning: an interval split doesn't fit (see [`partition`] and
    /// [`partition_with`]).
    BadSplit,
    /// A formula built by hand has an interval `[a, b]` with `a > b` (the
    /// parser never returns one).
    BadInterval,
    /// The problem is too large for machine integers (WEST's bit layout,
    /// the SAT encoding's variables, or R2U2's time stamps).
    TooLarge,
    /// The SAT solver CaDiCaL could not be run: install `cadical` on the
    /// `PATH`, or set `$CADICAL` to its path.
    SolverMissing,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse { text, error } => write!(f, "{}", error.render(text.as_bytes(), "<input>")),
            Error::Numbering { step, name, error } => match error {
                mltl_parse::ErrorKind::NumberTaken => write!(
                    f,
                    "error: atom `{name}` at step {step} may clash with a named atom\n  \
                     = help: use only names, or parse the formula with the largest `pN` first"
                ),
                _ => write!(f, "error: atom numbers ran out at `{name}` (step {step})"),
            },
            Error::BadSplit => write!(f, "error: an interval split doesn't fit its interval"),
            Error::BadInterval => write!(f, "error: an interval `[a,b]` has a > b"),
            Error::TooLarge => write!(f, "error: the problem is too large for machine integers"),
            Error::SolverMissing => write!(
                f,
                "error: CaDiCaL not found\n  = help: install `cadical` on the PATH, or set $CADICAL to its path"
            ),
        }
    }
}

// `main` returning `Err` and `.unwrap()` print `Debug` after a prefix
// (`Error: `); starting on a new line keeps the message whole.
impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;
        fmt::Display::fmt(self, f)
    }
}

impl std::error::Error for Error {}

/// The context formulas and traces are read and printed in: the table of
/// atom names and their numbers, shared by everything parsed with it, so a
/// name means the same atom everywhere. Wraps [`mltl_parse::Atoms`].
///
/// Atoms are numbered as in the parser's grammar: `pN` is atom N, and every
/// other name gets the next free number when first seen. Different names
/// always get different numbers, and a name keeps its number.
pub struct Context(mltl_parse::Atoms);

impl Default for Context {
    fn default() -> Self {
        Context::new()
    }
}

impl Context {
    /// An empty context: no names yet.
    pub fn new() -> Self {
        Context(mltl_parse::Atoms::new())
    }

    /// Parse a formula (syntax: `mltl-parse`'s GRAMMAR.md) and number its
    /// atoms. The result is exactly the formula the text denotes, and keeps
    /// the text: [`Context::display`] shows it as typed. An error means the
    /// text is not a formula, or a `pN` clashes with the numbers already
    /// given to names.
    pub fn parse_formula(&mut self, text: &str) -> Result<Parsed, Error> {
        let formula = self.0.parse(text.as_bytes()).map_err(|error| Error::Parse { text: text.to_string(), error })?;
        Ok(Parsed { text: text.to_string(), formula })
    }

    /// A trace from the names of the true atoms at each step. Names the
    /// context doesn't have yet get numbers. On the names in the context, the
    /// result agrees with the named trace, so formulas have the same truth
    /// value on both.
    pub fn trace<S, I>(&mut self, steps: impl IntoIterator<Item = I>) -> Result<Trace, Error>
    where
        S: AsRef<str>,
        I: IntoIterator<Item = S>,
    {
        let steps: Vec<Vec<Vec<u8>>> = steps
            .into_iter()
            .map(|s| s.into_iter().map(|n| n.as_ref().as_bytes().to_vec()).collect())
            .collect();
        self.0.trace(&steps).map_err(|(i, j, error)| Error::Numbering {
            step: i,
            name: String::from_utf8_lossy(&steps[i][j]).into_owned(),
            error,
        })
    }

    /// Read a trace written as one set of true atoms per step,
    /// `[{request}, {grant, ok}, {}]` (syntax: `mltl-parse`'s GRAMMAR.md §6).
    /// Names the context doesn't have yet get numbers. The result agrees with
    /// the text on every name, so formulas have the same truth value on both.
    pub fn parse_trace(&mut self, text: &str) -> Result<Trace, Error> {
        self.0.parse_trace(text.as_bytes()).map_err(|error| Error::Parse { text: text.to_string(), error })
    }

    /// [`Context::parse_trace`] for R2U2's CSV format: a header `# a,b`, then
    /// one row of `0`/`1` per step.
    pub fn parse_csv(&mut self, text: &str) -> Result<Trace, Error> {
        self.0.parse_csv(text.as_bytes()).map_err(|error| Error::Parse { text: text.to_string(), error })
    }

    /// Show a formula or a trace with this context's names, for `{}` in
    /// `println!` and `format!` (or `.to_string()`), like `Path::display`.
    /// A formula from [`Context::parse_formula`] shows its text as typed. Other
    /// formulas (results of the algorithms) are printed, like
    /// `G[0,2] (!request | F[0,1] grant)` (`pN` for numbers without a name;
    /// `a -> b` prints as `!a | b`, which is what it means). A trace shows
    /// as `[{request}, {grant, ok}, {}]`. Reading the text back in this
    /// context ([`Context::parse_formula`], [`Context::parse_trace`]) gives the same
    /// formula or trace.
    pub fn display<'a, T: Show + ?Sized>(&'a self, x: &'a T) -> Displayed<'a, T> {
        Displayed { cx: self, x }
    }

    fn trace_text(&self, trace: &[HashSet<usize>]) -> String {
        // Every atom is below the bound, so every atom is printed.
        let bound = trace.iter().flatten().max().map_or(0, |&m| m + 1);
        // The printer only emits ASCII.
        String::from_utf8(self.0.print_trace(&trace.to_vec(), bound)).expect("printer output is ASCII")
    }

    /// WEST: regular expressions that together match exactly the traces
    /// satisfying `f`, in WEST's text format after a header naming the
    /// columns. One line per expression; steps are separated by commas,
    /// with one character per atom: `1` true, `0` false, `s` either.
    ///
    /// ```text
    /// # request,grant
    /// 0s,0s,0s,ss
    /// ss,s1,0s,ss
    /// ```
    ///
    /// Column `k` is atom number `k`, so every number below the largest
    /// atom of `f` has a column (unused ones are always `s`). Guaranteed:
    /// a trace at least `complen(f)` long satisfies `f` exactly when it
    /// matches one of the lines.
    pub fn west(&self, f: &Formula) -> Result<String, Error> {
        if !r2u2::exec_engine::intervals_welldef_ex(f) {
            return Err(Error::BadInterval);
        }
        let r = west::api::fast_reg_checked(f).ok_or(Error::TooLarge)?;
        let names: Vec<String> = (0..r.n).map(|k| self.formula_text(&Mltl::Prop(k))).collect();
        let mut out = format!("# {}\n", names.join(","));
        for i in 0..r.traces.len() {
            // WEST text is ASCII.
            out.push_str(&String::from_utf8(west::api::trace_to_text(&r, i)).expect("WEST text is ASCII"));
            out.push('\n');
        }
        Ok(out)
    }

    /// The atoms of `trace` that `f` doesn't use, as a warning (`None` if
    /// there are none). They can't change any result about `f` (proved:
    /// `lemma_semantics_own_atoms` in mltl-core), so this only helps catch
    /// typos.
    pub fn unused(&self, f: &Formula, trace: &[HashSet<usize>]) -> Option<Warning> {
        let used = atoms_of(f);
        let mut extra: Vec<usize> = trace.iter().flatten().copied().filter(|a| !used.contains(a)).collect();
        extra.sort_unstable();
        extra.dedup();
        if extra.is_empty() {
            return None;
        }
        Some(Warning::UnusedAtoms(extra.into_iter().map(|a| self.formula_text(&Mltl::Prop(a))).collect()))
    }

    /// The number of an atom name, if the context has it.
    pub fn atom(&self, name: &str) -> Option<usize> {
        self.0.atom(&name.as_bytes().to_vec())
    }

    fn formula_text(&self, f: &Formula) -> String {
        // The printer only emits ASCII.
        String::from_utf8(self.0.print(f)).expect("printer output is ASCII")
    }
}

/// What [`Context::display`] can show: a [`Parsed`] formula, a [`Formula`],
/// or a trace.
pub trait Show: sealed::Sealed {
    #[doc(hidden)]
    fn text(&self, cx: &Context) -> String;
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for super::Parsed {}
    impl Sealed for super::Formula {}
    impl Sealed for [std::collections::HashSet<usize>] {}
    impl Sealed for Vec<std::collections::HashSet<usize>> {}
}

impl Show for Parsed {
    fn text(&self, _cx: &Context) -> String {
        self.text.clone()
    }
}

impl Show for Formula {
    fn text(&self, cx: &Context) -> String {
        cx.formula_text(self)
    }
}

impl Show for [HashSet<usize>] {
    fn text(&self, cx: &Context) -> String {
        cx.trace_text(self)
    }
}

impl Show for Vec<HashSet<usize>> {
    fn text(&self, cx: &Context) -> String {
        cx.trace_text(self)
    }
}

/// A formula or trace with a context's names, ready for `{}`; made by
/// [`Context::display`].
pub struct Displayed<'a, T: ?Sized> {
    cx: &'a Context,
    x: &'a T,
}

impl<T: Show + ?Sized> fmt::Display for Displayed<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.x.text(self.cx))
    }
}

/// Something worth telling the user that is not an error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Warning {
    /// Atoms of a trace that the formula doesn't use (see [`Context::unused`]).
    UnusedAtoms(Vec<String>),
}

impl fmt::Display for Warning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Warning::UnusedAtoms(names) => {
                let list: Vec<String> = names.iter().map(|n| format!("`{n}`")).collect();
                if names.len() == 1 {
                    write!(f, "warning: atom {} is not used in the formula and doesn't affect the result", list[0])
                } else {
                    write!(f, "warning: atoms {} are not used in the formula and don't affect the result", list.join(", "))
                }
            }
        }
    }
}

/// The atoms of a formula.
fn atoms_of(f: &Formula) -> HashSet<usize> {
    fn go(f: &Formula, out: &mut HashSet<usize>) {
        match f {
            Mltl::True | Mltl::False => {}
            Mltl::Prop(a) => {
                out.insert(*a);
            }
            Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => go(g, out),
            Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) => {
                go(g, out);
                go(h, out);
            }
        }
    }
    let mut out = HashSet::new();
    go(f, &mut out);
    out
}

/// Whether the trace satisfies the formula (AFP semantics; steps past the
/// end of the trace count as empty). Bottom-up evaluation: linear in trace
/// length times formula size. The trace is first packed into one bit row per
/// atom (`BitTrace::from_sets`, proved to keep its meaning), which is about
/// 4× faster to evaluate on large traces than the sets themselves.
pub fn eval(f: &Formula, trace: &[HashSet<usize>]) -> bool {
    // `from_sets` needs every atom of the trace below the bound.
    let bound = trace.iter().flatten().max().map_or(0, |&m| m + 1);
    let bits = mltl_eval::BitTrace::from_sets(trace, bound);
    mltl_eval::mltl_eval_bottom_up_bits(f, &bits)
}

/// Progress `f` over a trace prefix, simplifying as it goes: on every
/// non-empty continuation `rho`, the result holds iff `prefix ++ rho`
/// satisfies `f`. A result of `True` or `False` is a final verdict.
pub fn progress(f: &Formula, prefix: &[HashSet<usize>]) -> Formula {
    formula_progression::extended::prog(f, prefix)
}

/// [`progress`] without simplification: the AFP algorithm exactly as
/// published (its formulas grow with every step).
pub fn progress_afp(f: &Formula, prefix: &[HashSet<usize>]) -> Formula {
    formula_progression::algorithm::formula_progression(f, prefix)
}

/// Partition `f` into formulas that together hold exactly when `f` does
/// (on traces at least `wpd(f)` long), splitting every interval into
/// blocks of `width` steps and recursing `depth` levels into subformulas.
/// With `width = 1` or `depth = 1`, no two of the formulas hold on the same
/// such trace.
///
/// `Err(BadSplit)` if `width` is 0, or an interval is `[0, usize::MAX]`.
pub fn partition(f: &Formula, width: usize, depth: usize) -> Result<Vec<Formula>, Error> {
    if width == 0 {
        return Err(Error::BadSplit);
    }
    let t = language_partitioning::splits::with_width(f, width).ok_or(Error::BadSplit)?;
    Ok(language_partitioning::exec::LP_mltl(&t, depth))
}

/// [`partition`] with an explicit split per temporal operator, in reading
/// order (operator before its operands, left before right): each is a list
/// of positive block widths summing to the interval's length `b - a + 1`.
/// No two of the formulas hold on the same trace when every split is all
/// ones or `depth = 1`.
///
/// `Err(BadSplit)` if the number of splits is not the number of temporal
/// operators, or a split doesn't fit its interval.
///
/// The splits can be written as arrays when they have the same length, and
/// as vectors otherwise:
///
/// ```
/// let mut cx = mltl::Context::new();
/// let f = cx.parse_formula("F[0,3] (p U[0,1] q)")?;
/// let a = mltl::partition_with(&f, [[2, 2], [1, 1]], 1)?;
/// let b = mltl::partition_with(&f, [vec![2, 2], vec![1, 1]], 1)?;
/// let pieces: Vec<String> = a.iter().map(|p| cx.display(p).to_string()).collect();
/// assert_eq!(pieces, ["F[0,1] (p U[0,1] q)", "G[0,1] (!p R[0,1] !q) & F[2,3] (p U[0,1] q)"]);
/// assert_eq!(b.len(), 2);
///
/// // `F[0,3]` and `U[0,0]` need splits of different lengths.
/// let g = cx.parse_formula("F[0,3] (p U[0,0] q)")?;
/// assert_eq!(mltl::partition_with(&g, [vec![1, 3], vec![1]], 1)?.len(), 2);
/// # Ok::<(), mltl::Error>(())
/// ```
pub fn partition_with<S, I>(f: &Formula, splits: S, depth: usize) -> Result<Vec<Formula>, Error>
where
    S: IntoIterator<Item = I>,
    I: AsRef<[usize]>,
{
    let comps: Vec<Vec<usize>> = splits.into_iter().map(|s| s.as_ref().to_vec()).collect();
    let t = language_partitioning::splits::with_compositions(f, &comps).ok_or(Error::BadSplit)?;
    Ok(language_partitioning::exec::LP_mltl(&t, depth))
}

/// What [`sat`] found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sat {
    /// A trace of length `complen(f)` that satisfies `f`.
    Sat(Trace),
    /// No trace of length `complen(f)` satisfies `f`.
    Unsat,
    /// The solver's answer could not be checked (or it gave none).
    Unknown,
}

/// Is `f` satisfiable? Translates `f` to SAT, runs CaDiCaL, and checks its
/// answer with verified code: a satisfying trace is checked by the
/// evaluator, "unsatisfiable" by a verified checker of CaDiCaL's proof.
/// The solver itself is not trusted, so a wrong answer shows up as
/// [`Sat::Unknown`], never as a wrong [`Sat::Sat`] or [`Sat::Unsat`].
///
/// Needs `cadical` on the `PATH` (or `$CADICAL`); otherwise
/// [`Error::SolverMissing`].
pub fn sat(f: &Formula) -> Result<Sat, Error> {
    if !r2u2::exec_engine::intervals_welldef_ex(f) {
        return Err(Error::BadInterval);
    }
    let bin = std::env::var("CADICAL").unwrap_or_else(|_| "cadical".to_string());
    if std::process::Command::new(&bin).arg("--version").output().is_err() {
        return Err(Error::SolverMissing);
    }
    match mltl_sat::solve::solve(f) {
        Some((mltl_sat::solve::Answer::Sat(t), _)) => Ok(Sat::Sat(t)),
        Some((mltl_sat::solve::Answer::Unsat, _)) => Ok(Sat::Unsat),
        Some((mltl_sat::solve::Answer::Unknown, _)) => Ok(Sat::Unknown),
        None => Err(Error::TooLarge),
    }
}

/// Run the R2U2 monitor on a whole trace. Guaranteed: every verdict is the
/// truth value of `f` at the steps it covers, for every continuation of the
/// trace; and every step `t` with `t + wpd(f) < trace.len()` is covered
/// (`wpd` = the formula's worst-case delay). See [`Verdict`].
pub fn monitor(f: &Formula, trace: &[HashSet<usize>]) -> Result<Vec<Verdict>, Error> {
    if !r2u2::exec_engine::intervals_welldef_ex(f) {
        return Err(Error::BadInterval);
    }
    r2u2::exec_engine::monitor_trace(f, &trace.to_vec()).ok_or(Error::TooLarge)
}

/// The R2U2 monitor, fed one step at a time. Same guarantee as [`monitor`],
/// after every step.
pub struct Monitor(r2u2::exec_engine::Monitor);

impl Monitor {
    /// A monitor for `f`.
    pub fn new(f: &Formula) -> Result<Monitor, Error> {
        if !r2u2::exec_engine::intervals_welldef_ex(f) {
            return Err(Error::BadInterval);
        }
        r2u2::exec_engine::Monitor::new(f).map(Monitor).ok_or(Error::TooLarge)
    }

    /// Feed the atoms true at the next step. After an error the monitor
    /// stops.
    pub fn step(&mut self, state: &HashSet<usize>) -> Result<(), Error> {
        if self.0.step(state) { Ok(()) } else { Err(Error::TooLarge) }
    }

    /// Every verdict so far.
    pub fn verdicts(&self) -> &[Verdict] {
        self.0.verdicts()
    }

    /// The truth value of the formula at step `t`, once a verdict covers it.
    pub fn value_at(&self, t: usize) -> Option<bool> {
        value_at(self.verdicts(), t)
    }
}

/// The truth value at step `t` given by verdicts `v`: that of the first
/// verdict whose time is at least `t`, if any.
pub fn value_at(v: &[Verdict], t: usize) -> Option<bool> {
    v.iter().find(|x| x.time >= t).map(|x| x.val)
}

/// Negation normal form: negations pushed down to the atoms; same meaning.
pub fn nnf(f: &Formula) -> Formula {
    mltl_core::properties::convert_nnf(f)
}

/// Boolean normal form: only `true`, atoms, `!`, `&` and `U`; same meaning.
pub fn bnf(f: &Formula) -> Formula {
    mltl_core::properties::convert_bnf(f)
}
