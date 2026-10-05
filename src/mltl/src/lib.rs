//! The front door to the verified MLTL crates: text in, text out.
//!
//! Every function here calls one verified function, and says which; that
//! function's `ensures` clause is the guarantee.
//!
//! # Example
//!
//! Parse formulas and traces with one [`Atoms`] table, so a name means the
//! same atom everywhere, then use any algorithm and print the result:
//!
//! ```
//! use mltl::Atoms;
//!
//! let mut atoms = Atoms::new();
//! let f = atoms.parse("G[0,2] (request -> F[0,1] grant)")?;
//!
//! // One list of true atoms per time step.
//! let trace = atoms.trace([vec!["request"], vec!["grant"], vec![]])?;
//! assert!(mltl::eval(&f, &trace));
//!
//! // Progression: what the rest of the trace must satisfy after step 0
//! // (shown in negation normal form, which is easier to read).
//! let rest = mltl::progress(&f, &trace[..1]);
//! assert_eq!(atoms.print(&mltl::nnf(&rest)), "F[0,0] grant & G[0,1] (!request | F[0,1] grant)");
//!
//! // Partitioning: formulas that together say the same as `F[0,2] grant`,
//! // no two of which hold on the same trace.
//! let g = atoms.parse("F[0,2] grant")?;
//! let parts: Vec<String> = mltl::partition(&g, 1, 1)?.iter().map(|p| atoms.print(p)).collect();
//! assert_eq!(parts, ["F[0,0] grant", "G[0,0] !grant & F[1,1] grant", "G[0,1] !grant & F[2,2] grant"]);
//! # Ok::<(), mltl::Error>(())
//! ```
//!
//! Errors print like cargo's:
//!
//! ```
//! let mut atoms = mltl::Atoms::new();
//! let Err(e) = atoms.parse("p U[0,2] q U[0,3] r") else { unreachable!() };
//! assert!(e.to_string().starts_with("error: `U` and `R` can't be chained without parentheses"));
//! ```
//!
//! # The crates behind it
//!
//! | Here | Verified function | Crate |
//! |---|---|---|
//! | [`Atoms::parse`], [`Atoms::trace`], [`Atoms::print`] | `Atoms::parse`, `Atoms::trace`, `Atoms::print` | [`mltl_parse`] |
//! | [`eval`] | `mltl_eval_bottom_up` | [`mltl_eval`] |
//! | [`progress`], [`progress_afp`] | `prog`, `formula_progression` | [`formula_progression`] |
//! | [`partition`], [`partition_with`] | `with_width` / `with_compositions`, then `LP_mltl` | [`language_partitioning`] |
//! | [`nnf`], [`bnf`] | `convert_nnf`, `convert_bnf` | [`mltl_core`] |
use std::collections::HashSet;
use std::fmt;

pub use formula_progression;
pub use language_partitioning;
pub use mltl_core;
pub use mltl_eval;
pub use mltl_parse;

pub use mltl_core::mltl::Mltl;
pub use mltl_parse::ParseError;

/// A formula with numbered atoms, as the algorithms take it.
pub type Formula = Mltl<usize>;

/// A trace: the numbers of the true atoms at each time step.
pub type Trace = Vec<HashSet<usize>>;

/// What went wrong.
pub enum Error {
    /// The text is not a formula, or its atoms can't be numbered.
    Parse { text: String, error: ParseError },
    /// A trace names an atom that no formula parsed with the table has.
    UnknownAtom { step: usize, name: String },
    /// Partitioning: an interval split doesn't fit (see [`partition`] and
    /// [`partition_with`]).
    BadSplit,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse { text, error } => write!(f, "{}", error.render(text.as_bytes(), "<input>")),
            Error::UnknownAtom { step, name } => {
                write!(f, "error: unknown atom `{name}` at step {step}: no formula parsed with this table has it")
            }
            Error::BadSplit => write!(f, "error: an interval split doesn't fit its interval"),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl std::error::Error for Error {}

/// Atom names and their numbers, shared by every formula and trace parsed
/// with it. Wraps [`mltl_parse::Atoms`].
///
/// Atoms are numbered as in the parser's grammar: `pN` is atom N, and every
/// other name gets the next free number when first seen. Different names
/// always get different numbers, and a name keeps its number.
pub struct Atoms(mltl_parse::Atoms);

impl Default for Atoms {
    fn default() -> Self {
        Atoms::new()
    }
}

impl Atoms {
    /// An empty table.
    pub fn new() -> Self {
        Atoms(mltl_parse::Atoms::new())
    }

    /// Parse a formula (syntax: `mltl-parse`'s GRAMMAR.md) and number its
    /// atoms. The result is exactly the formula the text denotes; an error
    /// means the text is not a formula, or a `pN` clashes with the numbers
    /// already given to names.
    pub fn parse(&mut self, text: &str) -> Result<Formula, Error> {
        self.0.parse(text.as_bytes()).map_err(|error| Error::Parse { text: text.to_string(), error })
    }

    /// A trace from the names of the true atoms at each step. Every name
    /// must be in the table (parse the formulas first). On the names in the
    /// table, the result agrees with the named trace, so formulas have the
    /// same truth value on both.
    pub fn trace<S, I>(&self, steps: impl IntoIterator<Item = I>) -> Result<Trace, Error>
    where
        S: AsRef<str>,
        I: IntoIterator<Item = S>,
    {
        let steps: Vec<Vec<Vec<u8>>> = steps
            .into_iter()
            .map(|s| s.into_iter().map(|n| n.as_ref().as_bytes().to_vec()).collect())
            .collect();
        self.0.trace(&steps).map_err(|(i, j)| Error::UnknownAtom {
            step: i,
            name: String::from_utf8_lossy(&steps[i][j]).into_owned(),
        })
    }

    /// The number of an atom name, if the table has it.
    pub fn atom(&self, name: &str) -> Option<usize> {
        self.0.atom(&name.as_bytes().to_vec())
    }

    /// Print a formula with this table's names (`pN` for numbers without a
    /// name). Parsing the text with this table gives the formula back.
    pub fn print(&self, f: &Formula) -> String {
        // The printer only emits ASCII.
        String::from_utf8(self.0.print(f)).expect("printer output is ASCII")
    }
}

/// Whether the trace satisfies the formula (AFP semantics; steps past the
/// end of the trace count as empty). Bottom-up evaluation: linear in trace
/// length times formula size.
pub fn eval(f: &Formula, trace: &[HashSet<usize>]) -> bool {
    mltl_eval::mltl_eval_bottom_up(f, trace)
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
pub fn partition_with(f: &Formula, splits: &[&[usize]], depth: usize) -> Result<Vec<Formula>, Error> {
    let comps: Vec<Vec<usize>> = splits.iter().map(|s| s.to_vec()).collect();
    let t = language_partitioning::splits::with_compositions(f, &comps).ok_or(Error::BadSplit)?;
    Ok(language_partitioning::exec::LP_mltl(&t, depth))
}

/// Negation normal form: negations pushed down to the atoms; same meaning.
pub fn nnf(f: &Formula) -> Formula {
    mltl_core::properties::convert_nnf(f)
}

/// Boolean normal form: only `true`, atoms, `!`, `&` and `U`; same meaning.
pub fn bnf(f: &Formula) -> Formula {
    mltl_core::properties::convert_bnf(f)
}
