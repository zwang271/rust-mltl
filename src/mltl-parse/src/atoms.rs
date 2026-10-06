//! A table of atom names shared by several formulas and traces.
//!
//! Parse every formula and trace of one problem with the same [`Atoms`]: a
//! name then gets the same number everywhere, and different names get
//! different numbers. [`Atoms::print`] turns numbered results (of
//! evaluators, progression, partitioning, …) back into text with the names.
//! Numbering follows GRAMMAR.md §5: `pN` is atom N, other names get the
//! next free numbers in order of first appearance.
use vstd::prelude::*;
use std::collections::HashSet;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::lexer::*;
use crate::grammar::*;
use crate::parser::*;
use crate::printer::*;
use crate::numbering::*;
use crate::error::*;
use crate::trace::*;
use crate::csv::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// Atom names and their numbers.
///
/// Spec view: [`Atoms::names`] (every name numbered so far) and
/// [`Atoms::num`] (each name's number). Every method keeps the numbers of
/// names already in the table, and different names always have different
/// numbers ([`Atoms::injective`]).
pub struct Atoms {
    /// The non-`pN` names and their numbers (`table_ok` with `lo`, `next`).
    entries: Vec<(Vec<u8>, usize)>,
    /// Every `pN` seen has N < `lo`; names have numbers ≥ `lo`.
    lo: usize,
    /// The next free number for a name.
    next: usize,
    seen: Ghost<Set<Seq<u8>>>,
}

/// The names of a trace given as names: step `i` holds the names in `steps[i]`.
pub open spec fn named_trace(steps: Seq<Vec<Vec<u8>>>) -> Seq<Set<Seq<u8>>> {
    steps.map_values(|s: Vec<Vec<u8>>| s@.map_values(|v: Vec<u8>| v@).to_set())
}

/// The spec trace of a numbered trace.
pub open spec fn numbered_trace(t: Seq<HashSet<usize>>) -> Seq<Set<usize>> {
    t.map_values(|s: HashSet<usize>| s@)
}

/// Whether `n` is a name the printer can print (GRAMMAR.md §1).
pub(crate) fn exec_valid_name(n: &Vec<u8>) -> (r: bool)
    ensures
        r == valid_name(n@),
{
    let len = n.len();
    if len == 0 {
        return false;
    }
    let c0 = n[0];
    if !((65 <= c0 && c0 <= 90) || (97 <= c0 && c0 <= 122) || c0 == 95) {
        return false;
    }
    let mut k = 0;
    while k < len
        invariant
            k <= len, len == n.len(),
            forall|m: int| 0 <= m < k ==> is_word_char(#[trigger] n@[m]),
        decreases len - k,
    {
        let c = n[k];
        if !((65 <= c && c <= 90) || (97 <= c && c <= 122) || (48 <= c && c <= 57) || c == 95) {
            return false;
        }
        k = k + 1;
    }
    let kw = exec_keyword(n.as_slice(), 0, len);
    proof { assert(n@.subrange(0, len as int) =~= n@); }
    kw.is_none()
}

/// Every name in `steps` is in `s`.
pub open spec fn steps_in(steps: Seq<Vec<Vec<u8>>>, s: Set<Seq<u8>>) -> bool {
    forall|i: int, j: int| 0 <= i < steps.len() && 0 <= j < steps[i]@.len() ==> s.contains(#[trigger] steps[i]@[j]@)
}

/// The sets of a trace given as names (repeats don't matter).
pub open spec fn trace_sets(ss: SpecSteps) -> Seq<Set<Seq<u8>>> {
    ss.map_values(|s: Seq<Seq<u8>>| s.to_set())
}

proof fn lemma_trace_sets(steps: Seq<Vec<Vec<u8>>>)
    ensures
        named_trace(steps) == trace_sets(steps_view(steps)),
{
    assert(named_trace(steps) =~= trace_sets(steps_view(steps)));
}

/// Every name of `ss` is in `s`.
pub open spec fn sets_in(ss: SpecSteps, s: Set<Seq<u8>>) -> bool {
    forall|i: int, m: int| 0 <= i < ss.len() && 0 <= m < ss[i].len() ==> s.contains(#[trigger] ss[i][m])
}

/// The names of step `i` of `ss` are exactly the numbers `k < n` in step
/// `i` of `t`.
pub open spec fn printed_as(ss: SpecSteps, t: Seq<HashSet<usize>>, n: usize, num: spec_fn(Seq<u8>) -> usize) -> bool {
    &&& ss.len() == t.len()
    &&& forall|i: int, k: usize| 0 <= i < t.len() ==>
        ((#[trigger] t[i]@.contains(k) && k < n) <==> exists|m: int| 0 <= m < ss[i].len() && #[trigger] num(ss[i][m]) == k)
}

impl Atoms {
    /// Every name numbered so far.
    pub closed spec fn names(&self) -> Set<Seq<u8>> {
        self.seen@
    }

    /// The number of each name.
    pub closed spec fn num(&self) -> spec_fn(Seq<u8>) -> usize {
        numbering(table_view(self.entries@))
    }

    /// The internal invariant.
    pub closed spec fn wf(&self) -> bool {
        &&& table_ok(table_view(self.entries@), self.lo as nat, self.next as nat)
        &&& forall|n: Seq<u8>| #[trigger] self.seen@.contains(n) ==> match pnum(n) {
                Some(v) => v < self.lo,
                None => lookup(table_view(self.entries@), n) is Some,
            }
    }

    /// Different names have different numbers.
    pub open spec fn injective(&self) -> bool {
        forall|n1: Seq<u8>, n2: Seq<u8>| self.names().contains(n1) && self.names().contains(n2)
            && #[trigger] (self.num())(n1) == #[trigger] (self.num())(n2) ==> n1 == n2
    }

    /// `self` grew into `other`: no name lost, no number changed.
    pub open spec fn grows_to(&self, other: &Atoms) -> bool {
        &&& self.names().subset_of(other.names())
        &&& forall|n: Seq<u8>| #[trigger] self.names().contains(n) ==> (other.num())(n) == (self.num())(n)
    }

    proof fn lemma_injective(&self)
        requires
            self.wf(),
        ensures
            self.injective(),
    {
        let t = table_view(self.entries@);
        assert forall|n1: Seq<u8>, n2: Seq<u8>| self.names().contains(n1) && self.names().contains(n2)
            && #[trigger] (self.num())(n1) == #[trigger] (self.num())(n2) implies n1 == n2 by {
            assert(self.seen@.contains(n1) && self.seen@.contains(n2));
            match (pnum(n1), pnum(n2)) {
                (Some(v1), Some(v2)) => { lemma_pnum_injective(n1, n2); },
                (Some(v1), None) => {
                    let j2 = entry_index(t, n2);
                    assert(t[j2].1 >= self.lo);
                },
                (None, Some(v2)) => {
                    let j1 = entry_index(t, n1);
                    assert(t[j1].1 >= self.lo);
                },
                (None, None) => {
                    let (j1, j2) = (entry_index(t, n1), entry_index(t, n2));
                    if j1 != j2 { assert(t[j1].1 != t[j2].1); }
                },
            }
        }
    }

    /// An empty table.
    pub fn new() -> (r: Atoms)
        ensures
            r.wf(),
            r.injective(),
            r.names() == Set::<Seq<u8>>::empty(),
    {
        let r = Atoms { entries: Vec::new(), lo: 0, next: 0, seen: Ghost(Set::empty()) };
        proof {
            assert(table_view(r.entries@) =~= Seq::<(Seq<u8>, usize)>::empty());
            r.lemma_injective();
        }
        r
    }

    /// Number the atoms of `f`, adding its new names to the table.
    ///
    /// The result is `f` with every atom replaced by its number. Errors:
    /// [`ErrorKind::NumberTaken`] if a `pN` atom has N at or above the
    /// numbers already given to names (e.g. `p0` after `a` got 0);
    /// [`ErrorKind::NumberingFailed`] if N ≥ usize::MAX or the numbers run
    /// out. On error, no name is added.
    pub fn number(&mut self, f: &ExecFormula) -> (r: Result<Mltl<usize>, ErrorKind>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).injective(),
            old(self).grows_to(final(self)),
            r is Ok ==> r->Ok_0 == map_atoms(view_f(*f), final(self).num())
                && atoms_mltl(view_f(*f)).subset_of(final(self).names()),
            r is Err ==> final(self).names() == old(self).names()
                && (r->Err_0 is NumberTaken || r->Err_0 is NumberingFailed),
    {
        let ghost vf = view_f(*f);
        let ghost t0 = table_view(self.entries@);
        let ghost s0 = self.seen@;
        let ghost lo0 = self.lo;
        let b = match pn_bound(f) {
            Ok(b) => b,
            Err(()) => {
                proof { self.lemma_injective(); }
                return Err(ErrorKind::NumberingFailed);
            },
        };
        if b > self.lo {
            if self.entries.len() > 0 {
                proof { self.lemma_injective(); }
                return Err(ErrorKind::NumberTaken);
            }
            // No names yet, so every number so far is a `pN` below `lo`.
            self.lo = b;
            if self.next < b {
                self.next = b;
            }
            proof {
                assert(table_view(self.entries@) =~= t0);
                assert forall|n: Seq<u8>| #[trigger] s0.contains(n) implies pnum(n) is Some by {
                    if pnum(n) is None {
                        assert(lookup(t0, n) is Some);
                        assert(has_entry(t0, n));
                        let j = choose|j: int| 0 <= j < t0.len() && (#[trigger] t0[j]).0 == n;
                        assert(t0.len() == 0);
                    }
                }
            }
        }
        let ghost lo = self.lo as nat;
        proof {
            assert(pn_below(vf, lo));
        }
        let ghost t1 = table_view(self.entries@);
        let r = assign(f, &mut self.entries, &mut self.next, Ghost(lo));
        let ghost t2 = table_view(self.entries@);
        proof {
            // old numbers are kept
            assert forall|n: Seq<u8>| #[trigger] s0.contains(n) implies number_of(t2, n) == number_of(t0, n)
                && match pnum(n) { Some(v) => v < self.lo, None => lookup(t2, n) is Some } by {
                if pnum(n) is None {
                    assert(lookup(t0, n) is Some);
                    assert(t1 == t0);
                    lemma_lookup_extends(t1, t2, lo, self.next as nat, n);
                }
            }
        }
        match r {
            Some(g) => {
                self.seen = Ghost(s0.union(atoms_mltl(vf)));
                proof {
                    assert forall|n: Seq<u8>| #[trigger] self.seen@.contains(n) implies match pnum(n) {
                        Some(v) => v < self.lo,
                        None => lookup(t2, n) is Some,
                    } by {
                        if !s0.contains(n) {
                            assert(atoms_mltl(vf).contains(n));
                        }
                    }
                    assert(self.wf());
                    self.lemma_injective();
                    assert forall|n: Seq<u8>| #[trigger] s0.contains(n) implies (self.num())(n) == number_of(t0, n) by {}
                }
                Ok(g)
            },
            None => {
                proof {
                    assert(self.wf());
                    self.lemma_injective();
                }
                Err(ErrorKind::NumberingFailed)
            },
        }
    }

    /// Parse MLTL text ([`crate::parse`]) and number its atoms with this table.
    ///
    /// - `Ok(g)`: `g` is the formula the text denotes, with each atom
    ///   replaced by its number in the (grown) table.
    /// - An error other than [`ErrorKind::NumberTaken`] /
    ///   [`ErrorKind::NumberingFailed`] means the text is not a formula.
    pub fn parse(&mut self, text: &[u8]) -> (r: Result<Mltl<usize>, ParseError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).injective(),
            old(self).grows_to(final(self)),
            r is Ok ==> exists|f: SpecFormula| {
                &&& #[trigger] denotes(text@, f)
                &&& r->Ok_0 == map_atoms(f, final(self).num())
                &&& atoms_mltl(f).subset_of(final(self).names())
            },
            r is Err ==> error_ok(r->Err_0, text.len() as nat),
            r is Err && !(r->Err_0.kind is NumberTaken || r->Err_0.kind is NumberingFailed)
                ==> forall|f: SpecFormula| !#[trigger] denotes(text@, f),
    {
        match crate::parse(text) {
            Ok(f) => {
                proof { assert(denotes(text@, view_f(f))); }
                match self.number(&f) {
                    Ok(g) => Ok(g),
                    Err(kind) => Err(ParseError { kind, at: Span { start: 0, end: text.len() }, related: None }),
                }
            },
            Err(e) => {
                proof { self.lemma_injective(); }
                Err(e)
            },
        }
    }

    /// The number of the atom `name`, if it is in the table. Use it to build
    /// traces: `None` for a name that no formula parsed with this table has.
    pub fn atom(&self, name: &Vec<u8>) -> (r: Option<usize>)
        requires
            self.wf(),
        ensures
            self.names().contains(name@) ==> r is Some,
            r is Some ==> r->Some_0 == (self.num())(name@),
            // no other name has this number
            r is Some ==> forall|n: Seq<u8>| self.names().contains(n) && #[trigger] (self.num())(n) == r->Some_0
                ==> n == name@,
    {
        let ghost t = table_view(self.entries@);
        let (is_pn, overflow, v) = exec_pnum(name);
        if is_pn {
            if !overflow && v < self.lo {
                proof {
                    assert forall|n: Seq<u8>| self.names().contains(n) && #[trigger] (self.num())(n) == v
                        implies n == name@ by {
                        assert(self.seen@.contains(n));
                        if pnum(n) is Some {
                            lemma_pnum_injective(name@, n);
                        } else {
                            let j = entry_index(t, n);
                            assert(t[j].1 >= self.lo);
                        }
                    }
                }
                Some(v)
            } else {
                proof {
                    if self.names().contains(name@) { assert(self.seen@.contains(name@)); }
                }
                None
            }
        } else {
            let r = find(&self.entries, name, Ghost(self.lo as nat), Ghost(self.next as nat));
            proof {
                if self.names().contains(name@) { assert(self.seen@.contains(name@)); }
                if r is Some {
                    let jn = entry_index(t, name@);
                    assert forall|n: Seq<u8>| self.names().contains(n) && #[trigger] (self.num())(n) == r->Some_0
                        implies n == name@ by {
                        assert(self.seen@.contains(n));
                        if pnum(n) is Some {
                            assert(t[jn].1 >= self.lo);
                        } else {
                            let j = entry_index(t, n);
                            if j != jn { assert(t[j].1 != t[jn].1); }
                        }
                    }
                }
            }
            r
        }
    }

    /// [`Atoms::trace`] for names already in the table.
    /// `Err((i, j))`: `steps[i][j]` is not in the table.
    fn trace_known(&self, steps: &Vec<Vec<Vec<u8>>>) -> (r: Result<Vec<HashSet<usize>>, (usize, usize)>)
        requires
            self.wf(),
        ensures
            r is Ok ==> traces_agree(named_trace(steps@), numbered_trace((r->Ok_0)@), self.names(), self.num()),
            r is Err ==> {
                let (i, j) = r->Err_0;
                &&& i < steps.len() && j < steps@[i as int].len()
                &&& !self.names().contains(steps@[i as int]@[j as int]@)
            },
    {
        let ghost pi = named_trace(steps@);
        let mut out: Vec<HashSet<usize>> = Vec::new();
        let mut i = 0;
        while i < steps.len()
            invariant
                self.wf(),
                0 <= i <= steps.len(),
                out.len() == i,
                pi == named_trace(steps@),
                forall|k: int, n: Seq<u8>| 0 <= k < i && self.names().contains(n)
                    ==> (#[trigger] pi[k].contains(n) <==> out@[k]@.contains((self.num())(n))),
            decreases steps.len() - i,
        {
            let s = &steps[i];
            let mut set: HashSet<usize> = HashSet::new();
            let mut j = 0;
            while j < s.len()
                invariant
                    self.wf(),
                    0 <= j <= s.len(),
                    i < steps.len(),
                    s == steps@[i as int],
                    // the set holds the numbers of the first j names
                    forall|n: Seq<u8>| self.names().contains(n) ==>
                        (set@.contains(#[trigger] (self.num())(n)) <==> exists|m: int| 0 <= m < j && (#[trigger] s@[m])@ == n),
                decreases s.len() - j,
            {
                match self.atom(&s[j]) {
                    Some(id) => {
                        let ghost before = set@;
                        set.insert(id);
                        proof {
                            assert forall|n: Seq<u8>| self.names().contains(n) implies
                                (set@.contains(#[trigger] (self.num())(n)) <==> exists|m: int| 0 <= m < j + 1 && (#[trigger] s@[m])@ == n) by {
                                if set@.contains((self.num())(n)) {
                                    if !before.contains((self.num())(n)) {
                                        assert((self.num())(n) == id);
                                        assert(n == s@[j as int]@);
                                    } else {
                                        let m = choose|m: int| 0 <= m < j && (#[trigger] s@[m])@ == n;
                                        assert(0 <= m < j + 1 && s@[m]@ == n);
                                    }
                                }
                                if exists|m: int| 0 <= m < j + 1 && (#[trigger] s@[m])@ == n {
                                    let m = choose|m: int| 0 <= m < j + 1 && (#[trigger] s@[m])@ == n;
                                    if m == j {
                                        assert(id == (self.num())(s@[j as int]@));
                                    } else {
                                        assert(0 <= m < j && s@[m]@ == n);
                                    }
                                }
                            }
                        }
                    },
                    None => {
                        return Err((i, j));
                    },
                }
                j = j + 1;
            }
            proof {
                assert forall|n: Seq<u8>| self.names().contains(n) implies
                    (#[trigger] pi[i as int].contains(n) <==> set@.contains((self.num())(n))) by {
                    let names_i = s@.map_values(|v: Vec<u8>| v@);
                    assert(pi[i as int] == names_i.to_set());
                    names_i.to_set_ensures();
                    if exists|m: int| 0 <= m < s.len() && (#[trigger] s@[m])@ == n {
                        let m = choose|m: int| 0 <= m < s.len() && (#[trigger] s@[m])@ == n;
                        assert(names_i[m] == n);
                    }
                    if names_i.contains(n) {
                        let m = choose|m: int| 0 <= m < names_i.len() && names_i[m] == n;
                        assert(s@[m]@ == n);
                    }
                }
            }
            out.push(set);
            i = i + 1;
        }
        proof {
            let rho = numbered_trace(out@);
            assert forall|k: int, n: Seq<u8>| 0 <= k < pi.len() && self.names().contains(n)
                implies (#[trigger] pi[k].contains(n) <==> rho[k].contains((self.num())(n))) by {
                assert(rho[k] == out@[k]@);
            }
        }
        Ok(out)
    }

    /// Number every name in `steps` that is not in the table yet, in reading
    /// order, as [`Atoms::parse`] would. `Err((i, j, kind))`: numbering
    /// `steps[i][j]` failed (see [`Atoms::number`]); names before it were added.
    pub fn add_names(&mut self, steps: &Vec<Vec<Vec<u8>>>) -> (r: Result<(), (usize, usize, ErrorKind)>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).injective(),
            old(self).grows_to(final(self)),
            r is Ok ==> steps_in(steps@, final(self).names()),
            r matches Err((i, j, kind)) ==> i < steps.len() && j < steps@[i as int].len()
                && (kind is NumberTaken || kind is NumberingFailed),
    {
        let ghost names0 = self.names();
        let ghost num0 = self.num();
        proof {
            self.lemma_injective();
            assert(names0 == old(self).names() && num0 == old(self).num());
        }
        let mut i = 0;
        while i < steps.len()
            invariant
                self.wf(), self.injective(),
                names0.subset_of(self.names()),
                forall|n: Seq<u8>| #[trigger] names0.contains(n) ==> (self.num())(n) == num0(n),
                names0 == old(self).names(), num0 == old(self).num(),
                i <= steps.len(),
                forall|a: int, b: int| 0 <= a < i && 0 <= b < steps@[a]@.len() ==> self.names().contains(#[trigger] steps@[a]@[b]@),
            decreases steps.len() - i,
        {
            let s = &steps[i];
            let mut j = 0;
            while j < s.len()
                invariant
                    self.wf(), self.injective(),
                    names0.subset_of(self.names()),
                    forall|n: Seq<u8>| #[trigger] names0.contains(n) ==> (self.num())(n) == num0(n),
                    names0 == old(self).names(), num0 == old(self).num(),
                    i < steps.len(), s == steps@[i as int], j <= s.len(),
                    forall|a: int, b: int| 0 <= a < i && 0 <= b < steps@[a]@.len() ==> self.names().contains(#[trigger] steps@[a]@[b]@),
                    forall|b: int| 0 <= b < j ==> self.names().contains(#[trigger] s@[b]@),
                decreases s.len() - j,
            {
                let ghost names1 = self.names();
                let ghost num1 = self.num();
                let f: ExecFormula = Mltl::Prop(copy_vec(&s[j]));
                match self.number(&f) {
                    Ok(_) => {
                        proof {
                            assert(atoms_mltl(view_f(f)).contains(s@[j as int]@));
                            assert forall|n: Seq<u8>| #[trigger] names0.contains(n) implies (self.num())(n) == num0(n) by {
                                assert(names1.contains(n));
                            }
                            assert forall|b: int| 0 <= b < j + 1 implies self.names().contains(#[trigger] s@[b]@) by {
                                if b < j { assert(names1.contains(s@[b]@)); }
                            }
                            assert forall|a: int, b: int| 0 <= a < i && 0 <= b < steps@[a]@.len() implies self.names().contains(#[trigger] steps@[a]@[b]@) by {
                                assert(names1.contains(steps@[a]@[b]@));
                            }
                        }
                    },
                    Err(kind) => {
                        proof {
                            assert forall|n: Seq<u8>| #[trigger] names0.contains(n) implies (self.num())(n) == num0(n) by {
                                assert(names1.contains(n));
                            }
                        }
                        return Err((i, j, kind));
                    },
                }
                j = j + 1;
            }
            proof {
                assert forall|a: int, b: int| 0 <= a < i + 1 && 0 <= b < steps@[a]@.len() implies self.names().contains(#[trigger] steps@[a]@[b]@) by {
                    if a == i { assert(steps@[a] == s); }
                }
            }
            i = i + 1;
        }
        Ok(())
    }

    /// A trace given by names: step `i` holds exactly the names in
    /// `steps[i]`. Names not in the table yet are numbered first
    /// ([`Atoms::add_names`]). The numbered trace agrees with the named one
    /// on every name in the table, so a formula parsed with this table has
    /// the same truth value on both ([`lemma_numbering_semantics`]).
    pub fn trace(&mut self, steps: &Vec<Vec<Vec<u8>>>) -> (r: Result<Vec<HashSet<usize>>, (usize, usize, ErrorKind)>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).injective(),
            old(self).grows_to(final(self)),
            r is Ok ==> steps_in(steps@, final(self).names())
                && traces_agree(named_trace(steps@), numbered_trace((r->Ok_0)@), final(self).names(), final(self).num()),
            r matches Err((i, j, kind)) ==> i < steps.len() && j < steps@[i as int].len()
                && (kind is NumberTaken || kind is NumberingFailed),
    {
        self.add_names(steps)?;
        match self.trace_known(steps) {
            Ok(t) => Ok(t),
            Err((i, j)) => {
                proof { assert(self.names().contains(steps@[i as int]@[j as int]@)); }
                Err((i, j, ErrorKind::NumberingFailed))
            },
        }
    }

    /// From a numbered or named result to the error of a text: numbering
    /// errors cover the whole text.
    fn text_error(kind: ErrorKind, len: usize) -> (r: ParseError)
        ensures
            error_ok(r, len as nat),
            r.kind == kind,
    {
        ParseError { kind, at: Span { start: 0, end: len }, related: None }
    }

    /// Read a trace in the sets syntax (`[{request}, {grant, ok}, {}]`,
    /// GRAMMAR.md §6) and number it with this table.
    ///
    /// - `Ok(t)`: the text denotes a trace whose names are all in the
    ///   (grown) table, and `t` agrees with it on every name in the table.
    /// - An error other than [`ErrorKind::NumberTaken`] /
    ///   [`ErrorKind::NumberingFailed`] means the text is not a trace.
    pub fn parse_trace(&mut self, text: &[u8]) -> (r: Result<Vec<HashSet<usize>>, ParseError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).injective(),
            old(self).grows_to(final(self)),
            r is Ok ==> exists|ss: SpecSteps| {
                &&& #[trigger] trace_denotes(text@, ss)
                &&& sets_in(ss, final(self).names())
                &&& traces_agree(trace_sets(ss), numbered_trace((r->Ok_0)@), final(self).names(), final(self).num())
            },
            r is Err ==> error_ok(r->Err_0, text.len() as nat),
            r is Err && !(r->Err_0.kind is NumberTaken || r->Err_0.kind is NumberingFailed)
                ==> forall|ss: SpecSteps| !#[trigger] trace_denotes(text@, ss),
    {
        match parse_trace(text) {
            Ok(steps) => self.number_steps(&steps, text.len()),
            Err(e) => {
                proof { self.lemma_injective(); }
                Err(e)
            },
        }
    }

    /// Read a trace in R2U2's CSV format (GRAMMAR.md §6) and number it with
    /// this table. As [`Atoms::parse_trace`], for `csv_trace`.
    pub fn parse_csv(&mut self, text: &[u8]) -> (r: Result<Vec<HashSet<usize>>, ParseError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).injective(),
            old(self).grows_to(final(self)),
            r is Ok ==> exists|ss: SpecSteps| {
                &&& #[trigger] csv_trace(text@) == Some(ss)
                &&& sets_in(ss, final(self).names())
                &&& traces_agree(trace_sets(ss), numbered_trace((r->Ok_0)@), final(self).names(), final(self).num())
            },
            r is Err ==> error_ok(r->Err_0, text.len() as nat),
            r is Err && !(r->Err_0.kind is NumberTaken || r->Err_0.kind is NumberingFailed)
                ==> csv_trace(text@) is None,
    {
        match parse_csv(text) {
            Ok(steps) => {
                let r = self.number_steps(&steps, text.len());
                proof {
                    if r is Ok { assert(csv_trace(text@) == Some(steps_view(steps@))); }
                }
                r
            },
            Err(e) => {
                proof { self.lemma_injective(); }
                Err(e)
            },
        }
    }

    /// [`Atoms::trace`], stated for the steps' view.
    fn number_steps(&mut self, steps: &ExecSteps, len: usize) -> (r: Result<Vec<HashSet<usize>>, ParseError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).injective(),
            old(self).grows_to(final(self)),
            r is Ok ==> sets_in(steps_view(steps@), final(self).names())
                && traces_agree(trace_sets(steps_view(steps@)), numbered_trace((r->Ok_0)@), final(self).names(), final(self).num()),
            r is Err ==> error_ok(r->Err_0, len as nat)
                && (r->Err_0.kind is NumberTaken || r->Err_0.kind is NumberingFailed),
    {
        match self.trace(steps) {
            Ok(t) => {
                proof {
                    lemma_trace_sets(steps@);
                    let sv = steps_view(steps@);
                    assert forall|i: int, m: int| 0 <= i < sv.len() && 0 <= m < sv[i].len() implies self.names().contains(#[trigger] sv[i][m]) by {
                        assert(sv[i][m] == steps@[i]@[m]@);
                    }
                }
                Ok(t)
            },
            Err((_, _, kind)) => Err(Self::text_error(kind, len)),
        }
    }

    /// Print a numbered trace in the sets syntax, with this table's names
    /// (`pk` for numbers without a name), listing only atoms below `n`.
    /// The text denotes a trace whose steps hold, as numbers, exactly the
    /// atoms below `n` of `t`'s steps.
    pub fn print_trace(&self, t: &Vec<HashSet<usize>>, n: usize) -> (r: Vec<u8>)
        requires
            self.wf(),
        ensures
            exists|ss: SpecSteps| #[trigger] trace_denotes(r@, ss) && printed_as(ss, t@, n, self.num()),
    {
        let mut steps: ExecSteps = Vec::new();
        let mut i = 0;
        while i < t.len()
            invariant
                self.wf(),
                i <= t.len(),
                steps@.len() == i,
                valid_steps(steps_view(steps@)),
                forall|a: int, x: usize| 0 <= a < i ==>
                    ((#[trigger] t@[a]@.contains(x) && x < n) <==> exists|m: int| 0 <= m < steps_view(steps@)[a].len() && #[trigger] (self.num())(steps_view(steps@)[a][m]) == x),
            decreases t.len() - i,
        {
            let set = &t[i];
            let mut names: Vec<Vec<u8>> = Vec::new();
            let mut k: usize = 0;
            while k < n
                invariant
                    self.wf(),
                    i < t.len(), set == t@[i as int],
                    k <= n,
                    forall|m: int| 0 <= m < names@.len() ==> valid_name(#[trigger] names_view(names@)[m]),
                    forall|m: int| 0 <= m < names@.len() ==> (#[trigger] (self.num())(names_view(names@)[m])) < k
                        && set@.contains((self.num())(names_view(names@)[m])),
                    forall|x: usize| x < k ==> (#[trigger] set@.contains(x) <==> exists|m: int| 0 <= m < names@.len() && #[trigger] (self.num())(names_view(names@)[m]) == x),
                decreases n - k,
            {
                if set.contains(&k) {
                    let ghost before = names_view(names@);
                    let nm = self.name_of(k);
                    let ghost nv = nm@;
                    names.push(nm);
                    proof {
                        assert(names_view(names@) =~= before.push(nv));
                        assert(names_view(names@)[before.len() as int] == nv);
                        assert forall|x: usize| x < k + 1 implies (#[trigger] set@.contains(x) <==> exists|m: int| 0 <= m < names@.len() && #[trigger] (self.num())(names_view(names@)[m]) == x) by {
                            if x < k {
                                if set@.contains(x) {
                                    let m = choose|m: int| 0 <= m < before.len() && #[trigger] (self.num())(before[m]) == x;
                                    assert(names_view(names@)[m] == before[m]);
                                }
                                if exists|m: int| 0 <= m < names@.len() && #[trigger] (self.num())(names_view(names@)[m]) == x {
                                    let m = choose|m: int| 0 <= m < names@.len() && #[trigger] (self.num())(names_view(names@)[m]) == x;
                                    if m < before.len() { assert(names_view(names@)[m] == before[m]); }
                                }
                            } else {
                                assert((self.num())(names_view(names@)[before.len() as int]) == k);
                            }
                        }
                        assert forall|m: int| 0 <= m < names@.len() implies (#[trigger] (self.num())(names_view(names@)[m])) < k + 1
                            && set@.contains((self.num())(names_view(names@)[m])) by {
                            if m < before.len() { assert(names_view(names@)[m] == before[m]); }
                        }
                        assert forall|m: int| 0 <= m < names@.len() implies valid_name(#[trigger] names_view(names@)[m]) by {
                            if m < before.len() { assert(names_view(names@)[m] == before[m]); }
                        }
                    }
                } else {
                    proof {
                        assert forall|x: usize| x < k + 1 implies (#[trigger] set@.contains(x) <==> exists|m: int| 0 <= m < names@.len() && #[trigger] (self.num())(names_view(names@)[m]) == x) by {
                            if x == k && exists|m: int| 0 <= m < names@.len() && #[trigger] (self.num())(names_view(names@)[m]) == x {
                                let m = choose|m: int| 0 <= m < names@.len() && #[trigger] (self.num())(names_view(names@)[m]) == x;
                                assert(set@.contains((self.num())(names_view(names@)[m])));
                            }
                        }
                    }
                }
                k = k + 1;
            }
            let ghost sv0 = steps_view(steps@);
            let ghost nv = names_view(names@);
            proof {
                assert forall|x: usize| (#[trigger] set@.contains(x) && x < n) <==> exists|m: int| 0 <= m < nv.len() && #[trigger] (self.num())(nv[m]) == x by {
                    if exists|m: int| 0 <= m < nv.len() && #[trigger] (self.num())(nv[m]) == x {
                        let m = choose|m: int| 0 <= m < nv.len() && #[trigger] (self.num())(nv[m]) == x;
                        assert((self.num())(nv[m]) < k && set@.contains((self.num())(nv[m])));
                    }
                }
            }
            steps.push(names);
            proof {
                let sv = steps_view(steps@);
                assert(sv =~= sv0.push(nv));
                assert forall|a: int, m: int| 0 <= a < sv.len() && 0 <= m < sv[a].len() implies valid_name(#[trigger] sv[a][m]) by {
                    if a < sv0.len() { assert(sv[a] == sv0[a]); assert(valid_name(sv0[a][m])); }
                }
                assert forall|a: int, x: usize| 0 <= a < i + 1 implies
                    ((#[trigger] t@[a]@.contains(x) && x < n) <==> exists|m: int| 0 <= m < steps_view(steps@)[a].len() && #[trigger] (self.num())(steps_view(steps@)[a][m]) == x) by {
                    if a < i {
                        assert(sv[a] == sv0[a]);
                    } else {
                        assert(sv[a] == nv);
                        if t@[a]@.contains(x) && x < n {
                            assert(set@.contains(x));
                        }
                        if exists|m: int| 0 <= m < sv[a].len() && #[trigger] (self.num())(sv[a][m]) == x {
                            let m = choose|m: int| 0 <= m < sv[a].len() && #[trigger] (self.num())(sv[a][m]) == x;
                            assert((self.num())(nv[m]) < n && set@.contains((self.num())(nv[m])));
                        }
                    }
                }
            }
            proof {
                assert(forall|a: int, x: usize| 0 <= a < i + 1 ==>
                    ((#[trigger] t@[a]@.contains(x) && x < n) <==> exists|m: int| 0 <= m < steps_view(steps@)[a].len() && #[trigger] (self.num())(steps_view(steps@)[a][m]) == x));
            }
            i = i + 1;
            proof {
                assert(forall|a: int, x: usize| 0 <= a < i ==>
                    ((#[trigger] t@[a]@.contains(x) && x < n) <==> exists|m: int| 0 <= m < steps_view(steps@)[a].len() && #[trigger] (self.num())(steps_view(steps@)[a][m]) == x));
            }
        }
        let r = print_trace(&steps);
        proof {
            assert(trace_denotes(r@, steps_view(steps@)));
            let sv = steps_view(steps@);
            let tv = t@;
            assert(sv.len() == tv.len());
            assert forall|a: int, x: usize| 0 <= a < tv.len() implies
                ((#[trigger] tv[a]@.contains(x) && x < n) <==> exists|m: int| 0 <= m < sv[a].len() && #[trigger] (self.num())(sv[a][m]) == x) by {
                assert(0 <= a < i);
                assert((t@[a]@.contains(x) && x < n) <==> exists|m: int| 0 <= m < steps_view(steps@)[a].len() && #[trigger] (self.num())(steps_view(steps@)[a][m]) == x);
            }
            assert(printed_as(sv, tv, n, self.num()));
        }
        r
    }

    /// A name for atom number `k`: the name in the table with that number
    /// (if any), otherwise `pk`.
    fn name_of(&self, k: usize) -> (r: Vec<u8>)
        requires
            self.wf(),
        ensures
            valid_name(r@),
            (self.num())(r@) == k,
    {
        let ghost t = table_view(self.entries@);
        let mut j = 0;
        while j < self.entries.len()
            invariant
                self.wf(),
                t == table_view(self.entries@),
                j <= self.entries.len(),
            decreases self.entries.len() - j,
        {
            if self.entries[j].1 == k && exec_valid_name(&self.entries[j].0) {
                proof {
                    assert(t[j as int] == (self.entries@[j as int].0@, self.entries@[j as int].1));
                    lemma_lookup_at(t, self.lo as nat, self.next as nat, j as int);
                }
                return copy_vec(&self.entries[j].0);
            }
            j = j + 1;
        }
        let mut r: Vec<u8> = Vec::new();
        r.push(112u8);
        push_digits(k, &mut r);
        proof {
            let d = digits(k as nat);
            lemma_digits(k as nat);
            assert(r@ == seq![112u8] + d);
            assert(r@.subrange(1, (1 + d.len()) as int) =~= d);
            lemma_digits_value(r@, 1, k as nat);
            assert(r@.drop_first() =~= d);
            assert(pnum(r@) == Some(k as nat));
            assert(is_word_start(r@[0]));
            assert forall|m: int| 0 <= m < r@.len() implies is_word_char(#[trigger] r@[m]) by {
                if m > 0 { assert(r@[m] == d[m - 1]); }
            }
            assert(!is_word(r@, seq![70u8]) && !is_word(r@, seq![71u8]) && !is_word(r@, seq![85u8])
                && !is_word(r@, seq![82u8]) && !is_word(r@, seq![116u8, 114, 117, 101]) && !is_word(r@, seq![116u8])
                && !is_word(r@, seq![116u8, 116]) && !is_word(r@, seq![102u8, 97, 108, 115, 101])
                && !is_word(r@, seq![102u8]) && !is_word(r@, seq![102u8, 102]));
        }
        r
    }

    /// `g` with every atom number replaced by a name ([`Atoms::name_of`]):
    /// numbering the result with this table gives back `g`.
    pub fn name(&self, g: &Mltl<usize>) -> (r: ExecFormula)
        requires
            self.wf(),
        ensures
            map_atoms(view_f(r), self.num()) == *g,
            valid_names(view_f(r)),
            intervals_welldef(view_f(r)) == intervals_welldef(*g),
        decreases g,
    {
        match g {
            Mltl::True => Mltl::True,
            Mltl::False => Mltl::False,
            Mltl::Prop(k) => Mltl::Prop(self.name_of(*k)),
            Mltl::Not(x) => Mltl::Not(Box::new(self.name(x))),
            Mltl::And(x, y) => Mltl::And(Box::new(self.name(x)), Box::new(self.name(y))),
            Mltl::Or(x, y) => Mltl::Or(Box::new(self.name(x)), Box::new(self.name(y))),
            Mltl::Future(a, b, x) => Mltl::Future(*a, *b, Box::new(self.name(x))),
            Mltl::Global(a, b, x) => Mltl::Global(*a, *b, Box::new(self.name(x))),
            Mltl::Until(x, a, b, y) => Mltl::Until(Box::new(self.name(x)), *a, *b, Box::new(self.name(y))),
            Mltl::Release(x, a, b, y) => Mltl::Release(Box::new(self.name(x)), *a, *b, Box::new(self.name(y))),
        }
    }

    /// Print a numbered formula with this table's names (`pk` for numbers
    /// without a name). If every interval has `a ≤ b`, the text denotes a
    /// formula whose numbering with this table is exactly `g`.
    pub fn print(&self, g: &Mltl<usize>) -> (r: Vec<u8>)
        requires
            self.wf(),
        ensures
            intervals_welldef(*g) ==> exists|f: SpecFormula| #[trigger] denotes(r@, f) && map_atoms(f, self.num()) == *g,
    {
        let f = self.name(g);
        let r = print(&f);
        proof {
            if intervals_welldef(*g) {
                assert(printable(view_f(f)));
                assert(denotes(r@, view_f(f)));
            }
        }
        r
    }
}

} // verus!
