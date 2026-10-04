//! Verified LRAT proof checker (RUP steps and deletions).
//!
//! An LRAT proof is a list of steps. An addition step gives a clause id, the
//! clause `C`, and hints: ids of earlier clauses. It is checked by reverse
//! unit propagation along the hints: assume every literal of `C` is false;
//! then each hinted clause, in order, must either become unit (its one
//! unassigned literal is set true) or be falsified, which ends the check
//! successfully. A deletion step removes clauses. Adding the empty clause
//! proves the input CNF unsatisfiable.
//!
//! Soundness invariant: every clause in the database is entailed by the input
//! CNF. RAT steps (negative hints) are not supported and fail the check.
//! There is no Isabelle source; the guarantee is `refuted() ==>
//! !dimacs_satisfiable(formula)`.
use vstd::prelude::*;
use crate::dimacs::*;

verus! {

/// Value of a literal under a partial assignment (`vals[x]`: 0 unassigned,
/// 1 true, -1 false): 1 true, -1 false, 0 unassigned.
pub open spec fn lit_value(vals: Seq<i8>, l: i32) -> int {
    let x = var_of(l);
    if vals[x] == 0 {
        0
    } else if (vals[x] == 1) == (l > 0) {
        1
    } else {
        -1
    }
}

pub open spec fn vals_ok(vals: Seq<i8>) -> bool {
    forall|x: int| 0 <= x < vals.len() ==> (#[trigger] vals[x] == 0 || vals[x] == 1 || vals[x] == -1)
}

pub open spec fn all_zero(vals: Seq<i8>) -> bool {
    forall|x: int| 0 <= x < vals.len() ==> #[trigger] vals[x] == 0
}

/// The total valuation `v` extends the partial assignment.
pub open spec fn agrees(v: spec_fn(nat) -> bool, vals: Seq<i8>) -> bool {
    forall|x: int| 0 <= x < vals.len() && #[trigger] vals[x] != 0 ==> ((vals[x] == 1) == v(x as nat))
}

/// Every assigned variable is on the trail.
pub open spec fn covered(vals: Seq<i8>, trail: Seq<usize>) -> bool {
    forall|x: int| 0 <= x < vals.len() && #[trigger] vals[x] != 0 ==> exists|k: int|
        0 <= k < trail.len() && trail[k] as int == x
}

pub open spec fn trail_ok(trail: Seq<usize>, nv: int) -> bool {
    forall|k: int| 0 <= k < trail.len() ==> (#[trigger] trail[k] as int) < nv
}

/// Every clause in the database is well formed and entailed by `f`.
pub open spec fn db_ok(db: Seq<Option<Vec<i32>>>, f: Seq<Seq<i32>>, nv: int) -> bool {
    forall|id: int| 0 <= id < db.len() && (#[trigger] db[id]) is Some ==> {
        &&& clause_ok(db[id]->0@, nv)
        &&& dimacs_entails(f, db[id]->0@)
    }
}

/// RUP invariant: every model of `f` falsifying `c` extends `vals`.
pub open spec fn rup_inv(f: Seq<Seq<i32>>, c: Seq<i32>, vals: Seq<i8>) -> bool {
    forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f) && !dimacs_clause_sem(v, c) ==> agrees(v, vals)
}

proof fn lit_value_sound(v: spec_fn(nat) -> bool, vals: Seq<i8>, l: i32)
    requires
        vals_ok(vals),
        agrees(v, vals),
        lit_ok(l, vals.len() as int),
    ensures
        lit_value(vals, l) == 1 ==> dimacs_lit_sem(v, l),
        lit_value(vals, l) == -1 ==> !dimacs_lit_sem(v, l),
{
    let x = var_of(l);
    assert(vals[x] == 0 || vals[x] == 1 || vals[x] == -1);
    if vals[x] != 0 {
        assert((vals[x] == 1) == v(x as nat));
        if l > 0 {
            assert(l as nat == x as nat);
        }
    }
}

/// Clear the assignment: every assigned variable is on the trail.
fn reset(vals: &mut Vec<i8>, trail: &mut Vec<usize>)
    requires
        covered(old(vals)@, old(trail)@),
        trail_ok(old(trail)@, old(vals)@.len() as int),
    ensures
        final(vals)@.len() == old(vals)@.len(),
        all_zero(final(vals)@),
        final(trail)@.len() == 0,
{
    let mut i: usize = 0;
    let n = trail.len();
    while i < n
        invariant
            n == trail@.len(),
            trail@ == old(trail)@,
            i <= n,
            vals@.len() == old(vals)@.len(),
            trail_ok(trail@, vals@.len() as int),
            forall|x: int|
                0 <= x < vals@.len() && #[trigger] vals@[x] != 0 ==> exists|k: int|
                    i <= k < n && trail@[k] as int == x,
        decreases n - i,
    {
        let x = trail[i];
        assert((trail@[i as int] as int) < vals@.len());
        let ghost before = vals@;
        vals.set(x, 0);
        assert forall|y: int|
            0 <= y < vals@.len() && #[trigger] vals@[y] != 0 implies exists|k: int|
                i + 1 <= k < n && trail@[k] as int == y by {
            assert(y != x as int);
            assert(before[y] != 0);
            let k = choose|k: int| i <= k < n && trail@[k] as int == y;
            assert(k != i as int);
        }
        i += 1;
    }
    assert forall|x: int| 0 <= x < vals@.len() implies #[trigger] vals@[x] == 0 by {
        if vals@[x] != 0 {
            let k = choose|k: int| i <= k < n && trail@[k] as int == x;
        }
    }
    trail.clear();
}

/// Validate a clause's literals against the variable bound.
fn clause_valid(c: &Vec<i32>, nv: usize) -> (r: bool)
    ensures
        r == clause_ok(c@, nv as int),
{
    let mut j: usize = 0;
    while j < c.len()
        invariant
            j <= c.len(),
            forall|k: int| 0 <= k < j ==> lit_ok(#[trigger] c@[k], nv as int),
        decreases c.len() - j,
    {
        let l = c[j];
        if l == 0 || l == i32::MIN {
            return false;
        }
        let x: usize = if l > 0 { l as usize } else { (-l) as usize };
        if x >= nv {
            return false;
        }
        j += 1;
    }
    true
}

/// Exec `lit_value` (`l` well formed).
fn value(vals: &Vec<i8>, l: i32) -> (r: i8)
    requires
        lit_ok(l, vals@.len() as int),
        vals_ok(vals@),
    ensures
        r as int == lit_value(vals@, l),
{
    let x: usize = if l > 0 { l as usize } else { (-l) as usize };
    let s = vals[x];
    if s == 0 {
        0
    } else if (s == 1) == (l > 0) {
        1
    } else {
        -1
    }
}

/// Outcome of scanning a hinted clause.
pub enum Scan {
    /// every literal is false
    Conflict,
    /// every literal is false or equal to this unassigned literal
    Unit(i32),
    /// a literal is true, or two distinct literals are unassigned
    Fail,
}

fn scan(d: &Vec<i32>, vals: &Vec<i8>) -> (r: Scan)
    requires
        clause_ok(d@, vals@.len() as int),
        vals_ok(vals@),
    ensures
        r is Conflict ==> forall|k: int| 0 <= k < d@.len() ==> lit_value(vals@, #[trigger] d@[k]) == -1,
        r is Unit ==> {
            &&& lit_ok(r->0, vals@.len() as int)
            &&& lit_value(vals@, r->0) == 0
            &&& forall|k: int|
                0 <= k < d@.len() ==> lit_value(vals@, #[trigger] d@[k]) == -1 || d@[k] == r->0
        },
{
    let mut unit: i32 = 0;
    let mut j: usize = 0;
    while j < d.len()
        invariant
            j <= d@.len(),
            clause_ok(d@, vals@.len() as int),
            vals_ok(vals@),
            unit != 0 ==> lit_ok(unit, vals@.len() as int) && lit_value(vals@, unit) == 0,
            forall|k: int|
                0 <= k < j ==> lit_value(vals@, #[trigger] d@[k]) == -1 || (unit != 0 && d@[k] == unit),
        decreases d@.len() - j,
    {
        let l = d[j];
        assert(lit_ok(d@[j as int], vals@.len() as int));
        let s = value(vals, l);
        if s == 1 {
            return Scan::Fail;
        } else if s == 0 {
            if unit == 0 {
                unit = l;
            } else if unit != l {
                return Scan::Fail;
            }
        }
        j += 1;
    }
    if unit == 0 {
        Scan::Conflict
    } else {
        Scan::Unit(unit)
    }
}

/// Assign literal `l` the given truth value.
fn assign(vals: &mut Vec<i8>, trail: &mut Vec<usize>, l: i32, truth: bool)
    requires
        lit_ok(l, old(vals)@.len() as int),
        lit_value(old(vals)@, l) == 0,
        vals_ok(old(vals)@),
        covered(old(vals)@, old(trail)@),
        trail_ok(old(trail)@, old(vals)@.len() as int),
    ensures
        final(vals)@.len() == old(vals)@.len(),
        vals_ok(final(vals)@),
        covered(final(vals)@, final(trail)@),
        trail_ok(final(trail)@, final(vals)@.len() as int),
        final(vals)@ == old(vals)@.update(var_of(l), if truth == (l > 0) { 1i8 } else { -1i8 }),
        lit_value(final(vals)@, l) == if truth { 1int } else { -1int },
{
    let x: usize = if l > 0 { l as usize } else { (-l) as usize };
    let s: i8 = if truth == (l > 0) { 1 } else { -1 };
    vals.set(x, s);
    trail.push(x);
    assert forall|y: int| 0 <= y < vals@.len() && #[trigger] vals@[y] != 0 implies exists|k: int|
        0 <= k < trail@.len() && trail@[k] as int == y by {
        if y == x as int {
            assert(trail@[trail@.len() - 1] == x);
        } else {
            assert(old(vals)@[y] != 0);
            let k = choose|k: int| 0 <= k < old(trail)@.len() && old(trail)@[k] as int == y;
            assert(trail@[k] == old(trail)@[k]);
        }
    }
    assert forall|y: int| 0 <= y < vals@.len() implies (#[trigger] vals@[y] == 0 || vals@[y] == 1
        || vals@[y] == -1) by {
        if y != x as int {
            assert(old(vals)@[y] == 0 || old(vals)@[y] == 1 || old(vals)@[y] == -1);
        }
    }
}

/// Assigning `l` true keeps agreement with every `v` that makes `l` true.
proof fn agrees_assign(v: spec_fn(nat) -> bool, old_vals: Seq<i8>, l: i32, truth: bool)
    requires
        agrees(v, old_vals),
        lit_ok(l, old_vals.len() as int),
        dimacs_lit_sem(v, l) == truth,
    ensures
        agrees(v, old_vals.update(var_of(l), if truth == (l > 0) { 1i8 } else { -1i8 })),
{
    let nv = old_vals.update(var_of(l), if truth == (l > 0) { 1i8 } else { -1i8 });
    assert forall|y: int| 0 <= y < nv.len() && #[trigger] nv[y] != 0 implies ((nv[y] == 1) == v(y as nat)) by {
        if y == var_of(l) {
            if l > 0 {
                assert(l as nat == y as nat);
            }
        } else {
            assert(old_vals[y] != 0);
        }
    }
}

/// Check one RUP addition: on success, `f ⊫ c`. The assignment is all zero
/// before and after.
fn check_rup(
    db: &Vec<Option<Vec<i32>>>,
    vals: &mut Vec<i8>,
    trail: &mut Vec<usize>,
    c: &Vec<i32>,
    hints: &Vec<i64>,
    Ghost(f): Ghost<Seq<Seq<i32>>>,
) -> (r: bool)
    requires
        all_zero(old(vals)@),
        old(trail)@.len() == 0,
        db_ok(db@, f, old(vals)@.len() as int),
    ensures
        final(vals)@.len() == old(vals)@.len(),
        all_zero(final(vals)@),
        final(trail)@.len() == 0,
        r ==> clause_ok(c@, final(vals)@.len() as int) && dimacs_entails(f, c@),
{
    let nv = vals.len();
    if !clause_valid(c, nv) {
        return false;
    }
    let ghost cs = c@;
    // Phase 1: falsify every literal of `c`.
    let mut taut = false;
    let mut i: usize = 0;
    while i < c.len()
        invariant
            cs == c@,
            i <= cs.len(),
            vals@.len() == nv,
            clause_ok(cs, nv as int),
            vals_ok(vals@),
            covered(vals@, trail@),
            trail_ok(trail@, nv as int),
            !taut ==> forall|y: int|
                0 <= y < nv && #[trigger] vals@[y] != 0 ==> exists|j: int|
                    0 <= j < i && var_of(cs[j]) == y && lit_value(vals@, cs[j]) == -1,
            taut ==> forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_clause_sem(v, cs),
        decreases cs.len() - i,
    {
        if taut {
            break;
        }
        let l = c[i];
        assert(lit_ok(cs[i as int], nv as int));
        let s = value(vals, l);
        if s == 1 {
            // An earlier literal of `c` is `-l`: `c` is a tautology.
            let ghost y = var_of(l);
            assert(vals@[y] != 0);
            let ghost j = choose|j: int| 0 <= j < i && var_of(cs[j]) == y && lit_value(vals@, cs[j]) == -1;
            assert(cs[j] == -l);
            assert forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_clause_sem(v, cs) by {
                if !dimacs_lit_sem(v, cs[i as int]) {
                    assert(dimacs_lit_sem(v, cs[j]));
                }
            }
            taut = true;
        } else if s == 0 {
            let ghost old_vals = vals@;
            assign(vals, trail, l, false);
            assert forall|y: int|
                0 <= y < nv && #[trigger] vals@[y] != 0 implies exists|j: int|
                    0 <= j < i + 1 && var_of(cs[j]) == y && lit_value(vals@, cs[j]) == -1 by {
                if y == var_of(l) {
                    assert(var_of(cs[i as int]) == y && lit_value(vals@, cs[i as int]) == -1);
                } else {
                    assert(old_vals[y] != 0);
                    let j = choose|j: int| 0 <= j < i && var_of(cs[j]) == y && lit_value(old_vals, cs[j]) == -1;
                    assert(var_of(cs[j]) != var_of(l));
                    assert(lit_value(vals@, cs[j]) == -1);
                }
            }
        }
        i += 1;
    }
    if taut {
        reset(vals, trail);
        assert forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f) implies dimacs_clause_sem(v, cs) by {
            assert(dimacs_clause_sem(v, cs));
        }
        return true;
    }
    // Every model of f falsifying c extends vals.
    assert forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f) && !dimacs_clause_sem(v, cs) implies agrees(v, vals@) by {
        assert forall|y: int| 0 <= y < vals@.len() && #[trigger] vals@[y] != 0 implies ((vals@[y] == 1) == v(y as nat)) by {
            let j = choose|j: int| 0 <= j < cs.len() && var_of(cs[j]) == y && lit_value(vals@, cs[j]) == -1;
            assert(!dimacs_lit_sem(v, cs[j]));
            if cs[j] > 0 {
                assert(cs[j] as nat == y as nat);
            }
        }
    }
    // Phase 2: propagate along the hints.
    let mut ok = false;
    let mut k: usize = 0;
    while k < hints.len()
        invariant
            cs == c@,
            vals@.len() == nv,
            clause_ok(cs, nv as int),
            vals_ok(vals@),
            covered(vals@, trail@),
            trail_ok(trail@, nv as int),
            db_ok(db@, f, nv as int),
            rup_inv(f, cs, vals@),
            ok ==> dimacs_entails(f, cs),
        decreases hints.len() - k,
    {
        if ok {
            break;
        }
        let h = hints[k];
        if h <= 0 || h as u64 >= db.len() as u64 {
            break;
        }
        let hi = h as usize;
        match &db[hi] {
            None => {
                break;
            },
            Some(d) => {
                assert(db@[hi as int] is Some);
                assert(clause_ok(d@, nv as int) && dimacs_entails(f, d@));
                match scan(d, vals) {
                    Scan::Fail => {
                        break;
                    },
                    Scan::Conflict => {
                        assert forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f) implies dimacs_clause_sem(v, cs) by {
                            if !dimacs_clause_sem(v, cs) {
                                assert(agrees(v, vals@));
                                assert(dimacs_clause_sem(v, d@));
                                let j = choose|j: int| 0 <= j < d@.len() && dimacs_lit_sem(v, #[trigger] d@[j]);
                                assert(lit_ok(d@[j], nv as int));
                                lit_value_sound(v, vals@, d@[j]);
                            }
                        }
                        ok = true;
                    },
                    Scan::Unit(u) => {
                        let ghost old_vals = vals@;
                        assign(vals, trail, u, true);
                        assert forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f) && !dimacs_clause_sem(v, cs) implies agrees(v, vals@) by {
                            assert(agrees(v, old_vals));
                            assert(dimacs_clause_sem(v, d@));
                            let j = choose|j: int| 0 <= j < d@.len() && dimacs_lit_sem(v, #[trigger] d@[j]);
                            assert(lit_ok(d@[j], nv as int));
                            lit_value_sound(v, old_vals, d@[j]);
                            assert(d@[j] == u);
                            agrees_assign(v, old_vals, u, true);
                        }
                    },
                }
            },
        }
        k += 1;
    }
    reset(vals, trail);
    ok
}

/// One LRAT step, already parsed.
pub enum LratStep {
    /// `id lits 0 hints 0`
    Add { id: u64, clause: Vec<i32>, hints: Vec<i64> },
    /// `id d ids 0`
    Delete { ids: Vec<u64> },
}

/// Incremental LRAT checker for a fixed input CNF (`formula`).
pub struct LratChecker {
    db: Vec<Option<Vec<i32>>>,
    vals: Vec<i8>,
    trail: Vec<usize>,
    refuted: bool,
    formula: Ghost<Seq<Seq<i32>>>,
}

fn copy_clause(c: &Vec<i32>) -> (r: Vec<i32>)
    ensures
        r@ == c@,
{
    let mut r: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < c.len()
        invariant
            j <= c.len(),
            r@ == c@.subrange(0, j as int),
        decreases c.len() - j,
    {
        r.push(c[j]);
        j += 1;
    }
    assert(r@ =~= c@);
    r
}

impl LratChecker {
    /// The input CNF.
    pub closed spec fn formula(&self) -> Seq<Seq<i32>> {
        self.formula@
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.vals@.len() > 0
        &&& all_zero(self.vals@)
        &&& self.trail@.len() == 0
        &&& db_ok(self.db@, self.formula@, self.vals@.len() as int)
        &&& self.refuted ==> !dimacs_satisfiable(self.formula@)
    }

    /// Start checking proofs against `cnf`, whose clauses get ids 1..n in
    /// order. `None` if a literal is 0 or `i32::MIN`.
    pub fn new(cnf: &Vec<Vec<i32>>) -> (r: Option<Self>)
        ensures
            r is Some ==> r->0.inv() && r->0.formula() == cnf_seqs(cnf@),
    {
        let ghost f = cnf_seqs(cnf@);
        // Largest variable.
        let mut nv: usize = 0;
        let mut i: usize = 0;
        while i < cnf.len()
            invariant
                i <= cnf.len(),
                forall|k: int| 0 <= k < i ==> clause_ok(#[trigger] cnf@[k]@, nv as int + 1),
            decreases cnf.len() - i,
        {
            let c = &cnf[i];
            let mut j: usize = 0;
            while j < c.len()
                invariant
                    j <= c.len(),
                    forall|k: int| 0 <= k < i ==> clause_ok(#[trigger] cnf@[k]@, nv as int + 1),
                    forall|k: int| 0 <= k < j ==> lit_ok(#[trigger] c@[k], nv as int + 1),
                decreases c.len() - j,
            {
                let l = c[j];
                if l == 0 || l == i32::MIN {
                    return None;
                }
                let x: usize = if l > 0 { l as usize } else { (-l) as usize };
                if x > nv {
                    nv = x;
                }
                j += 1;
            }
            i += 1;
        }
        if nv == usize::MAX {
            return None;
        }
        let mut vals: Vec<i8> = Vec::new();
        let mut i: usize = 0;
        while i <= nv
            invariant
                nv < usize::MAX,
                i <= nv + 1,
                vals@.len() == i,
                all_zero(vals@),
            decreases nv + 1 - i,
        {
            vals.push(0);
            i += 1;
        }
        let mut db: Vec<Option<Vec<i32>>> = Vec::new();
        db.push(None);
        let mut i: usize = 0;
        while i < cnf.len()
            invariant
                i <= cnf.len(),
                db@.len() == i + 1,
                forall|k: int| 0 <= k < cnf@.len() ==> clause_ok(#[trigger] cnf@[k]@, nv as int + 1),
                db@[0] is None,
                forall|k: int| 1 <= k < db@.len() ==> (#[trigger] db@[k]) is Some && db@[k]->0@ == cnf@[k - 1]@,
            decreases cnf.len() - i,
        {
            db.push(Some(copy_clause(&cnf[i])));
            i += 1;
        }
        let r = LratChecker { db, vals, trail: Vec::new(), refuted: false, formula: Ghost(f) };
        assert forall|id: int| 0 <= id < r.db@.len() && (#[trigger] r.db@[id]) is Some implies {
            &&& clause_ok(r.db@[id]->0@, r.vals@.len() as int)
            &&& dimacs_entails(f, r.db@[id]->0@)
        } by {
            assert(f[id - 1] == cnf@[id - 1]@);
            assert forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f) implies dimacs_clause_sem(v, r.db@[id]->0@) by {
                assert(dimacs_clause_sem(v, f[id - 1]));
            }
        }
        Some(r)
    }

    pub closed spec fn is_refuted(&self) -> bool {
        self.refuted
    }

    /// `true` once the empty clause has been added. Then the input CNF is
    /// unsatisfiable.
    pub fn refuted(&self) -> (r: bool)
        requires
            self.inv(),
        ensures
            r == self.is_refuted(),
            r ==> !dimacs_satisfiable(self.formula()),
    {
        self.refuted
    }

    /// Check and add clause `id`. `false` if the step does not check (the
    /// database is unchanged then).
    pub fn add(&mut self, id: u64, clause: &Vec<i32>, hints: &Vec<i64>) -> (r: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).formula() == old(self).formula(),
            old(self).is_refuted() ==> final(self).is_refuted(),
    {
        let ghost f = self.formula@;
        if !check_rup(&self.db, &mut self.vals, &mut self.trail, clause, hints, Ghost(f)) {
            return false;
        }
        let ghost cs = clause@;
        if clause.len() == 0 {
            assert forall|v: spec_fn(nat) -> bool| !#[trigger] dimacs_models(v, f) by {
                if dimacs_models(v, f) {
                    assert(dimacs_clause_sem(v, cs));
                }
            }
            self.refuted = true;
        }
        if id >= usize::MAX as u64 {
            return false;
        }
        let idx = id as usize;
        let ghost nvl = self.vals@.len() as int;
        if idx < self.db.len() {
            self.db.set(idx, Some(copy_clause(clause)));
        } else {
            while self.db.len() < idx
                invariant
                    db_ok(self.db@, f, nvl),
                decreases idx - self.db@.len(),
            {
                self.db.push(None);
            }
            self.db.push(Some(copy_clause(clause)));
        }
        assert forall|j: int| 0 <= j < self.db@.len() && (#[trigger] self.db@[j]) is Some implies {
            &&& clause_ok(self.db@[j]->0@, nvl)
            &&& dimacs_entails(f, self.db@[j]->0@)
        } by {
            if j != idx as int {
            }
        }
        true
    }

    /// Delete clause `id` (no effect if absent).
    pub fn delete(&mut self, id: u64)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).formula() == old(self).formula(),
            old(self).is_refuted() ==> final(self).is_refuted(),
    {
        if id < self.db.len() as u64 {
            self.db.set(id as usize, None);
        }
    }
}

/// Check a whole LRAT proof of `cnf`. `true` means `cnf` is unsatisfiable.
/// The steps may come from anywhere (e.g. an unverified solver and parser).
pub fn check_lrat(cnf: &Vec<Vec<i32>>, steps: &Vec<LratStep>) -> (r: bool)
    ensures
        r ==> !dimacs_satisfiable(cnf_seqs(cnf@)),
{
    let mut ch = match LratChecker::new(cnf) {
        Some(ch) => ch,
        None => return false,
    };
    let mut s: usize = 0;
    while s < steps.len()
        invariant
            ch.inv(),
            ch.formula() == cnf_seqs(cnf@),
        decreases steps.len() - s,
    {
        if ch.refuted() {
            return true;
        }
        match &steps[s] {
            LratStep::Add { id, clause, hints } => {
                if !ch.add(*id, clause, hints) {
                    return false;
                }
            },
            LratStep::Delete { ids } => {
                let mut i: usize = 0;
                while i < ids.len()
                    invariant
                        ch.inv(),
                        ch.formula() == cnf_seqs(cnf@),
                    decreases ids.len() - i,
                {
                    ch.delete(ids[i]);
                    i += 1;
                }
            },
        }
        s += 1;
    }
    ch.refuted()
}

} // verus!
