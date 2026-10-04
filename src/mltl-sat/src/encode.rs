//! Executable CNF encoding of the fast translation.
//!
//! Variables: `bvar(n, id, t) = 1 + id·n + t` is `(sub[id], t)` (one per table
//! entry and time `t < n`); above `len·n` come auxiliary variables, one per
//! step of an Until unrolling (`aux[x] = (φ, ψ, i, ub)` means
//! `unroll_until φ ψ i ub`). Each spec clause `Atom(x) ↔ rhs` becomes:
//!
//! - `True`: `[x]`;  `Not`: `[¬x,¬y] [x,y]`;  `And`: `[¬x,y] [¬x,z] [x,¬y,¬z]`;
//! - `Until` at `k` (`lb = a+k`, `ub = b+k`): with `u_lb = x`, `u_ub = ψ@ub`
//!   and fresh `u_i` in between, `u_i ↔ ψ@i ∨ (φ@i ∧ u_{i+1})` for
//!   `lb ≤ i < ub`, i.e. `[¬u,ψ,φ] [¬u,ψ,u'] [u,¬ψ] [u,¬φ,¬u']`
//!   (`[¬x,ψ] [x,¬ψ]` when `lb = ub`).
//!
//! Soundness invariant (`enc_ok`): every valuation satisfying the spec clauses
//! emitted so far, extended to the auxiliary variables by their meaning
//! (`ext_val`), satisfies the CNF.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use propositional::formula::*;
use propositional::dimacs::*;
use crate::fast::*;
use crate::table::*;

verus! {

/// `(φ, ψ, i, ub)`: the auxiliary variable means `unroll_until φ ψ i ub`.
pub type AuxDef = (Mltl<usize>, Mltl<usize>, nat, nat);

pub open spec fn bvar(n: nat, id: nat, t: nat) -> int {
    (1 + id * n + t) as int
}

pub open spec fn nbase(sub: Seq<Mltl<usize>>, n: nat) -> int {
    (sub.len() * n) as int
}

/// Extension of a spec valuation to the CNF's variables.
pub open spec fn ext_val(
    v: spec_fn(Var<usize>) -> bool,
    sub: Seq<Mltl<usize>>,
    n: nat,
    aux: Map<nat, AuxDef>,
) -> spec_fn(nat) -> bool {
    |x: nat|
        if 1 <= x && x <= sub.len() * n {
            v((sub[(x - 1) / (n as int)], ((x - 1) % (n as int)) as nat))
        } else if aux.contains_key(x) {
            formula_semantics(v, unroll_until(aux[x].0, aux[x].1, aux[x].2, aux[x].3))
        } else {
            false
        }
}

pub proof fn bvar_bound(n: nat, id: nat, t: nat, len: nat)
    requires
        id < len,
        t < n,
    ensures
        1 <= bvar(n, id, t) <= len * n,
{
    assert(id * n + t < len * n) by (nonlinear_arith)
        requires
            id < len,
            t < n,
    ;
}

pub proof fn ext_val_base(v: spec_fn(Var<usize>) -> bool, sub: Seq<Mltl<usize>>, n: nat, aux: Map<nat, AuxDef>, id: nat, t: nat)
    requires
        id < sub.len(),
        t < n,
    ensures
        ext_val(v, sub, n, aux)(bvar(n, id, t) as nat) == v((sub[id as int], t)),
{
    bvar_bound(n, id, t, sub.len());
    let x = bvar(n, id, t);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x - 1, n as int, id as int, t as int);
}

/// Literal `l` uses a known variable: base, or auxiliary with a meaning.
pub open spec fn var_known(l: i32, nb: int, aux: Map<nat, AuxDef>, next: int) -> bool {
    &&& l != 0 && l != i32::MIN
    &&& var_of(l) < next
    &&& (var_of(l) <= nb || aux.contains_key(var_of(l) as nat))
}

pub open spec fn cnf_known(cnf: Seq<Seq<i32>>, nb: int, aux: Map<nat, AuxDef>, next: int) -> bool {
    forall|i: int, j: int| 0 <= i < cnf.len() && 0 <= j < cnf[i].len() ==> var_known(#[trigger] cnf[i][j], nb, aux, next)
}

/// The encoder state.
pub struct Enc {
    pub cnf: Vec<Vec<i32>>,
    /// Next free variable.
    pub next: i32,
    pub aux: Ghost<Map<nat, AuxDef>>,
    /// The spec clauses encoded so far.
    pub spec: Ghost<Seq<Formula<Var<usize>>>>,
}

pub open spec fn enc_ok(e: Enc, sub: Seq<Mltl<usize>>, n: nat) -> bool {
    let nb = nbase(sub, n);
    &&& nb < e.next
    &&& forall|x: nat| #[trigger] e.aux@.contains_key(x) ==> nb < x < e.next
    &&& cnf_known(cnf_seqs(e.cnf@), nb, e.aux@, e.next as int)
    &&& forall|v: spec_fn(Var<usize>) -> bool|
        #[trigger] models_all(v, e.spec@) ==> dimacs_models(ext_val(v, sub, n, e.aux@), cnf_seqs(e.cnf@))
}

pub open spec fn aux_extends(a1: Map<nat, AuxDef>, a2: Map<nat, AuxDef>) -> bool {
    forall|x: nat| #[trigger] a1.contains_key(x) ==> a2.contains_key(x) && a2[x] == a1[x]
}

/// A literal over known variables has the same value after more auxiliary
/// variables are defined.
pub proof fn ext_lit_stable(
    v: spec_fn(Var<usize>) -> bool,
    sub: Seq<Mltl<usize>>,
    n: nat,
    a1: Map<nat, AuxDef>,
    a2: Map<nat, AuxDef>,
    l: i32,
    next: int,
)
    requires
        var_known(l, nbase(sub, n), a1, next),
        aux_extends(a1, a2),
    ensures
        dimacs_lit_sem(ext_val(v, sub, n, a1), l) == dimacs_lit_sem(ext_val(v, sub, n, a2), l),
{
    let x = var_of(l) as nat;
    if l > 0 {
        assert(l as nat == x);
    }
    if !(1 <= x && x <= sub.len() * n) {
        assert(a1.contains_key(x));
    }
}

pub proof fn ext_cnf_stable(
    v: spec_fn(Var<usize>) -> bool,
    sub: Seq<Mltl<usize>>,
    n: nat,
    a1: Map<nat, AuxDef>,
    a2: Map<nat, AuxDef>,
    cnf: Seq<Seq<i32>>,
    next: int,
)
    requires
        cnf_known(cnf, nbase(sub, n), a1, next),
        aux_extends(a1, a2),
        dimacs_models(ext_val(v, sub, n, a1), cnf),
    ensures
        dimacs_models(ext_val(v, sub, n, a2), cnf),
{
    let w1 = ext_val(v, sub, n, a1);
    let w2 = ext_val(v, sub, n, a2);
    assert forall|i: int| 0 <= i < cnf.len() implies dimacs_clause_sem(w2, #[trigger] cnf[i]) by {
        assert(dimacs_clause_sem(w1, cnf[i]));
        let j = choose|j: int| 0 <= j < cnf[i].len() && dimacs_lit_sem(w1, #[trigger] cnf[i][j]);
        ext_lit_stable(v, sub, n, a1, a2, cnf[i][j], next);
    }
}

/// Satisfaction of a short clause, literal by literal.
pub proof fn clause_sem_3(w: spec_fn(nat) -> bool, c: Seq<i32>)
    requires
        1 <= c.len() <= 3,
    ensures
        dimacs_clause_sem(w, c) == (dimacs_lit_sem(w, c[0]) || (c.len() > 1 && dimacs_lit_sem(w, c[1])) || (
        c.len() > 2 && dimacs_lit_sem(w, c[2]))),
{
    if dimacs_clause_sem(w, c) {
        let j = choose|j: int| 0 <= j < c.len() && dimacs_lit_sem(w, #[trigger] c[j]);
        assert(j == 0 || j == 1 || j == 2);
    }
}

/// `dimacs_lit_sem` of a positive variable and its negation.
pub proof fn lit_sem_pm(w: spec_fn(nat) -> bool, x: i32, nx: i32)
    requires
        x > 0,
        nx == -x,
    ensures
        dimacs_lit_sem(w, x) == w(x as nat),
        dimacs_lit_sem(w, nx) == !w(x as nat),
{
    assert(var_of(nx) == x as int);
}

pub proof fn ext_var_stable(
    v: spec_fn(Var<usize>) -> bool,
    sub: Seq<Mltl<usize>>,
    n: nat,
    a1: Map<nat, AuxDef>,
    a2: Map<nat, AuxDef>,
    x: nat,
)
    requires
        (1 <= x && x <= sub.len() * n) || a1.contains_key(x),
        aux_extends(a1, a2),
    ensures
        ext_val(v, sub, n, a1)(x) == ext_val(v, sub, n, a2)(x),
{
}

// ---------------------------------------------------------------------------
// Reading a CNF model back as a valuation of the spec variables
// ---------------------------------------------------------------------------

/// `(ψ, t)` is true iff the variable of ψ's table entry at time `t` is.
pub open spec fn restrict(w: spec_fn(nat) -> bool, sub: Seq<Mltl<usize>>, n: nat) -> spec_fn(Var<usize>) -> bool {
    |p: Var<usize>|
        exists|id: nat| id < sub.len() && sub[id as int] == p.0 && p.1 < n && #[trigger] w(bvar(n, id, p.1) as nat)
}

pub open spec fn sub_injective(sub: Seq<Mltl<usize>>) -> bool {
    forall|i: int, j: int| 0 <= i < sub.len() && 0 <= j < sub.len() && i != j ==> #[trigger] sub[i] != #[trigger] sub[j]
}

pub proof fn restrict_base(w: spec_fn(nat) -> bool, sub: Seq<Mltl<usize>>, n: nat, id: nat, t: nat)
    requires
        sub_injective(sub),
        id < sub.len(),
        t < n,
    ensures
        restrict(w, sub, n)((sub[id as int], t)) == w(bvar(n, id, t) as nat),
{
    if restrict(w, sub, n)((sub[id as int], t)) {
        let j = choose|j: nat| j < sub.len() && sub[j as int] == sub[id as int] && t < n && #[trigger] w(bvar(n, j, t) as nat);
        assert(j == id);
    } else if w(bvar(n, id, t) as nat) {
        let p: Var<usize> = (sub[id as int], t);
        assert(w(bvar(n, id, p.1) as nat));
        assert(restrict(w, sub, n)(p));
    }
}

/// Completeness invariant: every model of the CNF, read back, satisfies the
/// spec clauses encoded so far.
pub open spec fn enc_complete(e: Enc, sub: Seq<Mltl<usize>>, n: nat) -> bool {
    forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(e.cnf@)) ==> models_all(restrict(w, sub, n), e.spec@)
}

pub proof fn cnf_seqs_push(v: Seq<Vec<i32>>, c: Vec<i32>)
    ensures
        cnf_seqs(v.push(c)) == cnf_seqs(v).push(c@),
{
    assert(cnf_seqs(v.push(c)) =~= cnf_seqs(v).push(c@));
}

pub proof fn models_prefix(w: spec_fn(nat) -> bool, f: Seq<Seq<i32>>, g: Seq<Seq<i32>>)
    requires
        dimacs_models(w, g),
        f.len() <= g.len(),
        g.subrange(0, f.len() as int) == f,
    ensures
        dimacs_models(w, f),
{
    assert forall|i: int| 0 <= i < f.len() implies dimacs_clause_sem(w, #[trigger] f[i]) by {
        assert(f[i] == g.subrange(0, f.len() as int)[i]);
        assert(dimacs_clause_sem(w, g[i]));
    }
}

pub proof fn models_contains(w: spec_fn(nat) -> bool, f: Seq<Seq<i32>>, c: Seq<i32>)
    requires
        dimacs_models(w, f),
        f.contains(c),
    ensures
        dimacs_clause_sem(w, c),
{
    let i = choose|i: int| 0 <= i < f.len() && f[i] == c;
    assert(dimacs_clause_sem(w, f[i]));
}

/// The four clauses of one Until unrolling step `u ↔ h ∨ (g ∧ u2)`.
pub open spec fn step_ok(f: Seq<Seq<i32>>, u: i32, u2: i32, h: i32, g: i32) -> bool {
    &&& f.contains(seq![(-u) as i32, h, g])
    &&& f.contains(seq![(-u) as i32, h, u2])
    &&& f.contains(seq![u, (-h) as i32])
    &&& f.contains(seq![u, (-g) as i32, (-u2) as i32])
}

pub proof fn step_value(w: spec_fn(nat) -> bool, f: Seq<Seq<i32>>, u: i32, u2: i32, h: i32, g: i32)
    requires
        dimacs_models(w, f),
        step_ok(f, u, u2, h, g),
        u > 0,
        u2 > 0,
        h > 0,
        g > 0,
    ensures
        w(u as nat) == (w(h as nat) || (w(g as nat) && w(u2 as nat))),
{
    models_contains(w, f, seq![(-u) as i32, h, g]);
    models_contains(w, f, seq![(-u) as i32, h, u2]);
    models_contains(w, f, seq![u, (-h) as i32]);
    models_contains(w, f, seq![u, (-g) as i32, (-u2) as i32]);
    lit_sem_pm(w, u, (-u) as i32);
    lit_sem_pm(w, u2, (-u2) as i32);
    lit_sem_pm(w, h, (-h) as i32);
    lit_sem_pm(w, g, (-g) as i32);
    clause_sem_3(w, seq![(-u) as i32, h, g]);
    clause_sem_3(w, seq![(-u) as i32, h, u2]);
    clause_sem_3(w, seq![u, (-h) as i32]);
    clause_sem_3(w, seq![u, (-g) as i32, (-u2) as i32]);
}

/// Completeness after encoding one more spec clause `cl`.
pub proof fn complete_after(
    cnf0: Seq<Seq<i32>>,
    spec0: Seq<Formula<Var<usize>>>,
    fin: Seq<Seq<i32>>,
    sub: Seq<Mltl<usize>>,
    n: nat,
    cl: Formula<Var<usize>>,
)
    requires
        forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf0) ==> models_all(restrict(w, sub, n), spec0),
        forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, fin) ==> dimacs_models(w, cnf0),
        forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, fin) ==> formula_semantics(restrict(w, sub, n), cl),
    ensures
        forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, fin) ==> models_all(restrict(w, sub, n), spec0.push(cl)),
{
    assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, fin) implies models_all(restrict(w, sub, n), spec0.push(cl)) by {
        assert(dimacs_models(w, cnf0));
        models_all_push(restrict(w, sub, n), spec0, cl);
    }
}

pub proof fn prefix_models(cnf0: Seq<Seq<i32>>, fin: Seq<Seq<i32>>)
    requires
        cnf0.len() <= fin.len(),
        fin.subrange(0, cnf0.len() as int) == cnf0,
    ensures
        forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, fin) ==> dimacs_models(w, cnf0),
{
    assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, fin) implies dimacs_models(w, cnf0) by {
        models_prefix(w, cnf0, fin);
    }
}

pub proof fn step_ok_prefix(f: Seq<Seq<i32>>, g: Seq<Seq<i32>>, u: i32, u2: i32, h: i32, gg: i32)
    requires
        step_ok(f, u, u2, h, gg),
        f.len() <= g.len(),
        g.subrange(0, f.len() as int) == f,
    ensures
        step_ok(g, u, u2, h, gg),
{
    assert forall|c: Seq<i32>| f.contains(c) implies g.contains(c) by {
        let i = choose|i: int| 0 <= i < f.len() && f[i] == c;
        assert(g[i] == g.subrange(0, f.len() as int)[i]);
    }
}

pub proof fn contains_push(s: Seq<Seq<i32>>, c: Seq<i32>, d: Seq<i32>)
    requires
        s.contains(d),
    ensures
        s.push(c).contains(d),
{
    let i = choose|i: int| 0 <= i < s.len() && s[i] == d;
    assert(s.push(c)[i] == d);
}

/// Along an encoded Until chain, every chain variable has the value of its
/// unrolling suffix (backwards induction from `ub`).
pub proof fn chain_values(
    w: spec_fn(nat) -> bool,
    f: Seq<Seq<i32>>,
    chain: Seq<i32>,
    sub: Seq<Mltl<usize>>,
    n: nat,
    ci: nat,
    di: nat,
    lb: nat,
    ub: nat,
    j: nat,
)
    requires
        dimacs_models(w, f),
        sub_injective(sub),
        ci < sub.len(),
        di < sub.len(),
        sub.len() * n < i32::MAX,
        lb <= ub,
        ub < n,
        chain.len() == ub - lb + 1,
        forall|jj: int| 0 <= jj < chain.len() ==> #[trigger] chain[jj] > 0,
        chain[ub - lb] as int == bvar(n, di, ub),
        forall|jj: int|
            0 <= jj < ub - lb ==> #[trigger] step_ok(
                f,
                chain[jj],
                chain[jj + 1],
                bvar(n, di, (lb + jj) as nat) as i32,
                bvar(n, ci, (lb + jj) as nat) as i32,
            ),
        j <= ub - lb,
    ensures
        w(chain[j as int] as nat) == formula_semantics(restrict(w, sub, n), unroll_until(sub[ci as int], sub[di as int], lb + j, ub)),
    decreases ub - lb - j,
{
    let v = restrict(w, sub, n);
    let i = lb + j;
    bvar_bound(n, di, i, sub.len());
    if j == ub - lb {
        restrict_base(w, sub, n, di, ub);
    } else {
        chain_values(w, f, chain, sub, n, ci, di, lb, ub, j + 1);
        bvar_bound(n, ci, i, sub.len());
        let h = bvar(n, di, i) as i32;
        let g = bvar(n, ci, i) as i32;
        assert(step_ok(f, chain[j as int], chain[j as int + 1], h, g));
        assert(chain[j as int] > 0 && chain[j as int + 1] > 0);
        step_value(w, f, chain[j as int], chain[j as int + 1], h, g);
        restrict_base(w, sub, n, di, i);
        restrict_base(w, sub, n, ci, i);
        reveal_with_fuel(formula_semantics, 3);
        assert(unroll_until(sub[ci as int], sub[di as int], i, ub) == Formula::Or(
            Box::new(Formula::Atom((sub[di as int], i))),
            Box::new(Formula::And(
                Box::new(Formula::Atom((sub[ci as int], i))),
                Box::new(unroll_until(sub[ci as int], sub[di as int], i + 1, ub)),
            )),
        ));
    }
}

// ---------------------------------------------------------------------------
// Encoder primitives
// ---------------------------------------------------------------------------

/// Context: a table and the horizon `n`, with room for every base variable.
pub open spec fn ctx_ok(t: &Table, n: nat) -> bool {
    &&& t.ok()
    &&& n > 0
    &&& t.sub@.len() * n < i32::MAX
}

/// Exec `bvar`.
pub(crate) fn bv_pub(t: &Table, n: usize, id: usize, k: usize) -> (x: i32)
    requires
        ctx_ok(t, n as nat),
        id < t.nodes@.len(),
        k < n,
    ensures
        x as int == bvar(n as nat, id as nat, k as nat),
        1 <= x,
{
    bv(t, n, id, k)
}

/// Exec `bvar`.
fn bv(t: &Table, n: usize, id: usize, k: usize) -> (x: i32)
    requires
        ctx_ok(t, n as nat),
        id < t.nodes@.len(),
        k < n,
    ensures
        x as int == bvar(n as nat, id as nat, k as nat),
        1 <= x,
        x as int <= nbase(t.sub@, n as nat),
{
    proof {
        bvar_bound(n as nat, id as nat, k as nat, t.sub@.len());
        assert(id * n <= t.sub@.len() * n) by (nonlinear_arith)
            requires
                id < t.sub@.len(),
        ;
    }
    (1 + id * n + k) as i32
}

/// Add a clause that every model of the spec satisfies (under `ext_val`).
fn add_clause(e: &mut Enc, c: Vec<i32>, Ghost(sub): Ghost<Seq<Mltl<usize>>>, Ghost(n): Ghost<nat>)
    requires
        enc_ok(*old(e), sub, n),
        forall|j: int| 0 <= j < c@.len() ==> var_known(#[trigger] c@[j], nbase(sub, n), old(e).aux@, old(e).next as int),
        forall|v: spec_fn(Var<usize>) -> bool|
            #[trigger] models_all(v, old(e).spec@) ==> dimacs_clause_sem(ext_val(v, sub, n, old(e).aux@), c@),
    ensures
        enc_ok(*final(e), sub, n),
        final(e).spec@ == old(e).spec@,
        final(e).aux@ == old(e).aux@,
        final(e).next == old(e).next,
        cnf_seqs(final(e).cnf@) == cnf_seqs(old(e).cnf@).push(c@),
{
    let ghost old_cnf = cnf_seqs(e.cnf@);
    let ghost cs = c@;
    e.cnf.push(c);
    proof {
        let f = cnf_seqs(e.cnf@);
        assert(f =~= old_cnf.push(cs));
        assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies dimacs_models(
            ext_val(v, sub, n, e.aux@),
            f,
        ) by {
            assert(dimacs_models(ext_val(v, sub, n, e.aux@), old_cnf));
            assert forall|i: int| 0 <= i < f.len() implies dimacs_clause_sem(ext_val(v, sub, n, e.aux@), #[trigger] f[i]) by {
                if i < old_cnf.len() {
                    assert(f[i] == old_cnf[i]);
                }
            }
        }
        assert forall|i: int, j: int| 0 <= i < f.len() && 0 <= j < f[i].len() implies var_known(
            #[trigger] f[i][j],
            nbase(sub, n),
            e.aux@,
            e.next as int,
        ) by {
            if i < old_cnf.len() {
                assert(f[i] == old_cnf[i]);
            } else {
                assert(f[i] == cs);
            }
        }
    }
}

/// Allocate an auxiliary variable meaning `unroll_until φ ψ i ub`.
fn alloc_aux(e: &mut Enc, Ghost(def): Ghost<AuxDef>, Ghost(sub): Ghost<Seq<Mltl<usize>>>, Ghost(n): Ghost<nat>) -> (x: i32)
    requires
        enc_ok(*old(e), sub, n),
        old(e).next < i32::MAX,
    ensures
        enc_ok(*final(e), sub, n),
        x == old(e).next,
        final(e).next == old(e).next + 1,
        final(e).aux@ == old(e).aux@.insert(x as nat, def),
        aux_extends(old(e).aux@, final(e).aux@),
        final(e).spec@ == old(e).spec@,
        final(e).cnf@ == old(e).cnf@,
{
    let x = e.next;
    let ghost a1 = e.aux@;
    proof {
        assert(!a1.contains_key(x as nat));
    }
    e.aux = Ghost(e.aux@.insert(x as nat, def));
    e.next = x + 1;
    proof {
        let a2 = e.aux@;
        assert(aux_extends(a1, a2));
        let f = cnf_seqs(e.cnf@);
        assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies dimacs_models(
            ext_val(v, sub, n, a2),
            f,
        ) by {
            ext_cnf_stable(v, sub, n, a1, a2, f, x as int);
        }
        assert forall|i: int, j: int| 0 <= i < f.len() && 0 <= j < f[i].len() implies var_known(
            #[trigger] f[i][j],
            nbase(sub, n),
            a2,
            e.next as int,
        ) by {
            assert(var_known(f[i][j], nbase(sub, n), a1, x as int));
        }
    }
    x
}

pub proof fn models_all_push<V>(v: spec_fn(V) -> bool, s: Seq<Formula<V>>, c: Formula<V>)
    ensures
        models_all(v, s.push(c)) == (models_all(v, s) && formula_semantics(v, c)),
{
    if models_all(v, s.push(c)) {
        assert(s.push(c)[s.len() as int] == c);
        assert forall|i: int| 0 <= i < s.len() implies formula_semantics(v, #[trigger] s[i]) by {
            assert(s.push(c)[i] == s[i]);
        }
    }
    if models_all(v, s) && formula_semantics(v, c) {
        assert forall|i: int| 0 <= i < s.push(c).len() implies formula_semantics(v, #[trigger] s.push(c)[i]) by {
            if i < s.len() {
                assert(s.push(c)[i] == s[i]);
            }
        }
    }
}

/// Record that spec clause `c` is being encoded.
fn push_spec(e: &mut Enc, Ghost(c): Ghost<Formula<Var<usize>>>, Ghost(sub): Ghost<Seq<Mltl<usize>>>, Ghost(n): Ghost<nat>)
    requires
        enc_ok(*old(e), sub, n),
    ensures
        enc_ok(*final(e), sub, n),
        final(e).spec@ == old(e).spec@.push(c),
        final(e).aux@ == old(e).aux@,
        final(e).next == old(e).next,
        final(e).cnf@ == old(e).cnf@,
{
    let ghost s0 = e.spec@;
    e.spec = Ghost(e.spec@.push(c));
    proof {
        assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies dimacs_models(
            ext_val(v, sub, n, e.aux@),
            cnf_seqs(e.cnf@),
        ) by {
            models_all_push(v, s0, c);
            assert(models_all(v, s0));
        }
    }
}

/// Every model of the spec satisfies its last clause.
pub open spec fn last_holds(s: Seq<Formula<Var<usize>>>, c: Formula<Var<usize>>) -> bool {
    forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, s) ==> formula_semantics(v, c)
}

/// Encode the associated clause of node `id` at time `k`. `false` if the
/// variables ran out (the encoding is then incomplete but still sound).
fn emit_at(e: &mut Enc, t: &Table, n: usize, id: usize, k: usize) -> (ok: bool)
    requires
        ctx_ok(t, n as nat),
        enc_ok(*old(e), t.sub@, n as nat),
        id < t.nodes@.len(),
        has_associated_clauses(t.sub@[id as int]),
        intervals_welldef(t.sub@[id as int]),
        k + complen_mltl(t.sub@[id as int]) <= n,
        enc_complete(*old(e), t.sub@, n as nat),
    ensures
        enc_ok(*final(e), t.sub@, n as nat),
        final(e).spec@ == old(e).spec@.push(associated_clause(t.sub@[id as int], k as nat)),
        ok ==> enc_complete(*final(e), t.sub@, n as nat),
{
    let ghost cnf0 = cnf_seqs(e.cnf@);
    let ghost spec0 = e.spec@;
    let ghost sub = t.sub@;
    let ghost gn = n as nat;
    let ghost f = sub[id as int];
    let ghost cl = associated_clause(f, k as nat);
    push_spec(e, Ghost(cl), Ghost(sub), Ghost(gn));
    proof {
        assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies formula_semantics(v, cl) by {
            models_all_push(v, old(e).spec@, cl);
        }
        assert(node_ok(t.nodes@, sub, id as int));
        complen_geq_one(f);
    }
    let ghost nb = nbase(sub, gn);
    reveal_with_fuel(formula_semantics, 3);
    match &t.nodes[id] {
        Node::True => {
            let x = bv(t, n, id, k);
            let nx: i32 = -x;
            proof {
                assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies dimacs_clause_sem(
                    ext_val(v, sub, gn, e.aux@),
                    seq![x],
                ) by {
                    let w = ext_val(v, sub, gn, e.aux@);
                    assert(formula_semantics(v, cl));
                    biimp_semantics(v, Formula::Atom((Mltl::<usize>::True, k as nat)), top());
                    ext_val_base(v, sub, gn, e.aux@, id as nat, k as nat);
                    lit_sem_pm(w, x, nx);
                    clause_sem_3(w, seq![x]);
                }
            }
            let c = vec![x];
            assert(c@ == seq![x]);
            add_clause(e, c, Ghost(sub), Ghost(gn));
            proof {
                assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(e.cnf@)) implies formula_semantics(
                    restrict(w, sub, gn),
                    cl,
                ) by {
                    let fin = cnf_seqs(e.cnf@);
                    assert(fin[cnf0.len() as int] == seq![x]);
                    models_contains(w, fin, seq![x]);
                    lit_sem_pm(w, x, nx);
                    clause_sem_3(w, seq![x]);
                    restrict_base(w, sub, gn, id as nat, k as nat);
                    biimp_semantics(restrict(w, sub, gn), Formula::Atom((Mltl::<usize>::True, k as nat)), top());
                }
                assert(cnf_seqs(e.cnf@).subrange(0, cnf0.len() as int) =~= cnf0);
                prefix_models(cnf0, cnf_seqs(e.cnf@));
                complete_after(cnf0, spec0, cnf_seqs(e.cnf@), sub, gn, cl);
            }
            true
        },
        Node::Not(ci) => {
            let ci = *ci;
            let x = bv(t, n, id, k);
            let nx: i32 = -x;
            let y = bv(t, n, ci, k);
            let ny: i32 = -y;
            proof {
                assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies {
                    &&& dimacs_clause_sem(ext_val(v, sub, gn, e.aux@), seq![nx, ny])
                    &&& dimacs_clause_sem(ext_val(v, sub, gn, e.aux@), seq![x, y])
                } by {
                    let w = ext_val(v, sub, gn, e.aux@);
                    assert(formula_semantics(v, cl));
                    biimp_semantics(v, Formula::Atom((f, k as nat)), Formula::Not(Box::new(Formula::Atom((sub[ci as int], k as nat)))));
                    ext_val_base(v, sub, gn, e.aux@, id as nat, k as nat);
                    ext_val_base(v, sub, gn, e.aux@, ci as nat, k as nat);
                    lit_sem_pm(w, x, nx);
                    lit_sem_pm(w, y, ny);
                    clause_sem_3(w, seq![nx, ny]);
                    clause_sem_3(w, seq![x, y]);
                }
            }
            let c1 = vec![nx, ny];
            assert(c1@ == seq![nx, ny]);
            add_clause(e, c1, Ghost(sub), Ghost(gn));
            let c2 = vec![x, y];
            assert(c2@ == seq![x, y]);
            add_clause(e, c2, Ghost(sub), Ghost(gn));
            proof {
                assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(e.cnf@)) implies formula_semantics(
                    restrict(w, sub, gn),
                    cl,
                ) by {
                    let fin = cnf_seqs(e.cnf@);
                    assert(fin[cnf0.len() as int] == seq![nx, ny]);
                    assert(fin[cnf0.len() as int + 1] == seq![x, y]);
                    models_contains(w, fin, seq![nx, ny]);
                    models_contains(w, fin, seq![x, y]);
                    lit_sem_pm(w, x, nx);
                    lit_sem_pm(w, y, ny);
                    clause_sem_3(w, seq![nx, ny]);
                    clause_sem_3(w, seq![x, y]);
                    restrict_base(w, sub, gn, id as nat, k as nat);
                    restrict_base(w, sub, gn, ci as nat, k as nat);
                    biimp_semantics(
                        restrict(w, sub, gn),
                        Formula::Atom((f, k as nat)),
                        Formula::Not(Box::new(Formula::Atom((sub[ci as int], k as nat)))),
                    );
                }
                assert(cnf_seqs(e.cnf@).subrange(0, cnf0.len() as int) =~= cnf0);
                prefix_models(cnf0, cnf_seqs(e.cnf@));
                complete_after(cnf0, spec0, cnf_seqs(e.cnf@), sub, gn, cl);
            }
            true
        },
        Node::And(ci, di) => {
            let ci = *ci;
            let di = *di;
            let x = bv(t, n, id, k);
            let nx: i32 = -x;
            let y = bv(t, n, ci, k);
            let ny: i32 = -y;
            let z = bv(t, n, di, k);
            let nz: i32 = -z;
            proof {
                assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies {
                    &&& dimacs_clause_sem(ext_val(v, sub, gn, e.aux@), seq![nx, y])
                    &&& dimacs_clause_sem(ext_val(v, sub, gn, e.aux@), seq![nx, z])
                    &&& dimacs_clause_sem(ext_val(v, sub, gn, e.aux@), seq![x, ny, nz])
                } by {
                    let w = ext_val(v, sub, gn, e.aux@);
                    assert(formula_semantics(v, cl));
                    biimp_semantics(
                        v,
                        Formula::Atom((f, k as nat)),
                        Formula::And(
                            Box::new(Formula::Atom((sub[ci as int], k as nat))),
                            Box::new(Formula::Atom((sub[di as int], k as nat))),
                        ),
                    );
                    ext_val_base(v, sub, gn, e.aux@, id as nat, k as nat);
                    ext_val_base(v, sub, gn, e.aux@, ci as nat, k as nat);
                    ext_val_base(v, sub, gn, e.aux@, di as nat, k as nat);
                    lit_sem_pm(w, x, nx);
                    lit_sem_pm(w, y, ny);
                    lit_sem_pm(w, z, nz);
                    clause_sem_3(w, seq![nx, y]);
                    clause_sem_3(w, seq![nx, z]);
                    clause_sem_3(w, seq![x, ny, nz]);
                }
            }
            let c1 = vec![nx, y];
            assert(c1@ == seq![nx, y]);
            add_clause(e, c1, Ghost(sub), Ghost(gn));
            let c2 = vec![nx, z];
            assert(c2@ == seq![nx, z]);
            add_clause(e, c2, Ghost(sub), Ghost(gn));
            let c3 = vec![x, ny, nz];
            assert(c3@ == seq![x, ny, nz]);
            add_clause(e, c3, Ghost(sub), Ghost(gn));
            proof {
                assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(e.cnf@)) implies formula_semantics(
                    restrict(w, sub, gn),
                    cl,
                ) by {
                    let fin = cnf_seqs(e.cnf@);
                    assert(fin[cnf0.len() as int] == seq![nx, y]);
                    assert(fin[cnf0.len() as int + 1] == seq![nx, z]);
                    assert(fin[cnf0.len() as int + 2] == seq![x, ny, nz]);
                    models_contains(w, fin, seq![nx, y]);
                    models_contains(w, fin, seq![nx, z]);
                    models_contains(w, fin, seq![x, ny, nz]);
                    lit_sem_pm(w, x, nx);
                    lit_sem_pm(w, y, ny);
                    lit_sem_pm(w, z, nz);
                    clause_sem_3(w, seq![nx, y]);
                    clause_sem_3(w, seq![nx, z]);
                    clause_sem_3(w, seq![x, ny, nz]);
                    restrict_base(w, sub, gn, id as nat, k as nat);
                    restrict_base(w, sub, gn, ci as nat, k as nat);
                    restrict_base(w, sub, gn, di as nat, k as nat);
                    biimp_semantics(
                        restrict(w, sub, gn),
                        Formula::Atom((f, k as nat)),
                        Formula::And(
                            Box::new(Formula::Atom((sub[ci as int], k as nat))),
                            Box::new(Formula::Atom((sub[di as int], k as nat))),
                        ),
                    );
                }
                assert(cnf_seqs(e.cnf@).subrange(0, cnf0.len() as int) =~= cnf0);
                prefix_models(cnf0, cnf_seqs(e.cnf@));
                complete_after(cnf0, spec0, cnf_seqs(e.cnf@), sub, gn, cl);
            }
            true
        },
        Node::Until(ci, a, b, di) => {
            let ci = *ci;
            let di = *di;
            proof {
                complen_geq_one(sub[di as int]);
                assert(complen_mltl(f) >= *b + 1);
            }
            let lb = *a + k;
            let ub = *b + k;
            let ok = emit_until_chain(e, t, n, id, k, ci, *a, *b, di, lb, ub);
            proof {
                if ok {
                    assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(e.cnf@)) implies formula_semantics(
                        restrict(w, sub, gn),
                        cl,
                    ) by {
                        biimp_semantics(
                            restrict(w, sub, gn),
                            Formula::Atom((f, k as nat)),
                            unroll_until(sub[ci as int], sub[di as int], lb as nat, ub as nat),
                        );
                    }
                    complete_after(cnf0, spec0, cnf_seqs(e.cnf@), sub, gn, cl);
                }
            }
            ok
        },
        Node::Prop(_) => {
            true
        },
    }
}

/// The value of a known variable under the extension.
pub open spec fn known_var(x: i32, nb: int, aux: Map<nat, AuxDef>, next: int) -> bool {
    1 <= x && (x as int) < next && (x as int <= nb || aux.contains_key(x as nat))
}

/// Encode `Atom(x) ↔ unroll_until φ ψ lb ub` (the Until node `id` at `k`).
fn emit_until_chain(
    e: &mut Enc,
    t: &Table,
    n: usize,
    id: usize,
    k: usize,
    ci: usize,
    a: usize,
    b: usize,
    di: usize,
    lb: usize,
    ub: usize,
) -> (ok: bool)
    requires
        ctx_ok(t, n as nat),
        enc_ok(*old(e), t.sub@, n as nat),
        id < t.nodes@.len(),
        ci < t.nodes@.len(),
        di < t.nodes@.len(),
        t.sub@[id as int] == Mltl::Until(Box::new(t.sub@[ci as int]), a, b, Box::new(t.sub@[di as int])),
        a <= b,
        lb == a + k,
        ub == b + k,
        ub < n,
        last_holds(old(e).spec@, associated_clause(t.sub@[id as int], k as nat)),
    ensures
        enc_ok(*final(e), t.sub@, n as nat),
        final(e).spec@ == old(e).spec@,
        ok ==> forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(final(e).cnf@)) ==> {
            &&& dimacs_models(w, cnf_seqs(old(e).cnf@))
            &&& restrict(w, t.sub@, n as nat)((t.sub@[id as int], k as nat)) == formula_semantics(
                restrict(w, t.sub@, n as nat),
                unroll_until(t.sub@[ci as int], t.sub@[di as int], lb as nat, ub as nat),
            )
        },
{
    let ghost cnf0 = cnf_seqs(e.cnf@);
    let ghost sub = t.sub@;
    let ghost gn = n as nat;
    let ghost nb = nbase(sub, gn);
    let ghost g = sub[ci as int];
    let ghost h = sub[di as int];
    let ghost f = sub[id as int];
    let ghost spec = e.spec@;
    let x = bv(t, n, id, k);
    let nx: i32 = -x;
    proof {
        assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, spec) implies ext_val(v, sub, gn, e.aux@)(
            x as nat,
        ) == formula_semantics(v, unroll_until(g, h, lb as nat, ub as nat)) by {
            assert(formula_semantics(v, associated_clause(f, k as nat)));
            biimp_semantics(v, Formula::Atom((f, k as nat)), unroll_until(g, h, lb as nat, ub as nat));
            ext_val_base(v, sub, gn, e.aux@, id as nat, k as nat);
        }
    }
    if lb == ub {
        let hb = bv(t, n, di, ub);
        let nhb: i32 = -hb;
        proof {
            assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies {
                &&& dimacs_clause_sem(ext_val(v, sub, gn, e.aux@), seq![nx, hb])
                &&& dimacs_clause_sem(ext_val(v, sub, gn, e.aux@), seq![x, nhb])
            } by {
                let w = ext_val(v, sub, gn, e.aux@);
                ext_val_base(v, sub, gn, e.aux@, di as nat, ub as nat);
                assert(w(x as nat) == formula_semantics(v, unroll_until(g, h, lb as nat, ub as nat)));
                lit_sem_pm(w, x, nx);
                lit_sem_pm(w, hb, nhb);
                clause_sem_3(w, seq![nx, hb]);
                clause_sem_3(w, seq![x, nhb]);
            }
        }
        let c1 = vec![nx, hb];
        assert(c1@ == seq![nx, hb]);
        add_clause(e, c1, Ghost(sub), Ghost(gn));
        let c2 = vec![x, nhb];
        assert(c2@ == seq![x, nhb]);
        add_clause(e, c2, Ghost(sub), Ghost(gn));
        proof {
            assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(e.cnf@)) implies {
                &&& dimacs_models(w, cnf0)
                &&& restrict(w, sub, gn)((f, k as nat)) == formula_semantics(
                    restrict(w, sub, gn),
                    unroll_until(g, h, lb as nat, ub as nat),
                )
            } by {
                let fin = cnf_seqs(e.cnf@);
                assert(fin == cnf0.push(seq![nx, hb]).push(seq![x, nhb]));
                assert(fin.subrange(0, cnf0.len() as int) =~= cnf0);
                models_prefix(w, cnf0, fin);
                assert(fin[cnf0.len() as int + 1] == seq![x, nhb]);
                assert(fin[cnf0.len() as int] == seq![nx, hb]);
                models_contains(w, fin, seq![nx, hb]);
                models_contains(w, fin, seq![x, nhb]);
                lit_sem_pm(w, x, nx);
                lit_sem_pm(w, hb, nhb);
                clause_sem_3(w, seq![nx, hb]);
                clause_sem_3(w, seq![x, nhb]);
                restrict_base(w, sub, gn, id as nat, k as nat);
                restrict_base(w, sub, gn, di as nat, ub as nat);
            }
        }
        return true;
    }
    let mut cur = x;
    let mut i = lb;
    let ghost mut chain: Seq<i32> = seq![x];
    while i < ub
        invariant
            cnf0.len() <= cnf_seqs(e.cnf@).len(),
            cnf_seqs(e.cnf@).subrange(0, cnf0.len() as int) == cnf0,
            chain.len() == i - lb + 1,
            chain[0] == x,
            chain[i - lb] == cur,
            forall|jj: int| 0 <= jj < chain.len() ==> #[trigger] chain[jj] > 0,
            i == ub ==> cur as int == bvar(gn, di as nat, ub as nat),
            forall|jj: int|
                0 <= jj < i - lb ==> #[trigger] step_ok(
                    cnf_seqs(e.cnf@),
                    chain[jj],
                    chain[jj + 1],
                    bvar(gn, di as nat, (lb + jj) as nat) as i32,
                    bvar(gn, ci as nat, (lb + jj) as nat) as i32,
                ),
            ctx_ok(t, n as nat),
            sub == t.sub@,
            gn == n as nat,
            nb == nbase(sub, gn),
            g == sub[ci as int],
            h == sub[di as int],
            ci < t.nodes@.len(),
            di < t.nodes@.len(),
            enc_ok(*e, sub, gn),
            e.spec@ == spec,
            spec == old(e).spec@,
            lb <= i <= ub,
            ub < n,
            known_var(cur, nb, e.aux@, e.next as int),
            forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, spec) ==> ext_val(v, sub, gn, e.aux@)(
                cur as nat,
            ) == formula_semantics(v, unroll_until(g, h, i as nat, ub as nat)),
        decreases ub - i,
    {
        let ghost f_start = cnf_seqs(e.cnf@);
        let ncur: i32 = -cur;
        let hi = bv(t, n, di, i);
        let nhi: i32 = -hi;
        let gi = bv(t, n, ci, i);
        let ngi: i32 = -gi;
        let ghost a1 = e.aux@;
        let nxt: i32;
        if i + 1 == ub {
            nxt = bv(t, n, di, ub);
            proof {
                assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, spec) implies ext_val(v, sub, gn, e.aux@)(
                    nxt as nat,
                ) == formula_semantics(v, unroll_until(g, h, (i + 1) as nat, ub as nat)) by {
                    ext_val_base(v, sub, gn, e.aux@, di as nat, ub as nat);
                }
            }
        } else {
            if e.next == i32::MAX {
                return false;
            }
            nxt = alloc_aux(e, Ghost((g, h, (i + 1) as nat, ub as nat)), Ghost(sub), Ghost(gn));
            proof {
                assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, spec) implies ext_val(v, sub, gn, e.aux@)(
                    nxt as nat,
                ) == formula_semantics(v, unroll_until(g, h, (i + 1) as nat, ub as nat)) by {
                    assert(e.aux@.contains_key(nxt as nat));
                    assert(e.aux@[nxt as nat] == (g, h, (i + 1) as nat, ub as nat));
                }
            }
        }
        let nnxt: i32 = -nxt;
        let ghost a2 = e.aux@;
        proof {
            assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies {
                &&& dimacs_clause_sem(ext_val(v, sub, gn, a2), seq![ncur, hi, gi])
                &&& dimacs_clause_sem(ext_val(v, sub, gn, a2), seq![ncur, hi, nxt])
                &&& dimacs_clause_sem(ext_val(v, sub, gn, a2), seq![cur, nhi])
                &&& dimacs_clause_sem(ext_val(v, sub, gn, a2), seq![cur, ngi, nnxt])
            } by {
                let w = ext_val(v, sub, gn, a2);
                ext_var_stable(v, sub, gn, a1, a2, cur as nat);
                ext_val_base(v, sub, gn, a2, di as nat, i as nat);
                ext_val_base(v, sub, gn, a2, ci as nat, i as nat);
                assert(w(cur as nat) == formula_semantics(v, unroll_until(g, h, i as nat, ub as nat)));
                assert(unroll_until(g, h, i as nat, ub as nat) == Formula::Or(
                    Box::new(Formula::Atom((h, i as nat))),
                    Box::new(Formula::And(
                        Box::new(Formula::Atom((g, i as nat))),
                        Box::new(unroll_until(g, h, (i + 1) as nat, ub as nat)),
                    )),
                ));
                reveal_with_fuel(formula_semantics, 3);
                lit_sem_pm(w, cur, ncur);
                lit_sem_pm(w, hi, nhi);
                lit_sem_pm(w, gi, ngi);
                lit_sem_pm(w, nxt, nnxt);
                clause_sem_3(w, seq![ncur, hi, gi]);
                clause_sem_3(w, seq![ncur, hi, nxt]);
                clause_sem_3(w, seq![cur, nhi]);
                clause_sem_3(w, seq![cur, ngi, nnxt]);
            }
        }
        let c1 = vec![ncur, hi, gi];
        assert(c1@ == seq![ncur, hi, gi]);
        add_clause(e, c1, Ghost(sub), Ghost(gn));
        let c2 = vec![ncur, hi, nxt];
        assert(c2@ == seq![ncur, hi, nxt]);
        add_clause(e, c2, Ghost(sub), Ghost(gn));
        let c3 = vec![cur, nhi];
        assert(c3@ == seq![cur, nhi]);
        add_clause(e, c3, Ghost(sub), Ghost(gn));
        let c4 = vec![cur, ngi, nnxt];
        assert(c4@ == seq![cur, ngi, nnxt]);
        let ghost f_before = cnf_seqs(e.cnf@);
        add_clause(e, c4, Ghost(sub), Ghost(gn));
        proof {
            let fin = cnf_seqs(e.cnf@);
            let f3 = f_before;
            let c1s = seq![ncur, hi, gi];
            let c2s = seq![ncur, hi, nxt];
            let c3s = seq![cur, nhi];
            let c4s = seq![cur, ngi, nnxt];
            assert(fin == f3.push(c4s));
            let new_chain = chain.push(nxt);
            let jn = (i - lb) as int;
            bvar_bound(gn, di as nat, i as nat, sub.len());
            bvar_bound(gn, ci as nat, i as nat, sub.len());
            assert(fin =~= f_start.push(c1s).push(c2s).push(c3s).push(c4s));
            assert(fin.subrange(0, f_start.len() as int) =~= f_start);
            assert(fin.subrange(0, cnf0.len() as int) =~= cnf0) by {
                assert(fin.subrange(0, cnf0.len() as int) =~= f_start.subrange(0, cnf0.len() as int));
            }
            assert(fin.contains(c4s)) by { assert(fin[f3.len() as int] == c4s); }
            assert(f3.len() >= 3);
            assert(fin.contains(c3s)) by { assert(fin[f3.len() - 1] == c3s); }
            assert(fin.contains(c2s)) by { assert(fin[f3.len() - 2] == c2s); }
            assert(fin.contains(c1s)) by { assert(fin[f3.len() - 3] == c1s); }
            assert(step_ok(fin, new_chain[jn], new_chain[jn + 1], bvar(gn, di as nat, (lb + jn) as nat) as i32, bvar(gn, ci as nat, (lb + jn) as nat) as i32));
            assert forall|jj: int| 0 <= jj < jn + 1 implies #[trigger] step_ok(
                fin,
                new_chain[jj],
                new_chain[jj + 1],
                bvar(gn, di as nat, (lb + jj) as nat) as i32,
                bvar(gn, ci as nat, (lb + jj) as nat) as i32,
            ) by {
                if jj < jn {
                    assert(new_chain[jj] == chain[jj] && new_chain[jj + 1] == chain[jj + 1]);
                    assert(step_ok(f_start, chain[jj], chain[jj + 1], bvar(gn, di as nat, (lb + jj) as nat) as i32, bvar(gn, ci as nat, (lb + jj) as nat) as i32));
                    step_ok_prefix(f_start, fin, chain[jj], chain[jj + 1], bvar(gn, di as nat, (lb + jj) as nat) as i32, bvar(gn, ci as nat, (lb + jj) as nat) as i32);
                }
            }
        }
        cur = nxt;
        proof { chain = chain.push(nxt); }
        i += 1;
    }
    proof {
        assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(e.cnf@)) implies {
            &&& dimacs_models(w, cnf0)
            &&& restrict(w, sub, gn)((f, k as nat)) == formula_semantics(
                restrict(w, sub, gn),
                unroll_until(g, h, lb as nat, ub as nat),
            )
        } by {
            models_prefix(w, cnf0, cnf_seqs(e.cnf@));
            chain_values(w, cnf_seqs(e.cnf@), chain, sub, gn, ci as nat, di as nat, lb as nat, ub as nat, 0);
            restrict_base(w, sub, gn, id as nat, k as nat);
        }
    }
    true
}

/// Encode `get_associated_clauses_at_node (sub[id]) alb aub`.
fn emit_node(e: &mut Enc, t: &Table, n: usize, id: usize, alb: usize, aub: usize) -> (ok: bool)
    requires
        ctx_ok(t, n as nat),
        enc_ok(*old(e), t.sub@, n as nat),
        id < t.nodes@.len(),
        intervals_welldef(t.sub@[id as int]),
        alb <= aub,
        aub + complen_mltl(t.sub@[id as int]) <= n,
        enc_complete(*old(e), t.sub@, n as nat),
    ensures
        enc_ok(*final(e), t.sub@, n as nat),
        ok ==> enc_complete(*final(e), t.sub@, n as nat),
        ok ==> final(e).spec@ == old(e).spec@ + get_associated_clauses_at_node(
            t.sub@[id as int],
            alb as nat,
            aub as nat,
        ),
{
    let ghost f = t.sub@[id as int];
    proof {
        get_associated_clauses_at_node_shape(f, alb as nat, aub as nat);
        assert(node_ok(t.nodes@, t.sub@, id as int));
        complen_geq_one(f);
    }
    match &t.nodes[id] {
        Node::Prop(_) => {
            assert(e.spec@ + get_associated_clauses_at_node(f, alb as nat, aub as nat) =~= e.spec@);
            return true;
        },
        _ => {},
    }
    let ghost s0 = e.spec@;
    let w = aub - alb;
    let mut j: usize = 0;
    while j <= w
        invariant
            ctx_ok(t, n as nat),
            enc_ok(*e, t.sub@, n as nat),
            enc_complete(*e, t.sub@, n as nat),
            id < t.nodes@.len(),
            f == t.sub@[id as int],
            has_associated_clauses(f),
            intervals_welldef(f),
            aub + complen_mltl(f) <= n,
            complen_mltl(f) >= 1,
            w == aub - alb,
            alb <= aub,
            j <= w + 1,
            e.spec@ == s0 + Seq::new(j as nat, |i: int| associated_clause(f, (aub - i) as nat)),
        decreases w + 1 - j,
    {
        let k = aub - j;
        if !emit_at(e, t, n, id, k) {
            return false;
        }
        assert(e.spec@ =~= s0 + Seq::new((j + 1) as nat, |i: int| associated_clause(f, (aub - i) as nat)));
        j += 1;
    }
    assert(e.spec@ =~= s0 + get_associated_clauses_at_node(f, alb as nat, aub as nat));
    true
}

/// Encode `fast_mltl_to_sat (sub[id]) alb aub`.
fn emit(e: &mut Enc, t: &Table, n: usize, id: usize, alb: usize, aub: usize) -> (ok: bool)
    requires
        ctx_ok(t, n as nat),
        enc_ok(*old(e), t.sub@, n as nat),
        id < t.nodes@.len(),
        intervals_welldef(t.sub@[id as int]),
        alb <= aub,
        aub + complen_mltl(t.sub@[id as int]) <= n,
        enc_complete(*old(e), t.sub@, n as nat),
    ensures
        enc_ok(*final(e), t.sub@, n as nat),
        ok ==> enc_complete(*final(e), t.sub@, n as nat),
        ok ==> final(e).spec@ == old(e).spec@ + fast_mltl_to_sat(t.sub@[id as int], alb as nat, aub as nat),
    decreases id,
{
    let ghost sub = t.sub@;
    let ghost f = sub[id as int];
    let ghost s0 = e.spec@;
    proof {
        assert(node_ok(t.nodes@, sub, id as int));
    }
    if !emit_node(e, t, n, id, alb, aub) {
        return false;
    }
    let ghost s1 = e.spec@;
    let ghost gc = get_associated_clauses_at_node(f, alb as nat, aub as nat);
    match &t.nodes[id] {
        Node::True => {
            true
        },
        Node::Prop(_) => {
            assert(gc =~= Seq::<Formula<Var<usize>>>::empty());
            assert(e.spec@ =~= s0 + fast_mltl_to_sat(f, alb as nat, aub as nat));
            true
        },
        Node::Not(c) => {
            let c = *c;
            if !emit(e, t, n, c, alb, aub) {
                return false;
            }
            assert(e.spec@ =~= s0 + (gc + fast_mltl_to_sat(sub[c as int], alb as nat, aub as nat)));
            true
        },
        Node::And(c, d) => {
            let c = *c;
            let d = *d;
            if !emit(e, t, n, c, alb, aub) {
                return false;
            }
            if !emit(e, t, n, d, alb, aub) {
                return false;
            }
            assert(e.spec@ =~= s0 + (gc + fast_mltl_to_sat(sub[c as int], alb as nat, aub as nat) + fast_mltl_to_sat(
                sub[d as int],
                alb as nat,
                aub as nat,
            )));
            true
        },
        Node::Until(c, a, b, d) => {
            let c = *c;
            let a = *a;
            let b = *b;
            let d = *d;
            proof {
                complen_geq_one(sub[c as int]);
                complen_geq_one(sub[d as int]);
            }
            let ghost mid: Seq<Formula<Var<usize>>> = if a == b {
                Seq::empty()
            } else {
                fast_mltl_to_sat(sub[c as int], (alb + a) as nat, nat_sub((aub + b) as nat, 1))
            };
            if a != b {
                if !emit(e, t, n, c, alb + a, aub + b - 1) {
                    return false;
                }
            }
            assert(e.spec@ =~= s1 + mid);
            if !emit(e, t, n, d, alb + a, aub + b) {
                return false;
            }
            assert(e.spec@ =~= s0 + (gc + mid + fast_mltl_to_sat(sub[d as int], (alb + a) as nat, (aub + b) as nat)));
            true
        },
    }
}

/// An encoding of `MLTL_SAT_LEN φ (complen φ)` as CNF. Built only by
/// [`encode`], which establishes `inv`.
pub struct Encoding {
    pub(crate) cnf: Vec<Vec<i32>>,
    pub(crate) table: Table,
    /// `complen φ`: the trace length.
    pub(crate) n: usize,
    pub(crate) phi: Mltl<usize>,
    /// Table id of `convert_bnf φ`.
    pub(crate) root: usize,
}

impl Encoding {
    /// The encoded formula.
    pub open(crate) spec fn formula(&self) -> Mltl<usize> {
        self.phi
    }

    pub open(crate) spec fn cnf_spec(&self) -> Seq<Seq<i32>> {
        cnf_seqs(self.cnf@)
    }

    /// If the formula is satisfiable on a trace of length `complen`, the CNF
    /// is satisfiable.
    pub open(crate) spec fn inv(&self) -> bool {
        &&& intervals_welldef(self.phi)
        &&& self.n as nat == complen_mltl(self.phi)
        &&& ctx_ok(&self.table, self.n as nat)
        &&& (mltl_sat_len(self.phi, complen_mltl(self.phi)) ==> dimacs_satisfiable(cnf_seqs(self.cnf@)))
        &&& self.root < self.table.sub@.len()
        &&& self.table.sub@[self.root as int] == convert_bnf_spec(self.phi)
        &&& forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(self.cnf@)) ==> {
            &&& models_all(restrict(w, self.table.sub@, self.n as nat), fast_mltl_to_sat(convert_bnf_spec(self.phi), 0, 0))
            &&& restrict(w, self.table.sub@, self.n as nat)((convert_bnf_spec(self.phi), 0nat))
        }
    }

    pub fn cnf(&self) -> (r: &Vec<Vec<i32>>)
        ensures
            cnf_seqs(r@) == self.cnf_spec(),
    {
        &self.cnf
    }
}

/// Encode a formula. `None` if its intervals are ill formed or the
/// encoding would exceed `i32` variables.
///
/// Guarantee: if `φ` is satisfiable on a trace of length `complen φ`, the
/// CNF is satisfiable. So an UNSAT CNF proves `φ` has no such trace.
pub fn encode(f: &Mltl<usize>) -> (r: Option<Encoding>)
    ensures
        match r {
            Some(enc) => {
                // It encodes `f`, whose intervals are well formed, ...
                &&& enc.formula() == *f
                &&& intervals_welldef(*f)
                // ... and its CNF is satisfiable exactly when some trace of
                // length `complen f` satisfies `f`.
                &&& dimacs_satisfiable(enc.cnf_spec()) <==> mltl_sat_len(*f, complen_mltl(*f))
                // (Internal invariant, needed by `decide`.)
                &&& enc.inv()
            },
            // `f` has an ill-formed interval, or needs more than `i32` variables.
            None => true,
        },
{
    if !check_welldef(f) {
        return None;
    }
    let g = convert_bnf(f);
    let n = match complen_exec(&g) {
        Some(n) => n,
        None => return None,
    };
    proof {
        complen_geq_one(g);
    }
    let mut t = Table { nodes: Vec::new(), sub: Ghost(Seq::empty()) };
    let root = intern(&mut t, &g);
    let len = t.nodes.len();
    let nb = match len.checked_mul(n) {
        Some(nb) => nb,
        None => return None,
    };
    if nb >= (i32::MAX - 1) as usize {
        return None;
    }
    let ghost sub = t.sub@;
    let ghost gn = n as nat;
    let mut e = Enc { cnf: Vec::new(), next: (nb + 1) as i32, aux: Ghost(Map::empty()), spec: Ghost(Seq::empty()) };
    proof {
        assert(cnf_seqs(e.cnf@) =~= Seq::<Seq<i32>>::empty());
    }
    if !emit(&mut e, &t, n, root, 0, 0) {
        return None;
    }
    let ghost body = fast_mltl_to_sat(g, 0, 0);
    assert(e.spec@ =~= body);
    let x = bv(&t, n, root, 0);
    let ghost top_atom = Formula::Atom((g, 0nat));
    push_spec(&mut e, Ghost(top_atom), Ghost(sub), Ghost(gn));
    proof {
        assert forall|v: spec_fn(Var<usize>) -> bool| #[trigger] models_all(v, e.spec@) implies dimacs_clause_sem(
            ext_val(v, sub, gn, e.aux@),
            seq![x],
        ) by {
            models_all_push(v, body, top_atom);
            ext_val_base(v, sub, gn, e.aux@, root as nat, 0);
            clause_sem_3(ext_val(v, sub, gn, e.aux@), seq![x]);
        }
    }
    let c = vec![x];
    assert(c@ == seq![x]);
    let ghost cnf_body = cnf_seqs(e.cnf@);
    add_clause(&mut e, c, Ghost(sub), Ghost(gn));
    proof {
        assert forall|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(e.cnf@)) implies {
            &&& models_all(restrict(w, sub, gn), body)
            &&& restrict(w, sub, gn)((g, 0nat))
        } by {
            let fin = cnf_seqs(e.cnf@);
            assert(fin.subrange(0, cnf_body.len() as int) =~= cnf_body);
            models_prefix(w, cnf_body, fin);
            assert(fin[cnf_body.len() as int] == seq![x]);
            models_contains(w, fin, seq![x]);
            clause_sem_3(w, seq![x]);
            restrict_base(w, sub, gn, root as nat, 0);
        }
        if mltl_sat_len(*f, complen_mltl(*f)) {
            soundness_fast_mltl_to_sat_root_complen(*f);
            let rootl = fast_mltl_to_sat_root(*f);
            let v = choose|v: spec_fn(Var<usize>) -> bool| #[trigger] models_set(v, rootl.to_set());
            models_set_to_set(v, rootl);
            models_all_append(v, seq![top_atom], body);
            assert(formula_semantics(v, seq![top_atom][0]));
            models_all_push(v, body, top_atom);
            assert(models_all(v, e.spec@));
            assert(dimacs_models(ext_val(v, sub, gn, e.aux@), cnf_seqs(e.cnf@)));
        }
    }
    let enc = Encoding { cnf: e.cnf, table: t, n, phi: clone_mltl(f), root };
    proof {
        enc.equisatisfiable();
    }
    Some(enc)
}

} // verus!
