//! From names to atom numbers (GRAMMAR.md §5).
//!
//! `pN` (N written without leading zeros) is atom N. Every other name gets
//! the next free number, in order of first appearance, starting after the
//! largest `pN` in the formula. Proved: different names get different
//! numbers (`number_injective`), and a formula and its numbered version have
//! the same truth value on traces that agree (`lemma_numbering_semantics`).
use vstd::prelude::*;
use mltl_core::mltl::*;
use crate::lexer::*;
use crate::grammar::*;
use crate::parser::*;
use crate::printer::*;

verus! {

broadcast use vstd::set::group_set_lemmas;

/// `Some(N)` if the name is `p` followed by the digits of N (no leading zeros).
pub open spec fn pnum(n: Seq<u8>) -> Option<nat> {
    if n.len() >= 2 && n[0] == 112 && n.drop_first() == digits(digits_value(n, 1, n.len())) {
        Some(digits_value(n, 1, n.len()))
    } else {
        None
    }
}

/// The table: names (none of the form `pN`) and their numbers.
pub type SpecTable = Seq<(Seq<u8>, usize)>;

pub open spec fn table_view(t: Seq<(Vec<u8>, usize)>) -> SpecTable {
    t.map_values(|e: (Vec<u8>, usize)| (e.0@, e.1))
}

/// Whether `n` has an entry in the table.
pub open spec fn has_entry(t: SpecTable, n: Seq<u8>) -> bool {
    exists|j: int| 0 <= j < t.len() && (#[trigger] t[j]).0 == n
}

/// The position of an entry for `n` (meaningful when `has_entry`).
pub open spec fn entry_index(t: SpecTable, n: Seq<u8>) -> int {
    choose|j: int| 0 <= j < t.len() && (#[trigger] t[j]).0 == n
}

pub open spec fn lookup(t: SpecTable, n: Seq<u8>) -> Option<usize> {
    if has_entry(t, n) { Some(t[entry_index(t, n)].1) } else { None }
}

/// The number of name `n`.
pub open spec fn number_of(t: SpecTable, n: Seq<u8>) -> usize {
    match pnum(n) {
        Some(v) => v as usize,
        None => match lookup(t, n) { Some(id) => id, None => 0 },
    }
}

/// `f` with every atom `n` replaced by `num(n)`.
pub open spec fn map_atoms(f: SpecFormula, num: spec_fn(Seq<u8>) -> usize) -> Mltl<usize>
    decreases f,
{
    match f {
        Mltl::True => Mltl::True,
        Mltl::False => Mltl::False,
        Mltl::Prop(n) => Mltl::Prop(num(n)),
        Mltl::Not(g) => Mltl::Not(Box::new(map_atoms(*g, num))),
        Mltl::And(g, h) => Mltl::And(Box::new(map_atoms(*g, num)), Box::new(map_atoms(*h, num))),
        Mltl::Or(g, h) => Mltl::Or(Box::new(map_atoms(*g, num)), Box::new(map_atoms(*h, num))),
        Mltl::Future(a, b, g) => Mltl::Future(a, b, Box::new(map_atoms(*g, num))),
        Mltl::Global(a, b, g) => Mltl::Global(a, b, Box::new(map_atoms(*g, num))),
        Mltl::Until(g, a, b, h) => Mltl::Until(Box::new(map_atoms(*g, num)), a, b, Box::new(map_atoms(*h, num))),
        Mltl::Release(g, a, b, h) => Mltl::Release(Box::new(map_atoms(*g, num)), a, b, Box::new(map_atoms(*h, num))),
    }
}

/// The numbering of table `t`, as a function.
pub open spec fn numbering(t: SpecTable) -> spec_fn(Seq<u8>) -> usize {
    |n: Seq<u8>| number_of(t, n)
}

/// Different atoms of `f` get different numbers.
pub open spec fn number_injective(f: SpecFormula, t: SpecTable) -> bool {
    forall|n1: Seq<u8>, n2: Seq<u8>| atoms_mltl(f).contains(n1) && atoms_mltl(f).contains(n2)
        && #[trigger] number_of(t, n1) == #[trigger] number_of(t, n2) ==> n1 == n2
}

// ---------------------------------------------------------------------------
// Semantics
// ---------------------------------------------------------------------------

/// The named trace and the numbered trace agree on `f`'s atoms: at every
/// step, atom `n` holds in the first exactly when `num(n)` holds in the second.
pub open spec fn traces_agree(pi: Seq<Set<Seq<u8>>>, rho: Seq<Set<usize>>, atoms: Set<Seq<u8>>,
    num: spec_fn(Seq<u8>) -> usize) -> bool {
    pi.len() == rho.len()
    && forall|i: int, n: Seq<u8>| 0 <= i < pi.len() && atoms.contains(n)
        ==> (#[trigger] pi[i].contains(n) <==> rho[i].contains(num(n)))
}

proof fn lemma_agree_drop(pi: Seq<Set<Seq<u8>>>, rho: Seq<Set<usize>>, atoms: Set<Seq<u8>>,
    sub: Set<Seq<u8>>, num: spec_fn(Seq<u8>) -> usize, k: nat)
    requires
        traces_agree(pi, rho, atoms, num),
        sub.subset_of(atoms),
    ensures
        traces_agree(drop(pi, k), drop(rho, k), sub, num),
{
    lemma_drop_len(pi, k);
    lemma_drop_len(rho, k);
    assert forall|i: int, n: Seq<u8>| 0 <= i < drop(pi, k).len() && sub.contains(n)
        implies (#[trigger] drop(pi, k)[i].contains(n) <==> drop(rho, k)[i].contains(num(n))) by {
        assert(drop(pi, k)[i] == pi[i + k]);
        assert(drop(rho, k)[i] == rho[i + k]);
        assert(pi[i + k].contains(n) <==> rho[i + k].contains(num(n)));
    }
}

/// **Truth is preserved.** On traces that agree on `f`'s atoms, `f` and its
/// numbered version have the same truth value.
pub proof fn lemma_numbering_semantics(pi: Seq<Set<Seq<u8>>>, rho: Seq<Set<usize>>, f: SpecFormula,
    num: spec_fn(Seq<u8>) -> usize)
    requires
        traces_agree(pi, rho, atoms_mltl(f), num),
    ensures
        semantics_mltl(pi, f) == semantics_mltl(rho, map_atoms(f, num)),
    decreases f,
{
    let g = map_atoms(f, num);
    match f {
        Mltl::True | Mltl::False => {},
        Mltl::Prop(n) => {
            if pi.len() > 0 {
                assert(pi[0].contains(n) <==> rho[0].contains(num(n)));
            }
        },
        Mltl::Not(a) => {
            lemma_numbering_semantics(pi, rho, *a, num);
        },
        Mltl::And(a, b) | Mltl::Or(a, b) => {
            lemma_agree_drop(pi, rho, atoms_mltl(f), atoms_mltl(*a), num, 0);
            lemma_agree_drop(pi, rho, atoms_mltl(f), atoms_mltl(*b), num, 0);
            lemma_drop_zero(pi);
            lemma_drop_zero(rho);
            lemma_numbering_semantics(pi, rho, *a, num);
            lemma_numbering_semantics(pi, rho, *b, num);
        },
        Mltl::Future(x, y, a) | Mltl::Global(x, y, a) => {
            assert forall|k: nat| #![trigger drop(pi, k)] #![trigger drop(rho, k)] semantics_mltl(drop(pi, k), *a) == semantics_mltl(drop(rho, k), map_atoms(*a, num)) by {
                lemma_agree_drop(pi, rho, atoms_mltl(f), atoms_mltl(*a), num, k);
                lemma_numbering_semantics(drop(pi, k), drop(rho, k), *a, num);
            }
            assert forall|k: nat| #[trigger] drop(rho, k).len() == drop(pi, k).len() by {
                lemma_drop_len(pi, k);
                lemma_drop_len(rho, k);
            }
            assert(semantics_mltl(pi, f) == semantics_mltl(rho, g));
        },
        Mltl::Until(a, x, y, b) | Mltl::Release(a, x, y, b) => {
            assert forall|k: nat| #![trigger drop(pi, k)] #![trigger drop(rho, k)] semantics_mltl(drop(pi, k), *a) == semantics_mltl(drop(rho, k), map_atoms(*a, num))
                && semantics_mltl(drop(pi, k), *b) == semantics_mltl(drop(rho, k), map_atoms(*b, num)) by {
                lemma_agree_drop(pi, rho, atoms_mltl(f), atoms_mltl(*a), num, k);
                lemma_agree_drop(pi, rho, atoms_mltl(f), atoms_mltl(*b), num, k);
                lemma_numbering_semantics(drop(pi, k), drop(rho, k), *a, num);
                lemma_numbering_semantics(drop(pi, k), drop(rho, k), *b, num);
            }
            assert(semantics_mltl(pi, f) == semantics_mltl(rho, g));
        },
    }
}


// ---------------------------------------------------------------------------
// Recognising `pN`
// ---------------------------------------------------------------------------

proof fn lemma_digits_first_zero(v: nat)
    ensures
        digits(v)[0] == 48 ==> v == 0,
    decreases v,
{
    if v >= 10 {
        lemma_digits_first_zero(v / 10);
        lemma_digits_len_pos(v / 10);
        assert(digits(v)[0] == digits(v / 10)[0]);
    }
}

proof fn lemma_digits_len_pos(v: nat)
    ensures
        digits(v).len() >= 1,
    decreases v,
{
    if v >= 10 { lemma_digits_len_pos(v / 10); }
}

/// A digit string without a leading zero is the decimal form of its value.
proof fn lemma_digits_canonical(s: Seq<u8>, i: nat, j: nat)
    requires
        i < j <= s.len(),
        forall|k: int| i <= k < j ==> is_digit(#[trigger] s[k]),
        s[i as int] != 48 || j == i + 1,
    ensures
        digits(digits_value(s, i, j)) == s.subrange(i as int, j as int),
    decreases j - i,
{
    let v = digits_value(s, i, j);
    let d = (s[j - 1] - 48) as nat;
    assert(v == digits_value(s, i, (j - 1) as nat) * 10 + d);
    if j == i + 1 {
        assert(digits_value(s, i, i) == 0);
        assert(digits(v) =~= s.subrange(i as int, j as int));
    } else {
        lemma_digits_canonical(s, i, (j - 1) as nat);
        let w = digits_value(s, i, (j - 1) as nat);
        // the leading digit is not zero, so w >= 1 and v >= 10
        lemma_digits_value_mono(s, i, i + 1, (j - 1) as nat);
        assert(digits_value(s, i, i + 1) == (s[i as int] - 48) as nat) by {
            assert(digits_value(s, i, i) == 0);
        }
        assert(w >= 1);
        assert(v / 10 == w && v % 10 == d) by (nonlinear_arith)
            requires v == w * 10 + d, d < 10;
        assert(digits(v) == digits(w) + seq![(48 + d) as u8]);
        assert(digits(v) =~= s.subrange(i as int, j as int));
    }
}

/// `pnum` identifies the name: two names with the same `pN` value are equal.
pub(crate) proof fn lemma_pnum_injective(n1: Seq<u8>, n2: Seq<u8>)
    requires
        pnum(n1) is Some,
        pnum(n1) == pnum(n2),
    ensures
        n1 == n2,
{
    assert(n1 =~= seq![n1[0]] + n1.drop_first());
    assert(n2 =~= seq![n2[0]] + n2.drop_first());
}

/// Whether `n` is a `pN` name, and its value N; `overflow` if N > usize::MAX.
pub(crate) fn exec_pnum(n: &Vec<u8>) -> (r: (bool, bool, usize))
    ensures
        !r.0 ==> pnum(n@) is None,
        r.0 && !r.1 ==> pnum(n@) == Some(r.2 as nat),
        r.0 && r.1 ==> pnum(n@) is Some && (pnum(n@)->Some_0) > usize::MAX,
{
    let len = n.len();
    if len < 2 || n[0] != 112 {
        return (false, false, 0);
    }
    let mut k = 1;
    while k < len
        invariant
            1 <= k <= len, len == n.len(),
            forall|m: int| 1 <= m < k ==> is_digit(#[trigger] n@[m]),
        decreases len - k,
    {
        if !(48 <= n[k] && n[k] <= 57) {
            proof {
                lemma_digits(digits_value(n@, 1, len as nat));
                assert(n@.drop_first()[k - 1] == n@[k as int]);
                if n@.drop_first() == digits(digits_value(n@, 1, len as nat)) {
                    assert(is_digit(digits(digits_value(n@, 1, len as nat))[k - 1]));
                }
            }
            return (false, false, 0);
        }
        k = k + 1;
    }
    if n[1] == 48 && len > 2 {
        proof {
            let v = digits_value(n@, 1, len as nat);
            lemma_digits_first_zero(v);
            if n@.drop_first() == digits(v) {
                assert(digits(v)[0] == n@[1]);
                assert(digits(0nat).len() == 1);
            }
        }
        return (false, false, 0);
    }
    proof {
        lemma_digits_canonical(n@, 1, len as nat);
        assert(n@.drop_first() =~= n@.subrange(1, len as int));
    }
    // value, with overflow detection
    let mut v: usize = 0;
    let mut overflow = false;
    let mut j = 1;
    proof { assert(digits_value(n@, 1, 1) == 0); }
    while j < len
        invariant
            1 <= j <= len, len == n.len(),
            forall|m: int| 1 <= m < len ==> is_digit(#[trigger] n@[m]),
            !overflow ==> v == digits_value(n@, 1, j as nat),
            overflow ==> digits_value(n@, 1, j as nat) > usize::MAX,
        decreases len - j,
    {
        let d = (n[j] - 48) as usize;
        proof { assert(digits_value(n@, 1, (j + 1) as nat) == digits_value(n@, 1, j as nat) * 10 + d); }
        if !overflow {
            if v > (usize::MAX - d) / 10 {
                overflow = true;
                proof {
                    assert(v * 10 + d > usize::MAX) by (nonlinear_arith)
                        requires v > (usize::MAX - d) / 10, d <= 9;
                }
            } else {
                proof {
                    assert(v * 10 + d <= usize::MAX) by (nonlinear_arith)
                        requires v <= (usize::MAX - d) / 10, d <= 9;
                }
                v = v * 10 + d;
            }
        } else {
            proof {
                assert(digits_value(n@, 1, j as nat) * 10 + d >= digits_value(n@, 1, j as nat)) by (nonlinear_arith);
            }
        }
        j = j + 1;
    }
    (true, overflow, v)
}

// ---------------------------------------------------------------------------
// The largest `pN`
// ---------------------------------------------------------------------------

/// Every `pN` atom of `f` has N below `lo`.
pub open spec fn pn_below(f: SpecFormula, lo: nat) -> bool {
    forall|n: Seq<u8>| #[trigger] atoms_mltl(f).contains(n) && pnum(n) is Some ==> (pnum(n)->Some_0) < lo
}

/// Some `pN` atom of `f` has N ≥ usize::MAX, which leaves no number free
/// after it (such a formula can't be numbered).
pub open spec fn pn_too_large(f: SpecFormula) -> bool {
    exists|n: Seq<u8>| #[trigger] atoms_mltl(f).contains(n) && pnum(n) is Some && (pnum(n)->Some_0) >= usize::MAX
}

/// `Ok(m)`: every `pN` atom has N below `m` (0 if there are none).
pub(crate) fn pn_bound(f: &ExecFormula) -> (r: Result<usize, ()>)
    ensures
        r is Ok ==> pn_below(view_f(*f), (r->Ok_0) as nat),
        r is Err ==> pn_too_large(view_f(*f)),
    decreases f,
{
    let ghost vf = view_f(*f);
    match f {
        Mltl::True => { proof { assert(atoms_mltl(vf) =~= Set::<Seq<u8>>::empty()); } Ok(0) },
        Mltl::False => { proof { assert(atoms_mltl(vf) =~= Set::<Seq<u8>>::empty()); } Ok(0) },
        Mltl::Prop(n) => {
            let (is_pn, overflow, v) = exec_pnum(n);
            proof { assert(atoms_mltl(vf) =~= Set::empty().insert(n@)); assert(atoms_mltl(vf).contains(n@)); }
            if !is_pn { Ok(0) }
            else if overflow || v == usize::MAX { Err(()) }
            else { Ok(v + 1) }
        },
        Mltl::Not(g) => { proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g))); } pn_bound(g) },
        Mltl::Future(_, _, g) => { proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g))); } pn_bound(g) },
        Mltl::Global(_, _, g) => { proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g))); } pn_bound(g) },
        Mltl::And(g, h) => {
            proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g)).union(atoms_mltl(view_f(**h)))); }
            let a = pn_bound(g); let b = pn_bound(h); combine_bounds(f, g, h, a, b)
        },
        Mltl::Or(g, h) => {
            proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g)).union(atoms_mltl(view_f(**h)))); }
            let a = pn_bound(g); let b = pn_bound(h); combine_bounds(f, g, h, a, b)
        },
        Mltl::Until(g, _, _, h) => {
            proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g)).union(atoms_mltl(view_f(**h)))); }
            let a = pn_bound(g); let b = pn_bound(h); combine_bounds(f, g, h, a, b)
        },
        Mltl::Release(g, _, _, h) => {
            proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g)).union(atoms_mltl(view_f(**h)))); }
            let a = pn_bound(g); let b = pn_bound(h); combine_bounds(f, g, h, a, b)
        },
    }
}

/// Combines the bounds of `g` and `h` for a node whose atoms are theirs.
fn combine_bounds(f: &ExecFormula, g: &ExecFormula, h: &ExecFormula, a: Result<usize, ()>, b: Result<usize, ()>)
    -> (r: Result<usize, ()>)
    requires
        atoms_mltl(view_f(*f)) == atoms_mltl(view_f(*g)).union(atoms_mltl(view_f(*h))),
        a is Ok ==> pn_below(view_f(*g), (a->Ok_0) as nat),
        a is Err ==> pn_too_large(view_f(*g)),
        b is Ok ==> pn_below(view_f(*h), (b->Ok_0) as nat),
        b is Err ==> pn_too_large(view_f(*h)),
    ensures
        r is Ok ==> pn_below(view_f(*f), (r->Ok_0) as nat),
        r is Err ==> pn_too_large(view_f(*f)),
{
    match (a, b) {
        (Ok(x), Ok(y)) => Ok(if x >= y { x } else { y }),
        _ => {
            proof {
                if a is Err {
                    let n = choose|n: Seq<u8>| #[trigger] atoms_mltl(view_f(*g)).contains(n) && pnum(n) is Some
                        && (pnum(n)->Some_0) >= usize::MAX;
                    assert(atoms_mltl(view_f(*f)).contains(n));
                } else {
                    let n = choose|n: Seq<u8>| #[trigger] atoms_mltl(view_f(*h)).contains(n) && pnum(n) is Some
                        && (pnum(n)->Some_0) >= usize::MAX;
                    assert(atoms_mltl(view_f(*f)).contains(n));
                }
            }
            Err(())
        },
    }
}


// ---------------------------------------------------------------------------
// Numbering
// ---------------------------------------------------------------------------

/// The table is consistent: names are not `pN` names and are distinct;
/// numbers are distinct, at least `lo` (above every `pN`), and below `next`.
pub open spec fn table_ok(t: SpecTable, lo: nat, next: nat) -> bool {
    &&& lo <= next
    &&& forall|j: int| 0 <= j < t.len() ==> pnum((#[trigger] t[j]).0) is None && lo <= t[j].1 < next
    &&& forall|j1: int, j2: int| 0 <= j1 < t.len() && 0 <= j2 < t.len() && j1 != j2
        ==> (#[trigger] t[j1]).0 != (#[trigger] t[j2]).0 && t[j1].1 != t[j2].1
}

/// `t2` extends `t1`.
pub open spec fn extends(t1: SpecTable, t2: SpecTable) -> bool {
    t1.len() <= t2.len() && forall|j: int| 0 <= j < t1.len() ==> #[trigger] t2[j] == t1[j]
}

/// Every non-`pN` atom of `f` has a table entry.
pub open spec fn resolved(f: SpecFormula, t: SpecTable) -> bool {
    forall|n: Seq<u8>| #[trigger] atoms_mltl(f).contains(n) && pnum(n) is None ==> lookup(t, n) is Some
}

pub(crate) proof fn lemma_lookup_at(t: SpecTable, lo: nat, next: nat, j: int)
    requires
        table_ok(t, lo, next),
        0 <= j < t.len(),
    ensures
        lookup(t, t[j].0) == Some(t[j].1),
{
    let n = t[j].0;
    assert(t[j].0 == n);
    assert(has_entry(t, n));
    let j2 = entry_index(t, n);
    if j2 != j {
        assert(t[j2].0 != t[j].0);
    }
}

pub(crate) proof fn lemma_lookup_extends(t1: SpecTable, t2: SpecTable, lo: nat, next: nat, n: Seq<u8>)
    requires
        table_ok(t2, lo, next),
        extends(t1, t2),
        lookup(t1, n) is Some,
    ensures
        lookup(t2, n) == lookup(t1, n),
{
    let j = entry_index(t1, n);
    assert(t2[j] == t1[j]);
    assert(t2[j].0 == n);
    lemma_lookup_at(t2, lo, next, j);
}

pub proof fn lemma_map_atoms_ext(f: SpecFormula, num1: spec_fn(Seq<u8>) -> usize, num2: spec_fn(Seq<u8>) -> usize)
    requires
        forall|n: Seq<u8>| #[trigger] atoms_mltl(f).contains(n) ==> num1(n) == num2(n),
    ensures
        map_atoms(f, num1) == map_atoms(f, num2),
    decreases f,
{
    match f {
        Mltl::True | Mltl::False => {},
        Mltl::Prop(n) => { assert(atoms_mltl(f).contains(n)); },
        Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => {
            assert forall|n: Seq<u8>| #[trigger] atoms_mltl(*g).contains(n) implies num1(n) == num2(n) by {
                assert(atoms_mltl(f).contains(n));
            }
            lemma_map_atoms_ext(*g, num1, num2);
        },
        Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) => {
            assert forall|n: Seq<u8>| #[trigger] atoms_mltl(*g).contains(n) implies num1(n) == num2(n) by {
                assert(atoms_mltl(f).contains(n));
            }
            assert forall|n: Seq<u8>| #[trigger] atoms_mltl(*h).contains(n) implies num1(n) == num2(n) by {
                assert(atoms_mltl(f).contains(n));
            }
            lemma_map_atoms_ext(*g, num1, num2);
            lemma_map_atoms_ext(*h, num1, num2);
        },
    }
}

/// Numbers of resolved atoms don't change when the table grows.
proof fn lemma_numbers_stable(f: SpecFormula, t1: SpecTable, t2: SpecTable, lo: nat, next: nat)
    requires
        resolved(f, t1),
        extends(t1, t2),
        table_ok(t2, lo, next),
    ensures
        map_atoms(f, numbering(t1)) == map_atoms(f, numbering(t2)),
        resolved(f, t2),
{
    assert forall|n: Seq<u8>| #[trigger] atoms_mltl(f).contains(n) implies numbering(t1)(n) == numbering(t2)(n) by {
        if pnum(n) is None {
            lemma_lookup_extends(t1, t2, lo, next, n);
        }
    }
    lemma_map_atoms_ext(f, numbering(t1), numbering(t2));
    assert forall|n: Seq<u8>| #[trigger] atoms_mltl(f).contains(n) && pnum(n) is None implies lookup(t2, n) is Some by {
        lemma_lookup_extends(t1, t2, lo, next, n);
    }
}

pub(crate) fn eq_bytes(a: &Vec<u8>, b: &Vec<u8>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut k = 0;
    while k < a.len()
        invariant
            k <= a.len(), a.len() == b.len(),
            forall|m: int| 0 <= m < k ==> a@[m] == b@[m],
        decreases a.len() - k,
    {
        if a[k] != b[k] {
            return false;
        }
        k = k + 1;
    }
    proof { assert(a@ =~= b@); }
    true
}

/// The number of `n` in the table, if it has one.
pub(crate) fn find(t: &Vec<(Vec<u8>, usize)>, n: &Vec<u8>, Ghost(lo): Ghost<nat>, Ghost(next): Ghost<nat>) -> (r: Option<usize>)
    requires
        table_ok(table_view(t@), lo, next),
    ensures
        r == lookup(table_view(t@), n@),
{
    let ghost tv = table_view(t@);
    let mut k = 0;
    while k < t.len()
        invariant
            k <= t.len(), tv == table_view(t@), table_ok(tv, lo, next),
            forall|m: int| 0 <= m < k ==> (#[trigger] tv[m]).0 != n@,
        decreases t.len() - k,
    {
        proof { assert(tv[k as int] == (t@[k as int].0@, t@[k as int].1)); }
        if eq_bytes(&t[k].0, n) {
            proof { lemma_lookup_at(tv, lo, next, k as int); }
            return Some(t[k].1);
        }
        k = k + 1;
    }
    None
}

/// Assigns numbers to `f`'s atoms, extending the table.
pub(crate) fn assign(f: &ExecFormula, t: &mut Vec<(Vec<u8>, usize)>, next: &mut usize, Ghost(lo): Ghost<nat>)
    -> (r: Option<Mltl<usize>>)
    requires
        table_ok(table_view(old(t)@), lo, *old(next) as nat),
        pn_below(view_f(*f), lo),
    ensures
        table_ok(table_view(final(t)@), lo, *final(next) as nat),
        extends(table_view(old(t)@), table_view(final(t)@)),
        r is Some ==> resolved(view_f(*f), table_view(final(t)@))
            && r->Some_0 == map_atoms(view_f(*f), numbering(table_view(final(t)@))),
    decreases f,
{
    let ghost vf = view_f(*f);
    let ghost t0 = table_view(t@);
    match f {
        Mltl::True => Some(Mltl::True),
        Mltl::False => Some(Mltl::False),
        Mltl::Prop(n) => {
            proof { assert(atoms_mltl(vf) =~= Set::empty().insert(n@)); assert(atoms_mltl(vf).contains(n@)); }
            let (is_pn, overflow, v) = exec_pnum(n);
            if is_pn {
                if overflow { proof { assert(false); } return None; }
                return Some(Mltl::Prop(v));
            }
            match find(t, n, Ghost(lo), Ghost(*next as nat)) {
                Some(id) => Some(Mltl::Prop(id)),
                None => {
                    if *next == usize::MAX {
                        return None;
                    }
                    let id = *next;
                    let name = copy_vec(n);
                    t.push((name, id));
                    *next = id + 1;
                    proof {
                        let t1 = table_view(t@);
                        assert(t1 == t0.push((n@, id)));
                        assert forall|j: int| 0 <= j < t0.len() implies (#[trigger] t0[j]).0 != n@ by {
                            if t0[j].0 == n@ { lemma_lookup_at(t0, lo, id as nat, j); }
                        }
                        assert(table_ok(t1, lo, *next as nat));
                        lemma_lookup_at(t1, lo, *next as nat, t0.len() as int);
                    }
                    Some(Mltl::Prop(id))
                },
            }
        },
        Mltl::Not(g) => {
            proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g))); }
            match assign(g, t, next, Ghost(lo)) {
                Some(a) => Some(Mltl::Not(Box::new(a))),
                None => None,
            }
        },
        Mltl::Future(x, y, g) => {
            proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g))); }
            match assign(g, t, next, Ghost(lo)) {
                Some(a) => Some(Mltl::Future(*x, *y, Box::new(a))),
                None => None,
            }
        },
        Mltl::Global(x, y, g) => {
            proof { assert(atoms_mltl(vf) == atoms_mltl(view_f(**g))); }
            match assign(g, t, next, Ghost(lo)) {
                Some(a) => Some(Mltl::Global(*x, *y, Box::new(a))),
                None => None,
            }
        },
        Mltl::And(g, h) => {
            let ghost (vg, vh) = (view_f(**g), view_f(**h));
            proof {
                assert(atoms_mltl(vf) == atoms_mltl(vg).union(atoms_mltl(vh)));
                lemma_pn_below_sub(vf, vg, lo);
                lemma_pn_below_sub(vf, vh, lo);
            }
            let ra = assign(g, t, next, Ghost(lo));
            let ghost t1 = table_view(t@);
            match ra {
                None => None,
                Some(a) => {
                    let rb = assign(h, t, next, Ghost(lo));
                    proof { lemma_extends_trans(t0, t1, table_view(t@)); }
                    match rb {
                        None => None,
                        Some(b) => {
                            proof { lemma_assign_binary(vf, vg, vh, a, b, t1, table_view(t@), lo, *next as nat); }
                            Some(Mltl::And(Box::new(a), Box::new(b)))
                        },
                    }
                },
            }
        },
        Mltl::Or(g, h) => {
            let ghost (vg, vh) = (view_f(**g), view_f(**h));
            proof {
                assert(atoms_mltl(vf) == atoms_mltl(vg).union(atoms_mltl(vh)));
                lemma_pn_below_sub(vf, vg, lo);
                lemma_pn_below_sub(vf, vh, lo);
            }
            let ra = assign(g, t, next, Ghost(lo));
            let ghost t1 = table_view(t@);
            match ra {
                None => None,
                Some(a) => {
                    let rb = assign(h, t, next, Ghost(lo));
                    proof { lemma_extends_trans(t0, t1, table_view(t@)); }
                    match rb {
                        None => None,
                        Some(b) => {
                            proof { lemma_assign_binary(vf, vg, vh, a, b, t1, table_view(t@), lo, *next as nat); }
                            Some(Mltl::Or(Box::new(a), Box::new(b)))
                        },
                    }
                },
            }
        },
        Mltl::Until(g, x, y, h) => {
            let ghost (vg, vh) = (view_f(**g), view_f(**h));
            proof {
                assert(atoms_mltl(vf) == atoms_mltl(vg).union(atoms_mltl(vh)));
                lemma_pn_below_sub(vf, vg, lo);
                lemma_pn_below_sub(vf, vh, lo);
            }
            let ra = assign(g, t, next, Ghost(lo));
            let ghost t1 = table_view(t@);
            match ra {
                None => None,
                Some(a) => {
                    let rb = assign(h, t, next, Ghost(lo));
                    proof { lemma_extends_trans(t0, t1, table_view(t@)); }
                    match rb {
                        None => None,
                        Some(b) => {
                            proof { lemma_assign_binary(vf, vg, vh, a, b, t1, table_view(t@), lo, *next as nat); }
                            Some(Mltl::Until(Box::new(a), *x, *y, Box::new(b)))
                        },
                    }
                },
            }
        },
        Mltl::Release(g, x, y, h) => {
            let ghost (vg, vh) = (view_f(**g), view_f(**h));
            proof {
                assert(atoms_mltl(vf) == atoms_mltl(vg).union(atoms_mltl(vh)));
                lemma_pn_below_sub(vf, vg, lo);
                lemma_pn_below_sub(vf, vh, lo);
            }
            let ra = assign(g, t, next, Ghost(lo));
            let ghost t1 = table_view(t@);
            match ra {
                None => None,
                Some(a) => {
                    let rb = assign(h, t, next, Ghost(lo));
                    proof { lemma_extends_trans(t0, t1, table_view(t@)); }
                    match rb {
                        None => None,
                        Some(b) => {
                            proof { lemma_assign_binary(vf, vg, vh, a, b, t1, table_view(t@), lo, *next as nat); }
                            Some(Mltl::Release(Box::new(a), *x, *y, Box::new(b)))
                        },
                    }
                },
            }
        },
    }
}

proof fn lemma_pn_below_sub(f: SpecFormula, g: SpecFormula, lo: nat)
    requires
        pn_below(f, lo),
        atoms_mltl(g).subset_of(atoms_mltl(f)),
    ensures
        pn_below(g, lo),
{
    assert forall|n: Seq<u8>| #[trigger] atoms_mltl(g).contains(n) && pnum(n) is Some implies (pnum(n)->Some_0) < lo by {
        assert(atoms_mltl(f).contains(n));
    }
}

proof fn lemma_extends_trans(t0: SpecTable, t1: SpecTable, t2: SpecTable)
    requires
        extends(t0, t1),
        extends(t1, t2),
    ensures
        extends(t0, t2),
{
    assert forall|j: int| 0 <= j < t0.len() implies #[trigger] t2[j] == t0[j] by {
        assert(t2[j] == t1[j]);
    }
}

/// After numbering `g` (giving `a` with table `t1`) and then `h` (giving `b`
/// with table `t2`): both results are valid for the final table `t2`.
proof fn lemma_assign_binary(f: SpecFormula, g: SpecFormula, h: SpecFormula, a: Mltl<usize>, b: Mltl<usize>,
    t1: SpecTable, t2: SpecTable, lo: nat, next: nat)
    requires
        atoms_mltl(f) == atoms_mltl(g).union(atoms_mltl(h)),
        resolved(g, t1),
        a == map_atoms(g, numbering(t1)),
        resolved(h, t2),
        b == map_atoms(h, numbering(t2)),
        extends(t1, t2),
        table_ok(t2, lo, next),
    ensures
        resolved(f, t2),
        a == map_atoms(g, numbering(t2)),
{
    lemma_numbers_stable(g, t1, t2, lo, next);
    assert forall|n: Seq<u8>| #[trigger] atoms_mltl(f).contains(n) && pnum(n) is None implies lookup(t2, n) is Some by {
        if atoms_mltl(g).contains(n) {} else { assert(atoms_mltl(h).contains(n)); }
    }
}


/// Every `pN` atom of `f` gets number N.
pub open spec fn pn_kept(f: SpecFormula, t: SpecTable) -> bool {
    forall|n: Seq<u8>| #[trigger] atoms_mltl(f).contains(n) && pnum(n) is Some
        ==> number_of(t, n) as nat == pnum(n)->Some_0
}

proof fn lemma_injective(f: SpecFormula, t: SpecTable, lo: nat, next: nat)
    requires
        table_ok(t, lo, next),
        next <= usize::MAX,
        pn_below(f, lo),
        resolved(f, t),
    ensures
        number_injective(f, t),
        pn_kept(f, t),
{
    assert forall|n1: Seq<u8>, n2: Seq<u8>| atoms_mltl(f).contains(n1) && atoms_mltl(f).contains(n2)
        && #[trigger] number_of(t, n1) == #[trigger] number_of(t, n2) implies n1 == n2 by {
        match (pnum(n1), pnum(n2)) {
            (Some(v1), Some(v2)) => { lemma_pnum_injective(n1, n2); },
            (Some(v1), None) => {
                let j2 = entry_index(t, n2);
                assert(t[j2].1 >= lo);
            },
            (None, Some(v2)) => {
                let j1 = entry_index(t, n1);
                assert(t[j1].1 >= lo);
            },
            (None, None) => {
                let (j1, j2) = (entry_index(t, n1), entry_index(t, n2));
                if j1 != j2 { assert(t[j1].1 != t[j2].1); }
            },
        }
    }
}

/// Number the atoms of `f` (GRAMMAR.md §5). Returns the numbered formula
/// and the table of non-`pN` names. Guaranteed: the result is `f` with each
/// atom replaced by its number, `pN` atoms get N, and different atoms get
/// different numbers. `None` if some `pN` has N ≥ usize::MAX, or if the
/// numbers run out.
pub fn number(f: &ExecFormula) -> (r: Option<(Mltl<usize>, Vec<(Vec<u8>, usize)>)>)
    ensures
        r is Some ==> {
            let (g, t) = r->Some_0;
            &&& g == map_atoms(view_f(*f), numbering(table_view(t@)))
            &&& number_injective(view_f(*f), table_view(t@))
            &&& pn_kept(view_f(*f), table_view(t@))
        },
        pn_too_large(view_f(*f)) ==> r is None,
{
    let lo = match pn_bound(f) {
        Ok(m) => m,
        Err(()) => {
            proof {
                let n = choose|n: Seq<u8>| #[trigger] atoms_mltl(view_f(*f)).contains(n) && pnum(n) is Some
                    && (pnum(n)->Some_0) >= usize::MAX;
            }
            return None;
        },
    };
    proof {
        if pn_too_large(view_f(*f)) {
            let n = choose|n: Seq<u8>| #[trigger] atoms_mltl(view_f(*f)).contains(n) && pnum(n) is Some
                && (pnum(n)->Some_0) >= usize::MAX;
            assert((pnum(n)->Some_0) < lo as nat);
        }
    }
    let mut t: Vec<(Vec<u8>, usize)> = Vec::new();
    let mut next = lo;
    proof { assert(table_view(t@) =~= Seq::<(Seq<u8>, usize)>::empty()); }
    let g = assign(f, &mut t, &mut next, Ghost(lo as nat));
    match g {
        Some(g) => {
            proof { lemma_injective(view_f(*f), table_view(t@), lo as nat, next as nat); }
            Some((g, t))
        },
        None => None,
    }
}

} // verus!
