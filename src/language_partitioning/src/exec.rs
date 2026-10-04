//! Executable language partitioning (`usize` atoms, D19).
//!
//! Extended formulas are parse trees with a `Vec<usize>` at every node
//! (`MltlExtExec`); `ext_view` reads one as the spec's `MltlExt<usize>`.
//! Each function is proved equal to its spec (`<name>_spec`, D20); `LP_mltl`
//! also states the union and disjointness guarantees.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use mltl_core::parse_tree::*;
use crate::ext::*;
use crate::composition::*;
use crate::algorithm::*;
use crate::lists::*;
use crate::blocks::*;
use crate::structure::*;
use crate::union::*;
use crate::disjoint::*;

verus! {

/// An executable extended formula: compositions as `Vec<usize>`.
pub type MltlExtExec = MltlParseTree<usize, Vec<usize>>;

/// The spec view of an executable extended formula
/// (`map_aux_data T (λv. v@)`).
pub open spec fn ext_view(t: MltlExtExec) -> MltlExt<usize>
    decreases t,
{
    match t {
        MltlParseTree::True(d) => MltlParseTree::True(d@),
        MltlParseTree::False(d) => MltlParseTree::False(d@),
        MltlParseTree::Prop(d, p) => MltlParseTree::Prop(d@, p),
        MltlParseTree::Not(d, x) => MltlParseTree::Not(d@, Box::new(ext_view(*x))),
        MltlParseTree::And(d, x, y) => MltlParseTree::And(d@, Box::new(ext_view(*x)), Box::new(ext_view(*y))),
        MltlParseTree::Or(d, x, y) => MltlParseTree::Or(d@, Box::new(ext_view(*x)), Box::new(ext_view(*y))),
        MltlParseTree::Future(d, a, b, x) => MltlParseTree::Future(d@, a, b, Box::new(ext_view(*x))),
        MltlParseTree::Global(d, a, b, x) => MltlParseTree::Global(d@, a, b, Box::new(ext_view(*x))),
        MltlParseTree::Until(d, x, a, b, y) => MltlParseTree::Until(d@, Box::new(ext_view(*x)), a, b, Box::new(ext_view(*y))),
        MltlParseTree::Release(d, x, a, b, y) => MltlParseTree::Release(d@, Box::new(ext_view(*x)), a, b, Box::new(ext_view(*y))),
    }
}

pub open spec fn exts_view(v: Seq<MltlExtExec>) -> Seq<MltlExt<usize>> {
    v.map_values(|t: MltlExtExec| ext_view(t))
}

/// The formula of an executable extended formula is that of its view.
pub proof fn lemma_to_mltl_view(t: MltlExtExec)
    ensures
        mltl_parse_tree_to_mltl_spec(t) == to_mltl(ext_view(t)),
    decreases t,
{
    match t {
        MltlParseTree::Not(_, x) | MltlParseTree::Future(_, _, _, x) | MltlParseTree::Global(_, _, _, x) =>
            lemma_to_mltl_view(*x),
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) | MltlParseTree::Until(_, x, _, _, y)
        | MltlParseTree::Release(_, x, _, _, y) => {
            lemma_to_mltl_view(*x);
            lemma_to_mltl_view(*y);
        },
        _ => {},
    }
}

proof fn lemma_exts_view_push(v: Seq<MltlExtExec>, t: MltlExtExec)
    ensures
        exts_view(v.push(t)) == exts_view(v).push(ext_view(t)),
{
    assert(exts_view(v.push(t)) =~= exts_view(v).push(ext_view(t)));
}

proof fn lemma_exts_view_append(v: Seq<MltlExtExec>, w: Seq<MltlExtExec>)
    ensures
        exts_view(v + w) == exts_view(v) + exts_view(w),
{
    assert(exts_view(v + w) =~= exts_view(v) + exts_view(w));
}

// ---------------------------------------------------------------------------
// Copies and NNF
// ---------------------------------------------------------------------------

pub fn clone_vec_usize(v: &Vec<usize>) -> (r: Vec<usize>)
    ensures
        r@ == v@,
{
    let mut r: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            r@ == v@.take(i as int),
        decreases v.len() - i,
    {
        r.push(v[i]);
        assert(v@.take(i as int).push(v@[i as int]) =~= v@.take(i + 1));
        i += 1;
    }
    assert(v@.take(v.len() as int) =~= v@);
    r
}

fn single_vec(x: usize) -> (r: Vec<usize>)
    ensures
        r@ == seq![x],
{
    let mut r = Vec::new();
    r.push(x);
    assert(r@ =~= seq![x]);
    r
}

/// Executable deep copy: `ext_view(r) == ext_view(*t)`.
pub fn clone_ext(t: &MltlExtExec) -> (r: MltlExtExec)
    ensures
        ext_view(r) == ext_view(*t),
    decreases t,
{
    match t {
        MltlParseTree::True(d) => MltlParseTree::True(clone_vec_usize(d)),
        MltlParseTree::False(d) => MltlParseTree::False(clone_vec_usize(d)),
        MltlParseTree::Prop(d, p) => MltlParseTree::Prop(clone_vec_usize(d), *p),
        MltlParseTree::Not(d, x) => MltlParseTree::Not(clone_vec_usize(d), Box::new(clone_ext(x))),
        MltlParseTree::And(d, x, y) => MltlParseTree::And(clone_vec_usize(d), Box::new(clone_ext(x)), Box::new(clone_ext(y))),
        MltlParseTree::Or(d, x, y) => MltlParseTree::Or(clone_vec_usize(d), Box::new(clone_ext(x)), Box::new(clone_ext(y))),
        MltlParseTree::Future(d, a, b, x) => MltlParseTree::Future(clone_vec_usize(d), *a, *b, Box::new(clone_ext(x))),
        MltlParseTree::Global(d, a, b, x) => MltlParseTree::Global(clone_vec_usize(d), *a, *b, Box::new(clone_ext(x))),
        MltlParseTree::Until(d, x, a, b, y) =>
            MltlParseTree::Until(clone_vec_usize(d), Box::new(clone_ext(x)), *a, *b, Box::new(clone_ext(y))),
        MltlParseTree::Release(d, x, a, b, y) =>
            MltlParseTree::Release(clone_vec_usize(d), Box::new(clone_ext(x)), *a, *b, Box::new(clone_ext(y))),
    }
}

/// Executable `convert_nnf_ext`.
pub fn convert_nnf_ext(t: &MltlExtExec) -> (r: MltlExtExec)
    ensures
        ext_view(r) == convert_nnf_ext_spec(ext_view(*t)),
    decreases t,
{
    match t {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => clone_ext(t),
        MltlParseTree::Not(dn, g) => convert_nnf_ext_not(dn, g),
        MltlParseTree::And(d, x, y) =>
            MltlParseTree::And(clone_vec_usize(d), Box::new(convert_nnf_ext(x)), Box::new(convert_nnf_ext(y))),
        MltlParseTree::Or(d, x, y) =>
            MltlParseTree::Or(clone_vec_usize(d), Box::new(convert_nnf_ext(x)), Box::new(convert_nnf_ext(y))),
        MltlParseTree::Future(d, a, b, x) => MltlParseTree::Future(clone_vec_usize(d), *a, *b, Box::new(convert_nnf_ext(x))),
        MltlParseTree::Global(d, a, b, x) => MltlParseTree::Global(clone_vec_usize(d), *a, *b, Box::new(convert_nnf_ext(x))),
        MltlParseTree::Until(d, x, a, b, y) =>
            MltlParseTree::Until(clone_vec_usize(d), Box::new(convert_nnf_ext(x)), *a, *b, Box::new(convert_nnf_ext(y))),
        MltlParseTree::Release(d, x, a, b, y) =>
            MltlParseTree::Release(clone_vec_usize(d), Box::new(convert_nnf_ext(x)), *a, *b, Box::new(convert_nnf_ext(y))),
    }
}

/// `convert_nnf_ext (Not_e dn g)` without building `Not_e dn g` first.
fn convert_nnf_ext_not(dn: &Vec<usize>, g: &MltlExtExec) -> (r: MltlExtExec)
    ensures
        ext_view(r) == convert_nnf_ext_spec(MltlParseTree::Not(dn@, Box::new(ext_view(*g)))),
    decreases g,
{
    reveal_with_fuel(ext_view, 3);
    match g {
        MltlParseTree::True(d) => MltlParseTree::False(clone_vec_usize(d)),
        MltlParseTree::False(d) => MltlParseTree::True(clone_vec_usize(d)),
        MltlParseTree::Prop(d, p) => MltlParseTree::Not(clone_vec_usize(dn), Box::new(MltlParseTree::Prop(clone_vec_usize(d), *p))),
        MltlParseTree::Not(_, x) => convert_nnf_ext(x),
        MltlParseTree::And(d, x, y) =>
            MltlParseTree::Or(clone_vec_usize(d), Box::new(convert_nnf_ext_not(dn, x)), Box::new(convert_nnf_ext_not(dn, y))),
        MltlParseTree::Or(d, x, y) =>
            MltlParseTree::And(clone_vec_usize(d), Box::new(convert_nnf_ext_not(dn, x)), Box::new(convert_nnf_ext_not(dn, y))),
        MltlParseTree::Future(d, a, b, x) => MltlParseTree::Global(clone_vec_usize(d), *a, *b, Box::new(convert_nnf_ext_not(dn, x))),
        MltlParseTree::Global(d, a, b, x) => MltlParseTree::Future(clone_vec_usize(d), *a, *b, Box::new(convert_nnf_ext_not(dn, x))),
        MltlParseTree::Until(d, x, a, b, y) =>
            MltlParseTree::Release(clone_vec_usize(d), Box::new(convert_nnf_ext_not(dn, x)), *a, *b, Box::new(convert_nnf_ext_not(dn, y))),
        MltlParseTree::Release(d, x, a, b, y) =>
            MltlParseTree::Until(clone_vec_usize(d), Box::new(convert_nnf_ext_not(dn, x)), *a, *b, Box::new(convert_nnf_ext_not(dn, y))),
    }
}

// ---------------------------------------------------------------------------
// List builders
// ---------------------------------------------------------------------------

/// `pairs (X @ [a]) B = pairs X B @ map (λx. (a, x)) B`
pub proof fn pairs_snoc<T>(xs: Seq<T>, a: T, b: Seq<T>)
    ensures
        pairs(xs.push(a), b) == pairs(xs, b) + b.map_values(|y: T| (a, y)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(xs.push(a).drop_first() =~= Seq::<T>::empty());
        assert(xs.push(a)[0] == a);
        assert(pairs(Seq::<T>::empty(), b) =~= Seq::<(T, T)>::empty());
        assert(pairs(xs, b) =~= Seq::<(T, T)>::empty());
        assert(pairs(xs.push(a), b) =~= pairs(xs, b) + b.map_values(|y: T| (a, y)));
    } else {
        assert(xs.push(a).drop_first() =~= xs.drop_first().push(a));
        pairs_snoc(xs.drop_first(), a, b);
        assert(xs.push(a)[0] == xs[0]);
        assert(pairs(xs.push(a), b) =~= pairs(xs, b) + b.map_values(|y: T| (a, y)));
    }
}

/// `And_mltl_list (X @ [a]) B = And_mltl_list X B @ map (And_mltl_ext a) B`
proof fn And_mltl_list_snoc(xs: Seq<MltlExt<usize>>, a: MltlExt<usize>, b: Seq<MltlExt<usize>>)
    ensures
        And_mltl_list_spec(xs.push(a), b) == And_mltl_list_spec(xs, b) + b.map_values(|y: MltlExt<usize>| and_mltl_ext(a, y)),
{
    pairs_snoc(xs, a, b);
    assert(And_mltl_list_spec(xs.push(a), b) =~= And_mltl_list_spec(xs, b) + b.map_values(|y: MltlExt<usize>| and_mltl_ext(a, y)));
}

/// Executable `And_mltl_list`.
pub fn And_mltl_list(dx: &Vec<MltlExtExec>, dy: &Vec<MltlExtExec>) -> (r: Vec<MltlExtExec>)
    ensures
        exts_view(r@) == And_mltl_list_spec(exts_view(dx@), exts_view(dy@)),
{
    let ghost xa = exts_view(dx@);
    let ghost yb = exts_view(dy@);
    let mut r: Vec<MltlExtExec> = Vec::new();
    let mut i = 0;
    assert(xa.take(0) =~= Seq::<MltlExt<usize>>::empty());
    assert(And_mltl_list_spec(Seq::<MltlExt<usize>>::empty(), yb) =~= Seq::<MltlExt<usize>>::empty());
    assert(exts_view(r@) =~= Seq::<MltlExt<usize>>::empty());
    while i < dx.len()
        invariant
            0 <= i <= dx.len(),
            xa == exts_view(dx@),
            yb == exts_view(dy@),
            exts_view(r@) == And_mltl_list_spec(xa.take(i as int), yb),
        decreases dx.len() - i,
    {
        let ghost row_start = exts_view(r@);
        let mut j = 0;
        assert(yb.take(0).map_values(|y: MltlExt<usize>| and_mltl_ext(xa[i as int], y)) =~= Seq::<MltlExt<usize>>::empty());
        assert(exts_view(r@) =~= row_start + yb.take(0).map_values(|y: MltlExt<usize>| and_mltl_ext(xa[i as int], y)));
        while j < dy.len()
            invariant
                0 <= i < dx.len(),
                0 <= j <= dy.len(),
                xa == exts_view(dx@),
                yb == exts_view(dy@),
                row_start == And_mltl_list_spec(xa.take(i as int), yb),
                exts_view(r@) == row_start + yb.take(j as int).map_values(|y: MltlExt<usize>| and_mltl_ext(xa[i as int], y)),
            decreases dy.len() - j,
        {
            let e = MltlParseTree::And(Vec::new(), Box::new(clone_ext(&dx[i])), Box::new(clone_ext(&dy[j])));
            proof {
                lemma_exts_view_push(r@, e);
                assert(ext_view(e) == and_mltl_ext(xa[i as int], yb[j as int]));
                assert(yb.take(j + 1).map_values(|y: MltlExt<usize>| and_mltl_ext(xa[i as int], y))
                    =~= yb.take(j as int).map_values(|y: MltlExt<usize>| and_mltl_ext(xa[i as int], y)).push(ext_view(e)));
            }
            r.push(e);
            j += 1;
        }
        proof {
            assert(yb.take(dy.len() as int) =~= yb);
            assert(xa.take(i + 1) =~= xa.take(i as int).push(xa[i as int]));
            And_mltl_list_snoc(xa.take(i as int), xa[i as int], yb);
        }
        i += 1;
    }
    assert(xa.take(dx.len() as int) =~= xa);
    r
}

/// Executable `Global_mltl_list`.
pub fn Global_mltl_list(d: &Vec<MltlExtExec>, a: usize, b: usize, l: &Vec<usize>) -> (r: Vec<MltlExtExec>)
    ensures
        exts_view(r@) == Global_mltl_list_spec(exts_view(d@), a, b, l@),
{
    let mut r: Vec<MltlExtExec> = Vec::new();
    let mut i = 0;
    while i < d.len()
        invariant
            0 <= i <= d.len(),
            r.len() == i,
            forall|p: int| 0 <= p < i ==> #[trigger] ext_view(r@[p]) == global_mltl_ext(a, b, l@, ext_view(d@[p])),
        decreases d.len() - i,
    {
        r.push(MltlParseTree::Global(clone_vec_usize(l), a, b, Box::new(clone_ext(&d[i]))));
        i += 1;
    }
    assert(exts_view(r@) =~= Global_mltl_list_spec(exts_view(d@), a, b, l@));
    r
}

/// Executable `Future_mltl_list`.
pub fn Future_mltl_list(d: &Vec<MltlExtExec>, a: usize, b: usize, l: &Vec<usize>) -> (r: Vec<MltlExtExec>)
    ensures
        exts_view(r@) == Future_mltl_list_spec(exts_view(d@), a, b, l@),
{
    let mut r: Vec<MltlExtExec> = Vec::new();
    let mut i = 0;
    while i < d.len()
        invariant
            0 <= i <= d.len(),
            r.len() == i,
            forall|p: int| 0 <= p < i ==> #[trigger] ext_view(r@[p]) == future_mltl_ext(a, b, l@, ext_view(d@[p])),
        decreases d.len() - i,
    {
        r.push(MltlParseTree::Future(clone_vec_usize(l), a, b, Box::new(clone_ext(&d[i]))));
        i += 1;
    }
    assert(exts_view(r@) =~= Future_mltl_list_spec(exts_view(d@), a, b, l@));
    r
}

/// Executable `Until_mltl_list`.
pub fn Until_mltl_list(phi: &MltlExtExec, d: &Vec<MltlExtExec>, a: usize, b: usize, l: &Vec<usize>) -> (r: Vec<MltlExtExec>)
    ensures
        exts_view(r@) == Until_mltl_list_spec(ext_view(*phi), exts_view(d@), a, b, l@),
{
    let mut r: Vec<MltlExtExec> = Vec::new();
    let mut i = 0;
    while i < d.len()
        invariant
            0 <= i <= d.len(),
            r.len() == i,
            forall|p: int| 0 <= p < i ==> #[trigger] ext_view(r@[p]) == until_mltl_ext(ext_view(*phi), a, b, l@, ext_view(d@[p])),
        decreases d.len() - i,
    {
        r.push(MltlParseTree::Until(clone_vec_usize(l), Box::new(clone_ext(phi)), a, b, Box::new(clone_ext(&d[i]))));
        i += 1;
    }
    assert(exts_view(r@) =~= Until_mltl_list_spec(ext_view(*phi), exts_view(d@), a, b, l@));
    r
}

/// Executable `Mighty_Release_mltl_list`.
pub fn Mighty_Release_mltl_list(d: &Vec<MltlExtExec>, psi: &MltlExtExec, a: usize, b: usize, l: &Vec<usize>) -> (r: Vec<MltlExtExec>)
    ensures
        exts_view(r@) == Mighty_Release_mltl_list_spec(exts_view(d@), ext_view(*psi), a, b, l@),
{
    reveal_with_fuel(ext_view, 3);
    let mut r: Vec<MltlExtExec> = Vec::new();
    let mut i = 0;
    while i < d.len()
        invariant
            0 <= i <= d.len(),
            r.len() == i,
            forall|p: int| 0 <= p < i ==> #[trigger] ext_view(r@[p])
                == Mighty_Release_mltl_ext(ext_view(d@[p]), ext_view(*psi), a, b, l@),
        decreases d.len() - i,
    {
        let x1 = clone_ext(&d[i]);
        let x2 = clone_ext(&d[i]);
        let p1 = clone_ext(psi);
        let rel = MltlParseTree::Release(clone_vec_usize(l), Box::new(x1), a, b, Box::new(p1));
        let fut = MltlParseTree::Future(clone_vec_usize(l), a, b, Box::new(x2));
        let nv: Vec<usize> = Vec::new();
        let e = MltlParseTree::And(nv, Box::new(rel), Box::new(fut));
        assert(ext_view(rel) == release_mltl_ext(ext_view(d@[i as int]), a, b, l@, ext_view(*psi)));
        assert(ext_view(fut) == future_mltl_ext(a, b, l@, ext_view(d@[i as int])));
        assert(nv@ =~= Seq::<usize>::empty());
        assert(ext_view(e) == Mighty_Release_mltl_ext(ext_view(d@[i as int]), ext_view(*psi), a, b, l@));
        r.push(e);
        i += 1;
    }
    assert(exts_view(r@) =~= Mighty_Release_mltl_list_spec(exts_view(d@), ext_view(*psi), a, b, l@));
    r
}

/// Executable `Global_mltl_decomp`.
pub fn Global_mltl_decomp(d: &Vec<MltlExtExec>, a: usize, len: usize, l: &Vec<usize>) -> (r: Vec<MltlExtExec>)
    requires
        a + len <= usize::MAX,
    ensures
        exts_view(r@) == Global_mltl_decomp_spec(exts_view(d@), a, len as nat, l@),
{
    let one = single_vec(1);
    let mut acc = Global_mltl_list(d, a, a, &one);
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            a + len <= usize::MAX,
            one@ == seq![1usize],
            exts_view(acc@) == Global_mltl_decomp_spec(exts_view(d@), a, i as nat, l@),
        decreases len - i,
    {
        i += 1;
        let g = Global_mltl_list(d, a + i, a + i, &one);
        acc = And_mltl_list(&acc, &g);
    }
    acc
}

// ---------------------------------------------------------------------------
// LP_mltl_aux, LP_mltl
// ---------------------------------------------------------------------------

/// `concat (Seq::new (m+1) f) = concat (Seq::new m f) @ f m`
proof fn concat_new_snoc(f: spec_fn(int) -> Seq<MltlExt<usize>>, m: nat)
    ensures
        concat(Seq::new(m + 1, f)) == concat(Seq::new(m, f)) + f(m as int),
{
    assert(Seq::new(m + 1, f).drop_last() =~= Seq::new(m, f));
}

/// The executable `F` case: block 0, then pieces `1 … length L - 1`.
fn lp_future_exec(l: &Vec<usize>, a: usize, b: usize, x: &MltlExtExec, dx: &Vec<MltlExtExec>) -> (r: Vec<MltlExtExec>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l@),
    ensures
        exts_view(r@) == lp_future_list(l@, a, b, ext_view(*x), exts_view(dx@)),
{
    reveal_with_fuel(ext_view, 3);
    let ghost s = interval_times(a as nat, l@);
    let ghost xv = ext_view(*x);
    let ghost dv = exts_view(dx@);
    proof { lemma_blocks_ok(a, b, l@); block_bounds(a, b, l@, s, 0); }
    let n = l.len();
    let hi0 = a + (l[0] - 1);
    let w0 = single_vec(l[0]);
    let mut r = Future_mltl_list(dx, a, hi0, &w0);
    let ghost head = exts_view(r@);
    let mut prev_end = hi0;
    let mut i: usize = 1;
    assert(Seq::new(0, |j: int| LP_future_piece(dv, xv, s, j + 1)) =~= Seq::<Seq<MltlExt<usize>>>::empty());
    assert(exts_view(r@) =~= head + concat(Seq::new(0, |j: int| LP_future_piece(dv, xv, s, j + 1))));
    while i < n
        invariant
            1 <= i <= n,
            n == l.len(),
            s == interval_times(a as nat, l@),
            blocks_ok(a, b, l@, s),
            xv == ext_view(*x),
            dv == exts_view(dx@),
            prev_end == s[i as int] - 1,
            exts_view(r@) == head + concat(Seq::new((i - 1) as nat, |j: int| LP_future_piece(dv, xv, s, j + 1))),
        decreases n - i,
    {
        proof { block_bounds(a, b, l@, s, i as int); }
        let start = prev_end + 1;
        let end = start + (l[i] - 1);
        let cx = clone_ext(x);
        let nv: Vec<usize> = Vec::new();
        let body = MltlParseTree::Not(nv, Box::new(cx));
        let wg = single_vec(start - a);
        assert(nv@ =~= Seq::<usize>::empty());
        assert(ext_view(body) == not_mltl_ext(xv));
        let g = MltlParseTree::Global(wg, a, start - 1, Box::new(body));
        let mut gv: Vec<MltlExtExec> = Vec::new();
        gv.push(g);
        let f = Future_mltl_list(dx, start, end, &single_vec(l[i]));
        let mut piece = And_mltl_list(&gv, &f);
        proof {
            assert(exts_view(gv@) =~= seq![ext_view(g)]);
            assert(ext_view(g) == global_mltl_ext(s[0] as usize, (s[i as int] - 1) as usize,
                seq![(s[i as int] - s[0]) as usize], not_mltl_ext(xv)));
            assert(exts_view(piece@) == LP_future_piece(dv, xv, s, i as int));
            lemma_exts_view_append(r@, piece@);
            concat_new_snoc(|j: int| LP_future_piece(dv, xv, s, j + 1), (i - 1) as nat);
        }
        r.append(&mut piece);
        prev_end = end;
        i += 1;
    }
    r
}

/// The executable `U` case.
fn lp_until_exec(l: &Vec<usize>, x: &MltlExtExec, a: usize, b: usize, y: &MltlExtExec, dy: &Vec<MltlExtExec>) -> (r: Vec<MltlExtExec>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l@),
    ensures
        exts_view(r@) == lp_until_list(l@, ext_view(*x), a, b, ext_view(*y), exts_view(dy@)),
{
    reveal_with_fuel(ext_view, 3);
    let ghost s = interval_times(a as nat, l@);
    let ghost xv = ext_view(*x);
    let ghost yv = ext_view(*y);
    let ghost dv = exts_view(dy@);
    proof { lemma_blocks_ok(a, b, l@); block_bounds(a, b, l@, s, 0); }
    let n = l.len();
    let hi0 = a + (l[0] - 1);
    let w0 = single_vec(l[0]);
    let mut r = Until_mltl_list(x, dy, a, hi0, &w0);
    let ghost head = exts_view(r@);
    let mut prev_end = hi0;
    let mut i: usize = 1;
    assert(Seq::new(0, |j: int| LP_until_piece(xv, dv, yv, s, j + 1)) =~= Seq::<Seq<MltlExt<usize>>>::empty());
    assert(exts_view(r@) =~= head + concat(Seq::new(0, |j: int| LP_until_piece(xv, dv, yv, s, j + 1))));
    while i < n
        invariant
            1 <= i <= n,
            n == l.len(),
            s == interval_times(a as nat, l@),
            blocks_ok(a, b, l@, s),
            xv == ext_view(*x),
            yv == ext_view(*y),
            dv == exts_view(dy@),
            prev_end == s[i as int] - 1,
            exts_view(r@) == head + concat(Seq::new((i - 1) as nat, |j: int| LP_until_piece(xv, dv, yv, s, j + 1))),
        decreases n - i,
    {
        proof { block_bounds(a, b, l@, s, i as int); }
        let start = prev_end + 1;
        let end = start + (l[i] - 1);
        let cx = clone_ext(x);
        let cy = clone_ext(y);
        let nv1: Vec<usize> = Vec::new();
        let nv2: Vec<usize> = Vec::new();
        let ny = MltlParseTree::Not(nv1, Box::new(cy));
        let body = MltlParseTree::And(nv2, Box::new(cx), Box::new(ny));
        let wg = single_vec(start - a);
        assert(nv1@ =~= Seq::<usize>::empty() && nv2@ =~= Seq::<usize>::empty());
        assert(ext_view(ny) == not_mltl_ext(yv));
        assert(ext_view(body) == and_mltl_ext(xv, not_mltl_ext(yv)));
        let g = MltlParseTree::Global(wg, a, start - 1, Box::new(body));
        let mut gv: Vec<MltlExtExec> = Vec::new();
        gv.push(g);
        let f = Until_mltl_list(x, dy, start, end, &single_vec(l[i]));
        let mut piece = And_mltl_list(&gv, &f);
        proof {
            assert(exts_view(gv@) =~= seq![ext_view(g)]);
            assert(ext_view(g) == global_mltl_ext(s[0] as usize, (s[i as int] - 1) as usize,
                seq![(s[i as int] - s[0]) as usize], and_mltl_ext(xv, not_mltl_ext(yv))));
            assert(exts_view(piece@) == LP_until_piece(xv, dv, yv, s, i as int));
            lemma_exts_view_append(r@, piece@);
            concat_new_snoc(|j: int| LP_until_piece(xv, dv, yv, s, j + 1), (i - 1) as nat);
        }
        r.append(&mut piece);
        prev_end = end;
        i += 1;
    }
    r
}

/// The executable `R` case.
fn lp_release_exec(l: &Vec<usize>, x: &MltlExtExec, a: usize, b: usize, y: &MltlExtExec, dx: &Vec<MltlExtExec>) -> (r: Vec<MltlExtExec>)
    requires
        a <= b,
        is_composition(nat_sub(b as nat, a as nat) + 1, l@),
    ensures
        exts_view(r@) == lp_release_list(l@, ext_view(*x), a, b, ext_view(*y), exts_view(dx@)),
{
    reveal_with_fuel(ext_view, 3);
    let ghost s = interval_times(a as nat, l@);
    let ghost xv = ext_view(*x);
    let ghost yv = ext_view(*y);
    let ghost dv = exts_view(dx@);
    proof { lemma_blocks_ok(a, b, l@); block_bounds(a, b, l@, s, 0); }
    let n = l.len();
    let e0 = MltlParseTree::Global(clone_vec_usize(l), a, b, Box::new(MltlParseTree::And(Vec::new(),
        Box::new(MltlParseTree::Not(Vec::new(), Box::new(clone_ext(x)))), Box::new(clone_ext(y)))));
    let mut r: Vec<MltlExtExec> = Vec::new();
    r.push(e0);
    let hi0 = a + (l[0] - 1);
    let w0 = single_vec(l[0]);
    let mut h = Mighty_Release_mltl_list(dx, y, a, hi0, &w0);
    proof {
        assert(exts_view(r@) =~= seq![global_mltl_ext(a, b, l@, and_mltl_ext(not_mltl_ext(xv), yv))]);
        lemma_exts_view_append(r@, h@);
    }
    r.append(&mut h);
    let ghost head = exts_view(r@);
    let mut prev_end = hi0;
    let mut i: usize = 1;
    assert(Seq::new(0, |j: int| LP_release_piece(dv, xv, yv, s, j + 1)) =~= Seq::<Seq<MltlExt<usize>>>::empty());
    assert(exts_view(r@) =~= head + concat(Seq::new(0, |j: int| LP_release_piece(dv, xv, yv, s, j + 1))));
    while i < n
        invariant
            1 <= i <= n,
            n == l.len(),
            s == interval_times(a as nat, l@),
            blocks_ok(a, b, l@, s),
            xv == ext_view(*x),
            yv == ext_view(*y),
            dv == exts_view(dx@),
            prev_end == s[i as int] - 1,
            exts_view(r@) == head + concat(Seq::new((i - 1) as nat, |j: int| LP_release_piece(dv, xv, yv, s, j + 1))),
        decreases n - i,
    {
        proof { block_bounds(a, b, l@, s, i as int); }
        let start = prev_end + 1;
        let end = start + (l[i] - 1);
        let cx = clone_ext(x);
        let cy = clone_ext(y);
        let nv1: Vec<usize> = Vec::new();
        let nv2: Vec<usize> = Vec::new();
        let nx = MltlParseTree::Not(nv1, Box::new(cx));
        let body = MltlParseTree::And(nv2, Box::new(nx), Box::new(cy));
        let wg = single_vec(start - a);
        assert(nv1@ =~= Seq::<usize>::empty() && nv2@ =~= Seq::<usize>::empty());
        assert(ext_view(nx) == not_mltl_ext(xv));
        assert(ext_view(body) == and_mltl_ext(not_mltl_ext(xv), yv));
        let g = MltlParseTree::Global(wg, a, start - 1, Box::new(body));
        let mut gv: Vec<MltlExtExec> = Vec::new();
        gv.push(g);
        let f = Mighty_Release_mltl_list(dx, y, start, end, &single_vec(l[i]));
        let mut piece = And_mltl_list(&gv, &f);
        proof {
            assert(exts_view(gv@) =~= seq![ext_view(g)]);
            assert(ext_view(g) == global_mltl_ext(s[0] as usize, (s[i as int] - 1) as usize,
                seq![(s[i as int] - s[0]) as usize], and_mltl_ext(not_mltl_ext(xv), yv)));
            assert(exts_view(piece@) == LP_release_piece(dv, xv, yv, s, i as int));
            lemma_exts_view_append(r@, piece@);
            concat_new_snoc(|j: int| LP_release_piece(dv, xv, yv, s, j + 1), (i - 1) as nat);
        }
        r.append(&mut piece);
        prev_end = end;
        i += 1;
    }
    r
}

/// Preconditions are kept by `convert_nnf_ext` on a child.
proof fn lemma_child_ok(x: MltlExtExec)
    requires
        intervals_welldef(to_mltl(ext_view(x))),
        is_composition_MLTL(ext_view(x)),
    ensures
        intervals_welldef(to_mltl(convert_nnf_ext_spec(ext_view(x)))),
        is_composition_MLTL(convert_nnf_ext_spec(ext_view(x))),
{
    convert_nnf_ext_welldef(ext_view(x));
    is_composition_convert_nnf_ext(ext_view(x));
}

/// Executable `LP_mltl_aux`.
pub fn LP_mltl_aux(phi: &MltlExtExec, k: usize) -> (r: Vec<MltlExtExec>)
    requires
        intervals_welldef(to_mltl(ext_view(*phi))),
        is_composition_MLTL(ext_view(*phi)),
    ensures
        exts_view(r@) == LP_mltl_aux_spec(ext_view(*phi), k as nat),
    decreases k,
{
    reveal_with_fuel(ext_view, 3);
    let ghost pv = ext_view(*phi);
    if k == 0 {
        let mut r = Vec::new();
        r.push(clone_ext(phi));
        assert(exts_view(r@) =~= seq![pv]);
        return r;
    }
    let k1 = k - 1;
    let single = |t: &MltlExtExec| -> (r: Vec<MltlExtExec>)
        ensures exts_view(r@) == seq![ext_view(*t)]
    {
        let mut r = Vec::new();
        r.push(clone_ext(t));
        assert(exts_view(r@) =~= seq![ext_view(*t)]);
        r
    };
    match phi {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => single(phi),
        MltlParseTree::Not(_, x) => match &**x {
            MltlParseTree::Prop(_, _) => single(phi),
            _ => {
                let r = Vec::new();
                assert(exts_view(r@) =~= Seq::<MltlExt<usize>>::empty());
                r
            },
        },
        MltlParseTree::And(_, x, y) => {
            proof { lemma_child_ok(**x); lemma_child_ok(**y); }
            let dx = LP_mltl_aux(&convert_nnf_ext(x), k1);
            let dy = LP_mltl_aux(&convert_nnf_ext(y), k1);
            And_mltl_list(&dx, &dy)
        },
        MltlParseTree::Or(_, x, y) => {
            proof { lemma_child_ok(**x); lemma_child_ok(**y); }
            let dx = LP_mltl_aux(&convert_nnf_ext(x), k1);
            let dy = LP_mltl_aux(&convert_nnf_ext(y), k1);
            let nx = single(&MltlParseTree::Not(Vec::new(), Box::new(clone_ext(x))));
            let ny = single(&MltlParseTree::Not(Vec::new(), Box::new(clone_ext(y))));
            let mut r = And_mltl_list(&dx, &dy);
            let mut r2 = And_mltl_list(&nx, &dy);
            let mut r3 = And_mltl_list(&dx, &ny);
            proof {
                lemma_exts_view_append(r@, r2@);
                lemma_exts_view_append(r@ + r2@, r3@);
            }
            r.append(&mut r2);
            r.append(&mut r3);
            r
        },
        MltlParseTree::Global(l, a, b, x) => {
            proof { lemma_child_ok(**x); }
            let dx = LP_mltl_aux(&convert_nnf_ext(x), k1);
            if dx.len() <= 1 {
                single(phi)
            } else {
                Global_mltl_decomp(&dx, *a, *b - *a, l)
            }
        },
        MltlParseTree::Future(l, a, b, x) => {
            proof { lemma_child_ok(**x); }
            let dx = LP_mltl_aux(&convert_nnf_ext(x), k1);
            let r = lp_future_exec(l, *a, *b, x, &dx);
            assert(LP_mltl_aux_spec(pv, k as nat) == lp_future_list(l@, *a, *b, ext_view(**x), exts_view(dx@)));
            r
        },
        MltlParseTree::Until(l, x, a, b, y) => {
            proof { lemma_child_ok(**y); }
            let dy = LP_mltl_aux(&convert_nnf_ext(y), k1);
            let r = lp_until_exec(l, x, *a, *b, y, &dy);
            assert(LP_mltl_aux_spec(pv, k as nat) == lp_until_list(l@, ext_view(**x), *a, *b, ext_view(**y), exts_view(dy@)));
            r
        },
        MltlParseTree::Release(l, x, a, b, y) => {
            proof { lemma_child_ok(**x); }
            let dx = LP_mltl_aux(&convert_nnf_ext(x), k1);
            let r = lp_release_exec(l, x, *a, *b, y, &dx);
            assert(LP_mltl_aux_spec(pv, k as nat) == lp_release_list(l@, ext_view(**x), *a, *b, ext_view(**y), exts_view(dx@)));
            r
        },
    }
}

/// Executable `LP_mltl`: partition `φ` into MLTL formulas.
///
/// Requires well-defined intervals and, on every `F`/`G`/`U`/`R`, a
/// composition of its interval (`check_lp_input` decides both).
pub fn LP_mltl(phi: &MltlExtExec, k: usize) -> (r: Vec<Mltl<usize>>)
    requires
        intervals_welldef(to_mltl(ext_view(*phi))),
        is_composition_MLTL(ext_view(*phi)),
    ensures
        // Computes exactly Isabelle's `LP_mltl φ k` ...
        r@ == LP_mltl_spec(ext_view(*phi), k as nat),
        // ... whose formulas together hold exactly when `φ` does, on every
        // trace of length at least `wpd` (`LP_mltl_language_union_explicit`) ...
        forall|pi: Seq<Set<usize>>| pi.len() >= wpd_mltl(to_mltl(ext_view(*phi))) ==>
            (semantics_mltl(pi, to_mltl(ext_view(*phi)))
                <==> exists|psi: Mltl<usize>| r@.contains(psi) && semantics_mltl(pi, psi)),
        // ... and, for all-ones compositions or `k = 1`, no two different
        // formulas hold on the same such trace (`LP_mltl_language_disjoint`,
        // `LP_mltl_language_disjoint_k1`).
        is_composition_MLTL_allones(ext_view(*phi)) || k == 1 ==>
            forall|pi: Seq<Set<usize>>, psi1: Mltl<usize>, psi2: Mltl<usize>|
                pi.len() >= wpd_mltl(to_mltl(ext_view(*phi))) && r@.contains(psi1) && r@.contains(psi2)
                    && psi1 != psi2 && semantics_mltl(pi, psi1) ==> !semantics_mltl(pi, psi2),
{
    let ghost pv = ext_view(*phi);
    proof { lemma_child_ok(*phi); }
    let d = LP_mltl_aux(&convert_nnf_ext(phi), k);
    let ghost dv = exts_view(d@);
    let mut r: Vec<Mltl<usize>> = Vec::new();
    let mut i = 0;
    while i < d.len()
        invariant
            0 <= i <= d.len(),
            dv == exts_view(d@),
            dv == LP_mltl_aux_spec(convert_nnf_ext_spec(pv), k as nat),
            r.len() == i,
            forall|p: int| 0 <= p < i ==> #[trigger] r@[p] == to_mltl(convert_nnf_ext_spec(dv[p])),
        decreases d.len() - i,
    {
        let n = convert_nnf_ext(&d[i]);
        let m = mltl_parse_tree_to_mltl(&n);
        proof { lemma_to_mltl_view(n); }
        r.push(m);
        i += 1;
    }
    proof {
        assert(r@ =~= LP_mltl_spec(pv, k as nat));
        assert forall|pi: Seq<Set<usize>>| pi.len() >= wpd_mltl(to_mltl(pv)) implies
            (semantics_mltl(pi, to_mltl(pv)) <==> exists|psi: Mltl<usize>| r@.contains(psi) && semantics_mltl(pi, psi)) by {
            LP_mltl_language_union_explicit(pv, k as nat, pi);
        }
        if is_composition_MLTL_allones(pv) || k == 1 {
            assert forall|pi: Seq<Set<usize>>, psi1: Mltl<usize>, psi2: Mltl<usize>|
                pi.len() >= wpd_mltl(to_mltl(pv)) && r@.contains(psi1) && r@.contains(psi2)
                    && psi1 != psi2 && semantics_mltl(pi, psi1) implies !semantics_mltl(pi, psi2) by {
                let rr = pi.len();
                if is_composition_MLTL_allones(pv) {
                    LP_mltl_language_disjoint(pv, psi1, psi2, k as nat, rr);
                } else {
                    LP_mltl_language_disjoint_k1(pv, psi1, psi2, rr);
                }
                if semantics_mltl(pi, psi2) {
                    assert(language_mltl_r(psi1, rr).contains(pi));
                    assert(language_mltl_r(psi2, rr).contains(pi));
                    assert(language_mltl_r(psi1, rr).intersect(language_mltl_r(psi2, rr)).contains(pi));
                }
            }
        }
    }
    r
}

// ---------------------------------------------------------------------------
// Input checks and builders (not in Isabelle)
// ---------------------------------------------------------------------------

/// Decides `is_composition (b - a + 1) L` for `a ≤ b`.
pub fn check_composition(a: usize, b: usize, l: &Vec<usize>) -> (r: bool)
    requires
        a <= b,
    ensures
        r == is_composition(nat_sub(b as nat, a as nat) + 1, l@),
{
    let mut rem: u128 = (b - a) as u128 + 1;
    let mut i = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            a <= b,
            rem as nat + sum_list(l@.take(i as int)) == nat_sub(b as nat, a as nat) + 1,
            forall|j: int| 0 <= j < i ==> #[trigger] l@[j] > 0,
        decreases l.len() - i,
    {
        proof {
            assert(l@.take(i + 1).drop_last() =~= l@.take(i as int));
        }
        if l[i] == 0 || l[i] as u128 > rem {
            proof {
                if l@[i as int] as u128 > rem {
                    // the remaining entries only add to the sum
                    lemma_sum_list_prefix_le(l@, (i + 1) as nat);
                }
            }
            return false;
        }
        rem = rem - l[i] as u128;
        i += 1;
    }
    proof {
        assert(l@.take(l.len() as int) =~= l@);
    }
    rem == 0
}

/// `sum_list (take i L) ≤ sum_list L`
proof fn lemma_sum_list_prefix_le(l: Seq<usize>, i: nat)
    requires
        i <= l.len(),
    ensures
        sum_list(l.take(i as int)) <= sum_list(l),
    decreases l.len() - i,
{
    if i < l.len() {
        lemma_sum_list_prefix_le(l, i + 1);
        assert(l.take((i + 1) as int).drop_last() =~= l.take(i as int));
    } else {
        assert(l.take(i as int) =~= l);
    }
}

/// Decides the precondition of `LP_mltl`: well-defined intervals and a
/// composition of every temporal interval.
pub fn check_lp_input(phi: &MltlExtExec) -> (r: bool)
    ensures
        r == (intervals_welldef(to_mltl(ext_view(*phi))) && is_composition_MLTL(ext_view(*phi))),
    decreases phi,
{
    match phi {
        MltlParseTree::True(_) | MltlParseTree::False(_) | MltlParseTree::Prop(_, _) => true,
        MltlParseTree::Not(_, x) => check_lp_input(x),
        MltlParseTree::And(_, x, y) | MltlParseTree::Or(_, x, y) => check_lp_input(x) && check_lp_input(y),
        MltlParseTree::Future(l, a, b, x) | MltlParseTree::Global(l, a, b, x) =>
            *a <= *b && check_composition(*a, *b, l) && check_lp_input(x),
        MltlParseTree::Until(l, x, a, b, y) | MltlParseTree::Release(l, x, a, b, y) =>
            *a <= *b && check_composition(*a, *b, l) && check_lp_input(x) && check_lp_input(y),
    }
}

} // verus!
