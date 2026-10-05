//! Building `LP_mltl`'s input from a plain formula: attach a composition
//! (block widths) to every `F`, `G`, `U`, `R` interval. Not in Isabelle.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use mltl_core::parse_tree::*;
use crate::ext::*;
use crate::composition::*;
use crate::exec::*;

verus! {

/// Blocks of width `w` covering `[a, b]` from the left (the last one may be
/// shorter). `None` only for the interval `[0, usize::MAX]`, whose length
/// doesn't fit in a `usize`.
fn blocks(a: usize, b: usize, w: usize) -> (r: Option<Vec<usize>>)
    requires
        a <= b,
        w > 0,
    ensures
        r is Some ==> is_composition(nat_sub(b as nat, a as nat) + 1, r->Some_0@),
        r is Some && w == 1 ==> is_composition_allones(nat_sub(b as nat, a as nat) + 1, r->Some_0@),
        r is None ==> b - a == usize::MAX,
{
    if b - a == usize::MAX {
        return None;
    }
    let n = b - a + 1;
    let mut l: Vec<usize> = Vec::new();
    let mut rem = n;
    while rem > 0
        invariant
            w > 0,
            rem as nat + sum_list(l@) == n as nat,
            forall|i: int| 0 <= i < l.len() ==> #[trigger] l@[i] > 0,
            w == 1 ==> forall|i: int| 0 <= i < l.len() ==> #[trigger] l@[i] == 1,
        decreases rem,
    {
        let x = if rem < w { rem } else { w };
        let ghost before = l@;
        l.push(x);
        proof { assert(l@.drop_last() =~= before); }
        rem = rem - x;
    }
    Some(l)
}

/// `f` with every interval split into blocks of width `w` (the last block
/// of an interval may be shorter). `w = 1` gives all-ones compositions,
/// for which `LP_mltl` also guarantees disjointness.
///
/// `Some(t)`: `t` is `f` with compositions, and a valid input of `LP_mltl`.
/// `None`: some interval has `a > b`, or is `[0, usize::MAX]`.
pub fn with_width(f: &Mltl<usize>, w: usize) -> (r: Option<MltlExtExec>)
    requires
        w > 0,
    ensures
        r is Some ==> {
            let t = ext_view(r->Some_0);
            &&& to_mltl(t) == *f
            &&& intervals_welldef(*f)
            &&& is_composition_MLTL(t)
            &&& w == 1 ==> is_composition_MLTL_allones(t)
        },
    decreases f,
{
    match f {
        Mltl::True => Some(MltlParseTree::True(Vec::new())),
        Mltl::False => Some(MltlParseTree::False(Vec::new())),
        Mltl::Prop(p) => Some(MltlParseTree::Prop(Vec::new(), *p)),
        Mltl::Not(x) => {
            let x = with_width(x, w)?;
            Some(MltlParseTree::Not(Vec::new(), Box::new(x)))
        },
        Mltl::And(x, y) => {
            let x = with_width(x, w)?;
            let y = with_width(y, w)?;
            Some(MltlParseTree::And(Vec::new(), Box::new(x), Box::new(y)))
        },
        Mltl::Or(x, y) => {
            let x = with_width(x, w)?;
            let y = with_width(y, w)?;
            Some(MltlParseTree::Or(Vec::new(), Box::new(x), Box::new(y)))
        },
        Mltl::Future(a, b, x) => {
            if *a > *b { return None; }
            let l = blocks(*a, *b, w)?;
            let x = with_width(x, w)?;
            Some(MltlParseTree::Future(l, *a, *b, Box::new(x)))
        },
        Mltl::Global(a, b, x) => {
            if *a > *b { return None; }
            let l = blocks(*a, *b, w)?;
            let x = with_width(x, w)?;
            Some(MltlParseTree::Global(l, *a, *b, Box::new(x)))
        },
        Mltl::Until(x, a, b, y) => {
            if *a > *b { return None; }
            let l = blocks(*a, *b, w)?;
            let x = with_width(x, w)?;
            let y = with_width(y, w)?;
            Some(MltlParseTree::Until(l, Box::new(x), *a, *b, Box::new(y)))
        },
        Mltl::Release(x, a, b, y) => {
            if *a > *b { return None; }
            let l = blocks(*a, *b, w)?;
            let x = with_width(x, w)?;
            let y = with_width(y, w)?;
            Some(MltlParseTree::Release(l, Box::new(x), *a, *b, Box::new(y)))
        },
    }
}

/// Attach `comps[*k]`, `comps[*k + 1]`, … to the temporal operators of `f`
/// in reading order (operator before its operands, left before right).
fn attach(f: &Mltl<usize>, comps: &Vec<Vec<usize>>, k: &mut usize) -> (r: Option<MltlExtExec>)
    ensures
        r is Some ==> to_mltl(ext_view(r->Some_0)) == *f,
    decreases f,
{
    match f {
        Mltl::True => Some(MltlParseTree::True(Vec::new())),
        Mltl::False => Some(MltlParseTree::False(Vec::new())),
        Mltl::Prop(p) => Some(MltlParseTree::Prop(Vec::new(), *p)),
        Mltl::Not(x) => {
            let x = attach(x, comps, k)?;
            Some(MltlParseTree::Not(Vec::new(), Box::new(x)))
        },
        Mltl::And(x, y) => {
            let x = attach(x, comps, k)?;
            let y = attach(y, comps, k)?;
            Some(MltlParseTree::And(Vec::new(), Box::new(x), Box::new(y)))
        },
        Mltl::Or(x, y) => {
            let x = attach(x, comps, k)?;
            let y = attach(y, comps, k)?;
            Some(MltlParseTree::Or(Vec::new(), Box::new(x), Box::new(y)))
        },
        Mltl::Future(a, b, x) => {
            if *k >= comps.len() { return None; }
            let l = clone_vec_usize(&comps[*k]);
            *k = *k + 1;
            let x = attach(x, comps, k)?;
            Some(MltlParseTree::Future(l, *a, *b, Box::new(x)))
        },
        Mltl::Global(a, b, x) => {
            if *k >= comps.len() { return None; }
            let l = clone_vec_usize(&comps[*k]);
            *k = *k + 1;
            let x = attach(x, comps, k)?;
            Some(MltlParseTree::Global(l, *a, *b, Box::new(x)))
        },
        Mltl::Until(x, a, b, y) => {
            if *k >= comps.len() { return None; }
            let l = clone_vec_usize(&comps[*k]);
            *k = *k + 1;
            let x = attach(x, comps, k)?;
            let y = attach(y, comps, k)?;
            Some(MltlParseTree::Until(l, Box::new(x), *a, *b, Box::new(y)))
        },
        Mltl::Release(x, a, b, y) => {
            if *k >= comps.len() { return None; }
            let l = clone_vec_usize(&comps[*k]);
            *k = *k + 1;
            let x = attach(x, comps, k)?;
            let y = attach(y, comps, k)?;
            Some(MltlParseTree::Release(l, Box::new(x), *a, *b, Box::new(y)))
        },
    }
}

/// `f` with the given compositions, one per temporal operator in reading
/// order (operator before its operands, left before right). For example,
/// `F[0,5] (p U[0,3] q)` with `[[3, 3], [2, 2]]` splits `F` into `[3, 3]`
/// and `U` into `[2, 2]`.
///
/// `Some(t)`: `t` is `f` with these compositions, and a valid input of
/// `LP_mltl`. `None`: the number of compositions is not the number of
/// temporal operators, some composition doesn't fit its interval (positive
/// widths summing to `b - a + 1`), or some interval has `a > b`.
pub fn with_compositions(f: &Mltl<usize>, comps: &Vec<Vec<usize>>) -> (r: Option<MltlExtExec>)
    ensures
        r is Some ==> {
            let t = ext_view(r->Some_0);
            &&& to_mltl(t) == *f
            &&& intervals_welldef(*f)
            &&& is_composition_MLTL(t)
        },
{
    let mut k = 0;
    let t = attach(f, comps, &mut k)?;
    if k != comps.len() || !check_lp_input(&t) {
        return None;
    }
    Some(t)
}

} // verus!
