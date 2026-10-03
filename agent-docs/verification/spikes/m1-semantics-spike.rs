use vstd::prelude::*;

verus! {

// ---- S1: recursive generic enum with Box, usize bounds ----
pub enum Formula<A> {
    True,
    False,
    Prop(A),
    Not(Box<Formula<A>>),
    And(Box<Formula<A>>, Box<Formula<A>>),
    Or(Box<Formula<A>>, Box<Formula<A>>),
    Future(usize, usize, Box<Formula<A>>),
    Global(usize, usize, Box<Formula<A>>),
    Until(Box<Formula<A>>, usize, usize, Box<Formula<A>>),
    Release(Box<Formula<A>>, usize, usize, Box<Formula<A>>),
}

// ---- S3: total drop (Isabelle drop i xs = [] when i > length) ----
pub open spec fn drop<T>(pi: Seq<T>, i: nat) -> Seq<T> {
    if i <= pi.len() { pi.skip(i as int) } else { Seq::empty() }
}

pub open spec fn semantics<A>(pi: Seq<ISet<A>>, f: Formula<A>) -> bool
    decreases f,
{
    match f {
        Formula::True => true,
        Formula::False => false,
        Formula::Prop(q) => pi.len() != 0 && pi[0].contains(q),
        Formula::Not(g) => !semantics(pi, *g),
        Formula::And(g, h) => semantics(pi, *g) && semantics(pi, *h),
        Formula::Or(g, h) => semantics(pi, *g) || semantics(pi, *h),
        Formula::Future(a, b, g) => a <= b && pi.len() > a
            && exists|i: nat| a <= i <= b && semantics(drop(pi, i), *g),
        Formula::Global(a, b, g) => a <= b && (pi.len() <= a
            || forall|i: nat| a <= i <= b ==> semantics(drop(pi, i), *g)),
        Formula::Until(g, a, b, h) => a <= b && pi.len() > a
            && exists|i: nat| a <= i <= b && semantics(drop(pi, i), *h)
                && forall|j: nat| a <= j < i ==> semantics(drop(pi, j), *g),
        Formula::Release(g, a, b, h) => a <= b && (pi.len() <= a
            || (forall|i: nat| a <= i <= b ==> semantics(drop(pi, i), *h))
            || exists|j: nat| a <= j <= (b - 1) as nat
                && semantics(drop(pi, j), *g)
                && forall|k: nat| a <= k <= j ==> semantics(drop(pi, k), *h)),
    }
}

// ---- S2/S4: exec trace view ----
pub open spec fn row_view(row: Seq<bool>) -> ISet<nat> {
    ISet::new(|p: nat| p < row.len() && row[p as int])
}
pub open spec fn trace_view(t: Seq<Vec<bool>>) -> Seq<ISet<nat>> {
    t.map_values(|r: Vec<bool>| row_view(r@))
}

broadcast use vstd::iset::group_iset_lemmas;

proof fn lemma_drop_drop<T>(pi: Seq<T>, s: nat, i: nat)
    requires s <= pi.len(),
    ensures drop(drop(pi, s), i) == drop(pi, s + i),
{
    if s + i <= pi.len() { assert(drop(drop(pi, s), i) =~= drop(pi, s + i)); }
}

proof fn lemma_drop_past_end<T>(pi: Seq<T>, i: nat)
    requires i >= pi.len(),
    ensures drop(pi, i) == drop(pi, pi.len()),
{
    assert(drop(pi, pi.len()) =~= Seq::<T>::empty());
}

// Isabelle examples (MLTL_Encoding.thy), with nat atoms
proof fn example_not_future() {
    reveal_with_fuel(semantics, 3);
    let pi = seq![ISet::empty().insert(0nat)];
    assert(drop(pi, 0) =~= pi);
    assert(semantics(drop(pi, 0), Formula::Prop(0nat)));
    let f = Formula::Not(Box::new(Formula::Future(0, 2, Box::new(Formula::Prop(0nat)))));
    assert(!semantics(pi, f));
}

proof fn example_future_not() {
    reveal_with_fuel(semantics, 3);
    let pi = seq![ISet::empty().insert(0nat)];
    let g = Formula::Not(Box::new(Formula::Prop(0nat)));
    assert(pi.len() == 1);
    assert(drop(pi, 1).len() == 0);
    assert(semantics(drop(pi, 1), g));
    let fut = Formula::Future(0, 2, Box::new(g));
    assert(pi.len() > 0usize);
    assert(exists|i: nat| 0usize <= i <= 2usize && semantics(#[trigger] drop(pi, i), g));
    assert(fut matches Formula::Future(a, b, h) && a == 0 && b == 2 && *h == g);
    assert(semantics(pi, fut));
}

proof fn example_global() {
    reveal_with_fuel(semantics, 3);
    let pi = seq![ISet::empty().insert(0nat)];
    assert(pi.len() == 1);
    assert(drop(pi, 1).len() == 0);
    assert(!semantics(drop(pi, 1), Formula::Prop(0nat)));
    assert(!semantics(pi, Formula::Global(0, 2, Box::new(Formula::Prop(0nat)))));
}

pub open spec fn fragment(f: Formula<nat>) -> bool decreases f {
    match f {
        Formula::True | Formula::False | Formula::Prop(_) => true,
        Formula::Not(g) => fragment(*g),
        Formula::And(g, h) | Formula::Or(g, h) => fragment(*g) && fragment(*h),
        Formula::Future(_, _, g) => fragment(*g),
        _ => false,
    }
}

pub fn eval(t: &[Vec<bool>], start: usize, f: &Formula<usize>) -> (r: bool)
    requires start <= t.len(), fragment(view_f(*f)),
    ensures r == semantics(drop(trace_view(t@), start as nat), view_f(*f)),
    decreases *f,
{
    let ghost tv = trace_view(t@);
    let ghost pi = drop(tv, start as nat);
    match f {
        Formula::True => true,
        Formula::False => false,
        Formula::Prop(q) => {
            if start < t.len() {
                let row = &t[start];
                assert(pi[0] == row_view(row@));
                *q < row.len() && row[*q]
            } else { false }
        }
        Formula::Not(g) => !eval(t, start, g),
        Formula::And(g, h) => { let x = eval(t, start, g); let y = eval(t, start, h); x && y }
        Formula::Or(g, h) => { let x = eval(t, start, g); let y = eval(t, start, h); x || y }
        Formula::Future(a, b, g) => {
            let (a, b) = (*a, *b);
            let rem = t.len() - start;
            if !(a <= b && rem > a) { return false; }
            // Positions past the trace end all see the empty suffix; checking up to
            // min(b, rem) covers them (lemma_drop_past_end).
            assert(tv.len() == t.len());
            assert(pi.len() == rem);
            let hi = if b < rem { b } else { rem };
            assert(view_f(*f) == Formula::<nat>::Future(a, b, Box::new(view_f(**g))));
            let mut i = a;
            loop
                invariant
                    a <= i, i <= hi, hi <= rem, rem == t.len() - start, a <= b, hi <= b, rem > a,
                    hi == b || hi == rem,
                    start <= t.len(), fragment(view_f(**g)),
                    *f == Formula::<usize>::Future(a, b, *g), pi.len() == rem,
                    view_f(*f) == Formula::<nat>::Future(a, b, Box::new(view_f(**g))),
                    tv == trace_view(t@), pi == drop(tv, start as nat),
                    forall|k: nat| a <= k < i ==> !semantics(#[trigger] drop(pi, k), view_f(**g)),
                ensures
                    forall|k: nat| a <= k <= hi ==> !semantics(#[trigger] drop(pi, k), view_f(**g)),
                decreases hi - i,
            {
                proof { lemma_drop_drop(tv, start as nat, i as nat); }
                if eval(t, start + i, g) {
                    assert(semantics(drop(pi, i as nat), view_f(**g)));
                    return true;
                }
                assert(!semantics(drop(pi, i as nat), view_f(**g)));
                if i == hi { break; }
                i = i + 1;
            }
            proof {
                assert forall|k: nat| a <= k <= b implies !semantics(#[trigger] drop(pi, k), view_f(**g)) by {
                    if k > hi {
                        lemma_drop_past_end(pi, k);
                        lemma_drop_past_end(pi, hi as nat);
                    }
                }
            }
            false
        }
        _ => { assert(false); false }
    }
}

pub open spec fn view_f(f: Formula<usize>) -> Formula<nat> decreases f {
    match f {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Prop(q) => Formula::Prop(q as nat),
        Formula::Not(g) => Formula::Not(Box::new(view_f(*g))),
        Formula::And(g, h) => Formula::And(Box::new(view_f(*g)), Box::new(view_f(*h))),
        Formula::Or(g, h) => Formula::Or(Box::new(view_f(*g)), Box::new(view_f(*h))),
        Formula::Future(a, b, g) => Formula::Future(a, b, Box::new(view_f(*g))),
        Formula::Global(a, b, g) => Formula::Global(a, b, Box::new(view_f(*g))),
        Formula::Until(g, a, b, h) => Formula::Until(Box::new(view_f(*g)), a, b, Box::new(view_f(*h))),
        Formula::Release(g, a, b, h) => Formula::Release(Box::new(view_f(*g)), a, b, Box::new(view_f(*h))),
    }
}

} // verus!
verus! {
proof fn probe_not(pi: Seq<ISet<nat>>) {
    reveal_with_fuel(semantics, 2);
    assert(semantics(pi, Formula::Not(Box::new(Formula::<nat>::False))));
}
proof fn probe_fut_param(pi: Seq<ISet<nat>>, f: Formula<nat>, g: Formula<nat>)
    requires f == Formula::<nat>::Future(0, 2, Box::new(g)),
{
    reveal_with_fuel(semantics, 2);
    assert(semantics(pi, f) ==> pi.len() > 0);
    assert(semantics(pi, f) ==> exists|i: nat| 0 <= i <= 2 && semantics(#[trigger] drop(pi, i), g));
    assert((pi.len() > 0 && semantics(drop(pi, 1), g)) ==> semantics(pi, f));
}
proof fn probe_fut_and(pi: Seq<ISet<nat>>, g: Formula<nat>) {
    let f = Formula::And(Box::new(g), Box::new(g));
    assert(semantics(pi, f) == (semantics(pi, g) && semantics(pi, g)));
}
proof fn probe_true_fut(pi: Seq<ISet<nat>>) {
    let f = Formula::<nat>::Future(0, 2, Box::new(Formula::True));
    reveal_with_fuel(semantics, 2);
    assert(pi.len() > 0 ==> semantics(drop(pi, 0), Formula::<nat>::True));
    assert(pi.len() > 0 ==> semantics(pi, f));
}
}
