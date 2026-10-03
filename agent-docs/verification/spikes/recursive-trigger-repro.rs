use vstd::prelude::*;
verus! {
pub enum F { T, Fut(usize, Box<F>) }
// V1: no explicit trigger
pub open spec fn sem1(pi: Seq<nat>, f: F) -> bool decreases f {
    match f { F::T => true, F::Fut(b, g) => exists|i: nat| i <= b && sem1(pi.skip(i as int), *g) }
}
proof fn v1(pi: Seq<nat>, g: F) {
    assert(sem1(pi.skip(1), g) ==> sem1(pi, F::Fut(2, Box::new(g))));
}
// V2: bind subformula with let outside quantifier
pub open spec fn sem2(pi: Seq<nat>, f: F) -> bool decreases f {
    match f { F::T => true, F::Fut(b, g) => { let h = *g; exists|i: nat| i <= b && #[trigger] sem2(pi.skip(i as int), h) } }
}
proof fn v2(pi: Seq<nat>, g: F) {
    assert(sem2(pi.skip(1), g) ==> sem2(pi, F::Fut(2, Box::new(g))));
}
// V3: explicit witness via assert on the definition after reveal
proof fn v3(pi: Seq<nat>, g: F) {
    let f = F::Fut(2, Box::new(g));
    if sem1(pi.skip(1), g) {
        assert(exists|i: nat| i <= 2 && sem1(pi.skip(i as int), g)) by { assert(1nat <= 2); }
        assert(sem1(pi, f));
    }
}
// V4: helper spec fn for the quantifier (no recursion inside quantifier body syntactically)
pub open spec fn sem4(pi: Seq<nat>, f: F) -> bool decreases f {
    match f { F::T => true, F::Fut(b, g) => exists|i: nat| i <= b && #[trigger] sem4(pi.skip(i as int), *g) }
}
proof fn v4(pi: Seq<nat>, g: F) {
    let f = F::Fut(2, Box::new(g));
    assert(f->Fut_1 == Box::new(g));
    assert(*f->Fut_1 == g);
    assert(sem4(pi.skip(1), g) ==> sem4(pi, f));
}
fn main() {}
}
