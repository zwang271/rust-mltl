//! Subformula table: every distinct subformula of a BNF formula gets one id
//! (hash-consing), so the executable encoding has one Boolean variable per
//! `(subformula, time)`, exactly like the Isabelle translation's atoms.
//! Also executable `complen_mltl` and `intervals_welldef`.
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;

verus! {

/// One table entry: a BNF constructor whose children are table ids.
pub enum Node {
    True,
    Prop(usize),
    Not(usize),
    And(usize, usize),
    Until(usize, usize, usize, usize),
}

/// Entry `i` describes subformula `sub[i]`; children come earlier.
pub open spec fn node_ok(nodes: Seq<Node>, sub: Seq<Mltl<usize>>, i: int) -> bool {
    match nodes[i] {
        Node::True => sub[i] == Mltl::<usize>::True,
        Node::Prop(p) => sub[i] == Mltl::<usize>::Prop(p),
        Node::Not(c) => c < i && sub[i] == Mltl::Not(Box::new(sub[c as int])),
        Node::And(c, d) => c < i && d < i && sub[i] == Mltl::And(Box::new(sub[c as int]), Box::new(sub[d as int])),
        Node::Until(c, a, b, d) => c < i && d < i && sub[i] == Mltl::Until(
            Box::new(sub[c as int]),
            a,
            b,
            Box::new(sub[d as int]),
        ),
    }
}

pub open spec fn table_ok(nodes: Seq<Node>, sub: Seq<Mltl<usize>>) -> bool {
    &&& nodes.len() == sub.len()
    &&& forall|i: int| 0 <= i < nodes.len() ==> #[trigger] node_ok(nodes, sub, i)
    &&& forall|i: int, j: int|
        0 <= i < sub.len() && 0 <= j < sub.len() && i != j ==> #[trigger] sub[i] != #[trigger] sub[j]
}

pub struct Table {
    pub nodes: Vec<Node>,
    pub sub: Ghost<Seq<Mltl<usize>>>,
}

pub proof fn extends_trans(t0: &Table, t1: &Table, t2: &Table)
    requires
        t1.extends(t0),
        t2.extends(t1),
    ensures
        t2.extends(t0),
{
    assert forall|i: int| 0 <= i < t0.sub@.len() implies #[trigger] t2.sub@[i] == t0.sub@[i] && t2.nodes@[i]
        == t0.nodes@[i] by {
        assert(t1.sub@[i] == t0.sub@[i]);
        assert(t2.sub@[i] == t1.sub@[i]);
    }
}

impl Table {
    pub open spec fn ok(&self) -> bool {
        table_ok(self.nodes@, self.sub@)
    }

    /// `self` extends `old` (ids are stable).
    pub open spec fn extends(&self, old: &Table) -> bool {
        &&& old.sub@.len() <= self.sub@.len()
        &&& forall|i: int| 0 <= i < old.sub@.len() ==> #[trigger] self.sub@[i] == old.sub@[i] && self.nodes@[i]
            == old.nodes@[i]
    }
}

fn node_eq(x: &Node, y: &Node) -> (r: bool)
    ensures
        r == (*x == *y),
{
    match (x, y) {
        (Node::True, Node::True) => true,
        (Node::Prop(p), Node::Prop(q)) => *p == *q,
        (Node::Not(c), Node::Not(d)) => *c == *d,
        (Node::And(c1, d1), Node::And(c2, d2)) => *c1 == *c2 && *d1 == *d2,
        (Node::Until(c1, a1, b1, d1), Node::Until(c2, a2, b2, d2)) => *c1 == *c2 && *a1 == *a2 && *b1 == *b2
            && *d1 == *d2,
        _ => false,
    }
}

/// A subformula already in the table has the same entry.
proof fn same_sub_same_node(nodes: Seq<Node>, sub: Seq<Mltl<usize>>, key: Node, m: Mltl<usize>, j: int)
    requires
        table_ok(nodes, sub),
        node_ok(nodes.push(key), sub.push(m), nodes.len() as int),
        0 <= j < nodes.len(),
        sub[j] == m,
    ensures
        nodes[j] == key,
{
    let n2 = nodes.push(key);
    let s2 = sub.push(m);
    let len = nodes.len() as int;
    assert(node_ok(nodes, sub, j));
    assert(n2[len] == key);
    match key {
        Node::Not(c) => {
            assert(s2[c as int] == sub[c as int]);
            match nodes[j] {
                Node::Not(c2) => {
                    assert(sub[c2 as int] == sub[c as int]);
                },
                _ => {},
            }
        },
        Node::And(c, d) => {
            assert(s2[c as int] == sub[c as int]);
            assert(s2[d as int] == sub[d as int]);
            match nodes[j] {
                Node::And(c2, d2) => {
                    assert(sub[c2 as int] == sub[c as int]);
                    assert(sub[d2 as int] == sub[d as int]);
                },
                _ => {},
            }
        },
        Node::Until(c, a, b, d) => {
            assert(s2[c as int] == sub[c as int]);
            assert(s2[d as int] == sub[d as int]);
            match nodes[j] {
                Node::Until(c2, a2, b2, d2) => {
                    assert(sub[c2 as int] == sub[c as int]);
                    assert(sub[d2 as int] == sub[d as int]);
                },
                _ => {},
            }
        },
        _ => {
            match nodes[j] {
                Node::Not(c2) => {},
                Node::And(c2, d2) => {},
                Node::Until(c2, a2, b2, d2) => {},
                _ => {},
            }
        },
    }
}

proof fn found_same(nodes: Seq<Node>, sub: Seq<Mltl<usize>>, key: Node, m: Mltl<usize>, i: int)
    requires
        table_ok(nodes, sub),
        node_ok(nodes.push(key), sub.push(m), nodes.len() as int),
        0 <= i < nodes.len(),
        nodes[i] == key,
    ensures
        sub[i] == m,
{
    let n2 = nodes.push(key);
    let s2 = sub.push(m);
    let len = nodes.len() as int;
    assert(n2[len] == key);
    assert(s2[len] == m);
    assert(node_ok(nodes, sub, i));
    match key {
        Node::Not(c) => {
            assert(s2[c as int] == sub[c as int]);
        },
        Node::And(c, d) => {
            assert(s2[c as int] == sub[c as int]);
            assert(s2[d as int] == sub[d as int]);
        },
        Node::Until(c, a, b, d) => {
            assert(s2[c as int] == sub[c as int]);
            assert(s2[d as int] == sub[d as int]);
        },
        _ => {},
    }
}

/// The id of the subformula described by `key` (`m`), adding it if new.
fn find_or_add(t: &mut Table, key: Node, Ghost(m): Ghost<Mltl<usize>>) -> (id: usize)
    requires
        old(t).ok(),
        node_ok(old(t).nodes@.push(key), old(t).sub@.push(m), old(t).nodes@.len() as int),
    ensures
        final(t).ok(),
        final(t).extends(old(t)),
        id < final(t).sub@.len(),
        final(t).sub@[id as int] == m,
{
    let mut i: usize = 0;
    while i < t.nodes.len()
        invariant
            t.ok(),
            t.nodes@ == old(t).nodes@,
            t.sub@ == old(t).sub@,
            i <= t.nodes@.len(),
            forall|j: int| 0 <= j < i ==> t.nodes@[j] != key,
            node_ok(t.nodes@.push(key), t.sub@.push(m), t.nodes@.len() as int),
        decreases t.nodes@.len() - i,
    {
        if node_eq(&t.nodes[i], &key) {
            proof { found_same(t.nodes@, t.sub@, key, m, i as int); }
            return i;
        }
        i += 1;
    }
    let ghost old_nodes = t.nodes@;
    let ghost old_sub = t.sub@;
    proof {
        assert forall|j: int| 0 <= j < old_sub.len() implies old_sub[j] != m by {
            if old_sub[j] == m {
                same_sub_same_node(old_nodes, old_sub, key, m, j);
            }
        }
    }
    t.nodes.push(key);
    t.sub = Ghost(t.sub@.push(m));
    proof {
        let ns = t.nodes@;
        let ss = t.sub@;
        assert forall|j: int| 0 <= j < ns.len() implies #[trigger] node_ok(ns, ss, j) by {
            if j < old_nodes.len() {
                assert(node_ok(old_nodes, old_sub, j));
                assert(ns[j] == old_nodes[j]);
                match ns[j] {
                    Node::Not(c) => { assert(ss[c as int] == old_sub[c as int]); },
                    Node::And(c, d) => {
                        assert(ss[c as int] == old_sub[c as int]);
                        assert(ss[d as int] == old_sub[d as int]);
                    },
                    Node::Until(c, a, b, d) => {
                        assert(ss[c as int] == old_sub[c as int]);
                        assert(ss[d as int] == old_sub[d as int]);
                    },
                    _ => {},
                }
            }
        }
        assert forall|a: int, b: int| 0 <= a < ss.len() && 0 <= b < ss.len() && a != b implies #[trigger] ss[a]
            != #[trigger] ss[b] by {
            if a < old_sub.len() && b < old_sub.len() {
                assert(ss[a] == old_sub[a] && ss[b] == old_sub[b]);
            } else if a < old_sub.len() {
                assert(ss[a] == old_sub[a]);
            } else {
                assert(ss[b] == old_sub[b]);
            }
        }
    }
    t.nodes.len() - 1
}

/// Add every subformula of the BNF formula `f`; returns the id of `f`.
pub fn intern(t: &mut Table, f: &Mltl<usize>) -> (id: usize)
    requires
        old(t).ok(),
        is_bnf(*f),
    ensures
        final(t).ok(),
        final(t).extends(old(t)),
        id < final(t).sub@.len(),
        final(t).sub@[id as int] == *f,
    decreases *f,
{
    let ghost t0 = *t;
    match f {
        Mltl::True => find_or_add(t, Node::True, Ghost(*f)),
        Mltl::Prop(p) => find_or_add(t, Node::Prop(*p), Ghost(*f)),
        Mltl::Not(g) => {
            let c = intern(t, g);
            let ghost t1 = *t;
            let r = find_or_add(t, Node::Not(c), Ghost(*f));
            proof { extends_trans(&t0, &t1, t); }
            r
        },
        Mltl::And(g, h) => {
            let c = intern(t, g);
            let ghost t1 = *t;
            let d = intern(t, h);
            let ghost t2 = *t;
            assert(t.sub@[c as int] == t1.sub@[c as int]);
            let r = find_or_add(t, Node::And(c, d), Ghost(*f));
            proof { extends_trans(&t0, &t1, &t2); extends_trans(&t0, &t2, t); }
            r
        },
        Mltl::Until(g, a, b, h) => {
            let c = intern(t, g);
            let ghost t1 = *t;
            let d = intern(t, h);
            let ghost t2 = *t;
            assert(t.sub@[c as int] == t1.sub@[c as int]);
            let r = find_or_add(t, Node::Until(c, *a, *b, d), Ghost(*f));
            proof { extends_trans(&t0, &t1, &t2); extends_trans(&t0, &t2, t); }
            r
        },
        _ => {
            assert(false);
            0
        },
    }
}

/// The atoms with a `Prop` entry.
pub open spec fn table_props(nodes: Seq<Node>) -> Set<usize>
    decreases nodes.len(),
{
    if nodes.len() == 0 {
        Set::empty()
    } else {
        let rest = table_props(nodes.drop_last());
        match nodes.last() {
            Node::Prop(p) => rest.insert(p),
            _ => rest,
        }
    }
}

pub proof fn table_props_contains(nodes: Seq<Node>, p: usize)
    ensures
        table_props(nodes).contains(p) == exists|j: int| 0 <= j < nodes.len() && nodes[j] == Node::Prop(p),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let d = nodes.drop_last();
        table_props_contains(d, p);
        if table_props(nodes).contains(p) {
            if !table_props(d).contains(p) {
                assert(nodes[nodes.len() - 1] == Node::Prop(p));
            } else {
                let j = choose|j: int| 0 <= j < d.len() && d[j] == Node::Prop(p);
                assert(nodes[j] == d[j]);
            }
        } else if exists|j: int| 0 <= j < nodes.len() && nodes[j] == Node::Prop(p) {
            let j = choose|j: int| 0 <= j < nodes.len() && nodes[j] == Node::Prop(p);
            if j < nodes.len() - 1 {
                assert(d[j] == nodes[j]);
            }
        }
    }
}

/// `sub[i]` is `Prop p` exactly when entry `i` is `Prop(p)`.
pub proof fn sub_prop_iff(nodes: Seq<Node>, sub: Seq<Mltl<usize>>, i: int, p: usize)
    requires
        table_ok(nodes, sub),
        0 <= i < nodes.len(),
    ensures
        (sub[i] == Mltl::<usize>::Prop(p)) == (nodes[i] == Node::Prop(p)),
{
    assert(node_ok(nodes, sub, i));
}

/// Every atom of every entry has a `Prop` entry.
pub proof fn atoms_in_table(nodes: Seq<Node>, sub: Seq<Mltl<usize>>, i: int)
    requires
        table_ok(nodes, sub),
        0 <= i < nodes.len(),
    ensures
        atoms_mltl(sub[i]).subset_of(table_props(nodes)),
    decreases i,
{
    assert(node_ok(nodes, sub, i));
    match nodes[i] {
        Node::True => {},
        Node::Prop(p) => {
            table_props_contains(nodes, p);
        },
        Node::Not(c) => {
            atoms_in_table(nodes, sub, c as int);
        },
        Node::And(c, d) => {
            atoms_in_table(nodes, sub, c as int);
            atoms_in_table(nodes, sub, d as int);
        },
        Node::Until(c, a, b, d) => {
            atoms_in_table(nodes, sub, c as int);
            atoms_in_table(nodes, sub, d as int);
        },
    }
}

/// Executable `complen_mltl` (`None` on overflow).
pub fn complen_exec(f: &Mltl<usize>) -> (r: Option<usize>)
    ensures
        r is Some ==> r->0 as nat == complen_mltl(*f),
    decreases *f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => Some(1),
        Mltl::Not(g) => complen_exec(g),
        Mltl::And(g, h) | Mltl::Or(g, h) => {
            let x = complen_exec(g)?;
            let y = complen_exec(h)?;
            Some(if x >= y { x } else { y })
        },
        Mltl::Future(_, b, g) | Mltl::Global(_, b, g) => {
            let x = complen_exec(g)?;
            b.checked_add(x)
        },
        Mltl::Until(g, _, b, h) | Mltl::Release(g, _, b, h) => {
            let x = complen_exec(g)?;
            let y = complen_exec(h)?;
            let x1 = if x >= 1 { x - 1 } else { 0 };
            let m = if x1 >= y { x1 } else { y };
            b.checked_add(m)
        },
    }
}

/// Executable `intervals_welldef`.
pub fn check_welldef(f: &Mltl<usize>) -> (r: bool)
    ensures
        r == intervals_welldef(*f),
    decreases *f,
{
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => true,
        Mltl::Not(g) => check_welldef(g),
        Mltl::And(g, h) | Mltl::Or(g, h) => check_welldef(g) && check_welldef(h),
        Mltl::Future(a, b, g) | Mltl::Global(a, b, g) => *a <= *b && check_welldef(g),
        Mltl::Until(g, a, b, h) | Mltl::Release(g, a, b, h) => *a <= *b && check_welldef(g) && check_welldef(h),
    }
}

} // verus!
