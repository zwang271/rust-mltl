//! The bounded ring buffer of a shared connection queue (Isabelle
//! `R2U2_SCQ.thy`: `scq_values`, `write_ptr`, read pointers, `scq_write`,
//! `scq_read_aux`; Rust `memory/scq.rs`).
//!
//! The link to the history model ([`ring_abs`]): a ring of `N` slots holds
//! the last `N` entries of the compacted history, entry `i` in slot
//! `i mod N`, and the write pointer is `len mod N`. Writing keeps the link
//! ([`lemma_ring_write`]). A read from a pointer that is at or before the
//! first needed entry, and still in the ring, returns exactly what the
//! history model's read returns ([`lemma_ring_read`]).
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use crate::verdict::*;

verus! {

/// Isabelle's `scq_values` + `write_ptr`. `None` is `undecidedV` (empty slot).
pub struct Ring {
    pub slots: Seq<Option<Verdict>>,
    pub write_ptr: nat,
}

/// `initial_SCQ sz tau` (ring part): `sz` empty slots.
pub open spec fn empty_ring(size: nat) -> Ring {
    Ring { slots: Seq::new(size, |i: int| None), write_ptr: 0 }
}

/// `circ_succ ptr Q_size`
pub open spec fn circ_succ(p: nat, n: nat) -> nat {
    ((p + 1) as int % (n as int)) as nat
}

/// `circ_minus ptr Q_size`
pub open spec fn circ_minus(p: nat, n: nat) -> nat {
    if p == 0 { (n - 1) as nat } else { (p - 1) as nat }
}

/// `scq_write Q v` (ring part): if the previous slot holds the same value,
/// overwrite it; otherwise write at the write pointer and advance it.
pub open spec fn ring_write(r: Ring, v: Verdict) -> Ring {
    let n = r.slots.len();
    let prev = circ_minus(r.write_ptr, n);
    let same = match r.slots[prev as int] {
        Some(pv) => pv.val == v.val,
        None => false,
    };
    if same {
        Ring { slots: r.slots.update(prev as int, Some(v)), write_ptr: r.write_ptr }
    } else {
        Ring { slots: r.slots.update(r.write_ptr as int, Some(v)), write_ptr: circ_succ(r.write_ptr, n) }
    }
}

/// `scq_read_aux parent_Q child_Q LR rd_ptr`: scan from the read pointer
/// for the first entry at or after `tau`; stop before the write pointer.
/// Returns the entry (or `None`) and the new read pointer.
pub open spec fn ring_scan(r: Ring, rd: nat, tau: nat, fuel: nat) -> (Option<Verdict>, nat)
    decreases fuel,
{
    let n = r.slots.len();
    if fuel == 0 || rd >= n || r.write_ptr >= n || (r.slots[rd as int].is_none() && rd == 0) {
        (None, rd)
    } else if r.slots[rd as int].is_some() && r.slots[rd as int].unwrap().time >= tau {
        (r.slots[rd as int], rd)
    } else if circ_succ(rd, n) == r.write_ptr {
        (None, rd)
    } else {
        ring_scan(r, circ_succ(rd, n), tau, (fuel - 1) as nat)
    }
}

/// `scq_read` (one side): at most one lap of the ring.
pub open spec fn ring_read(r: Ring, rd: nat, tau: nat) -> (Option<Verdict>, nat) {
    ring_scan(r, rd, tau, r.slots.len())
}

/// The ring holds the last `N` entries of `c` (compacted history), entry
/// `i` in slot `i mod N`; unused slots are empty; `write_ptr = len mod N`.
pub open spec fn ring_abs(r: Ring, c: Seq<Verdict>) -> bool {
    let n = r.slots.len();
    &&& n > 0
    &&& r.write_ptr == c.len() as int % (n as int)
    &&& forall|i: int| 0 <= i < c.len() && c.len() - n <= i ==> r.slots[i % (n as int)] == Some(#[trigger] c[i])
    &&& forall|s: int| c.len() <= s < n ==> #[trigger] r.slots[s] == None::<Verdict>
}

// ---------------------------------------------------------------------------
// Modular arithmetic
// ---------------------------------------------------------------------------

pub proof fn lemma_mod_succ(k: nat, n: nat)
    requires
        n > 0,
    ensures
        circ_succ((k as int % (n as int)) as nat, n) == (k + 1) as int % (n as int),
{
    let q = k as int / (n as int);
    let r = k as int % (n as int);
    lemma_fundamental_div_mod(k as int, n as int);
    lemma_mod_pos_bound(k as int, n as int);
    if r + 1 < n {
        lemma_fundamental_div_mod_converse((k + 1) as int, n as int, q, r + 1);
        lemma_small_mod((r + 1) as nat, n);
    } else {
        assert(k + 1 == (q + 1) * n) by (nonlinear_arith) requires k == q * n + r, r + 1 == n;
        lemma_fundamental_div_mod_converse((k + 1) as int, n as int, q + 1, 0);
        lemma_mod_self_0(n as int);
    }
}

pub proof fn lemma_mod_pred(k: nat, n: nat)
    requires
        n > 0,
        k >= 1,
    ensures
        circ_minus((k as int % (n as int)) as nat, n) == (k - 1) as int % (n as int),
{
    lemma_mod_succ((k - 1) as nat, n);
    lemma_mod_pos_bound((k - 1) as int, n as int);
    lemma_mod_pos_bound(k as int, n as int);
    let r = (k - 1) as int % (n as int);
    if r + 1 < n {
        lemma_small_mod((r + 1) as nat, n);
    } else {
        lemma_mod_self_0(n as int);
    }
}

/// Indices less than `n` apart land in different slots.
pub proof fn lemma_mod_distinct(i: int, j: int, n: int)
    requires
        n > 0,
        0 <= i < j,
        j - i < n,
    ensures
        i % n != j % n,
{
    lemma_fundamental_div_mod(i, n);
    lemma_fundamental_div_mod(j, n);
    lemma_mod_pos_bound(i, n);
    lemma_mod_pos_bound(j, n);
    if i % n == j % n {
        let (qi, qj) = (i / n, j / n);
        assert(j - i == (qj - qi) * n) by (nonlinear_arith) requires i == n * qi + i % n, j == n * qj + j % n, i % n == j % n;
        assert(qj - qi > 0) by (nonlinear_arith) requires j - i == (qj - qi) * n, j - i > 0, n > 0;
        assert((qj - qi) * n >= n) by (nonlinear_arith) requires qj - qi >= 1, n > 0;
    }
}

// ---------------------------------------------------------------------------
// Writing and reading keep the link to the history
// ---------------------------------------------------------------------------

pub proof fn lemma_ring_write(r: Ring, h: Seq<Verdict>, v: Verdict)
    requires
        ring_abs(r, compact(h)),
        strictly_increasing(h.push(v)),
    ensures
        ring_abs(ring_write(r, v), compact(h.push(v))),
        ring_write(r, v).slots.len() == r.slots.len(),
{
    let n = r.slots.len();
    let ni = n as int;
    let c = compact(h);
    let len = c.len();
    assert(h.push(v).drop_last() =~= h);
    assert(h.push(v).last() == v);
    let c2 = compact(h.push(v));
    assert(strictly_increasing(h)) by {
        assert forall|i: int, k: int| #![trigger h[i], h[k]] 0 <= i < k < h.len() implies h[i].time < h[k].time by {
            assert(h[i] == h.push(v)[i] && h[k] == h.push(v)[k]);
        }
    }
    lemma_compact(h);
    let prev = circ_minus(r.write_ptr, n);
    lemma_mod_pos_bound(len as int, ni);
    if len >= 1 {
        lemma_mod_pred(len, n);
        assert(r.slots[prev as int] == Some(c[len - 1]));
    } else {
        lemma_small_mod(0, n);
        assert(r.slots[prev as int] == None::<Verdict>);
    }
    let r2 = ring_write(r, v);
    if len > 0 && c.last().val == v.val {
        assert(c2 == c.update(len - 1, v));
        assert forall|i: int| 0 <= i < c2.len() && c2.len() - n <= i implies r2.slots[i % ni] == Some(#[trigger] c2[i]) by {
            if i != len - 1 {
                lemma_mod_distinct(i, len - 1, ni);
            }
        }
        assert forall|s: int| c2.len() <= s < n implies #[trigger] r2.slots[s] == None::<Verdict> by {
            lemma_mod_pos_bound(len - 1, ni);
            lemma_mod_le_self(len - 1, ni);
        }
    } else {
        assert(c2 == c.push(v));
        lemma_mod_succ(len, n);
        assert forall|i: int| 0 <= i < c2.len() && c2.len() - n <= i implies r2.slots[i % ni] == Some(#[trigger] c2[i]) by {
            if i < len {
                lemma_mod_distinct(i, len as int, ni);
                assert(c2[i] == c[i]);
            }
        }
        assert forall|s: int| c2.len() <= s < n implies #[trigger] r2.slots[s] == None::<Verdict> by {
            lemma_small_mod(len, n);
        }
    }
}

proof fn lemma_mod_le_self(x: int, n: int)
    requires
        x >= 0,
        n > 0,
    ensures
        x % n <= x,
{
    lemma_fundamental_div_mod(x, n);
    lemma_mod_pos_bound(x, n);
    lemma_div_pos_is_pos(x, n);
    assert(n * (x / n) >= 0) by (nonlinear_arith) requires x / n >= 0, n > 0;
}

/// Scanning from logical entry `j` (slot `j mod N`) up to the first needed
/// entry.
pub proof fn lemma_ring_scan(r: Ring, c: Seq<Verdict>, j: nat, tau: nat, fuel: nat)
    requires
        ring_abs(r, c),
        strictly_increasing(c),
        j < c.len(),
        c.len() - j <= r.slots.len(),
        j <= first_idx(c, tau),
        fuel >= c.len() - j,
    ensures
        ring_scan(r, (j as int % (r.slots.len() as int)) as nat, tau, fuel) == (first_from(c, tau),
            ((if first_idx(c, tau) < c.len() { first_idx(c, tau) } else { (c.len() - 1) as nat }) as int % (r.slots.len() as int)) as nat),
    decreases fuel,
{
    let n = r.slots.len();
    let ni = n as int;
    let len = c.len();
    lemma_first_idx(c, tau);
    lemma_mod_pos_bound(j as int, ni);
    lemma_mod_pos_bound(len as int, ni);
    let rd = (j as int % ni) as nat;
    assert(r.slots[rd as int] == Some(c[j as int]));
    if j < first_idx(c, tau) {
        assert(c[j as int].time < tau);
        lemma_mod_succ(j, n);
        if j + 1 == len {
            assert(circ_succ(rd, n) == r.write_ptr);
        } else {
            lemma_mod_distinct((j + 1) as int, len as int, ni);
            assert(circ_succ(rd, n) != r.write_ptr);
            lemma_ring_scan(r, c, j + 1, tau, (fuel - 1) as nat);
        }
    }
}

/// A read from a pointer at logical entry `j` (at or before the first
/// needed entry, still in the ring) returns what the history model reads,
/// and leaves the pointer at that entry (or the last one).
pub proof fn lemma_ring_read(r: Ring, c: Seq<Verdict>, rd: nat, j: nat, tau: nat)
    requires
        ring_abs(r, c),
        strictly_increasing(c),
        (c.len() == 0 && rd == 0) || (j < c.len() && c.len() - j <= r.slots.len()
            && rd == j as int % (r.slots.len() as int) && j <= first_idx(c, tau)),
    ensures
        ring_read(r, rd, tau).0 == first_from(c, tau),
        c.len() == 0 ==> ring_read(r, rd, tau).1 == 0,
        c.len() > 0 ==> ring_read(r, rd, tau).1
            == ((if first_idx(c, tau) < c.len() { first_idx(c, tau) } else { (c.len() - 1) as nat }) as int % (r.slots.len() as int)) as nat,
{
    if c.len() == 0 {
        lemma_first_idx(c, tau);
        assert(r.slots[0] == None::<Verdict>);
    } else {
        lemma_ring_scan(r, c, j, tau, r.slots.len());
    }
}

} // verus!
