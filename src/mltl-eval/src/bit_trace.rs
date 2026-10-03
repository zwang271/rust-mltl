//! Bit-row traces: one row of bits per atom; bit i of row a says whether
//! atom a holds at step i. Its meaning (`view_trace`) is defined from the
//! bits alone; `from_sets` is proved to produce the bit trace denoting the
//! same spec trace as its set-per-step input.
use vstd::prelude::*;
use std::collections::HashSet;
use crate::trace::*;
use crate::atom_read::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct BitTrace {
    pub len: usize,
    pub rows: Vec<Vec<u64>>,
}

/// Bit k of word w.
pub open spec fn bit(w: u64, k: u64) -> bool {
    (w >> k) & 1u64 == 1u64
}

/// Number of 64-bit words needed for n steps.
pub open spec fn words_for(n: nat) -> nat {
    (n + 63) / 64
}

impl BitTrace {
    /// Does atom a hold at step i (a < rows.len(), i < len)?
    pub open spec fn holds_spec(&self, a: int, i: int) -> bool {
        bit(self.rows@[a]@[i / 64], (i % 64) as u64)
    }

    /// The atoms among 0..k that hold at step i, as a finite set.
    pub open spec fn atoms_upto(&self, i: int, k: nat) -> Set<usize>
        decreases k,
    {
        if k == 0 {
            Set::empty()
        } else {
            let s = self.atoms_upto(i, (k - 1) as nat);
            if self.holds_spec((k - 1) as int, i) { s.insert((k - 1) as usize) } else { s }
        }
    }

    pub proof fn lemma_atoms_upto(&self, i: int, k: nat, a: usize)
        requires
            k <= usize::MAX,
        ensures
            self.atoms_upto(i, k).contains(a) == (a < k && self.holds_spec(a as int, i)),
        decreases k,
    {
        if k > 0 {
            self.lemma_atoms_upto(i, (k - 1) as nat, a);
        }
    }
}

impl AtomRead for BitTrace {
    open spec fn view_trace(&self) -> Seq<Set<usize>> {
        Seq::new(self.len as nat, |i: int| self.atoms_upto(i, self.rows@.len()))
    }

    open spec fn inv(&self) -> bool {
        &&& self.rows@.len() <= usize::MAX
        &&& forall|a: int| 0 <= a < self.rows@.len() ==> #[trigger] self.rows@[a]@.len() == words_for(self.len as nat)
    }

    fn len(&self) -> (n: usize) {
        self.len
    }

    fn push_row(&self, atom: usize, h: usize, w: &mut Vec<bool>) {
        let ghost w0 = w@;
        if atom >= self.rows.len() {
            let mut i = 0;
            while i < h
                invariant
                    i <= h, h <= self.len, atom >= self.rows@.len(), self.rows@.len() <= usize::MAX,
                    w@ == w0 + Seq::new(i as nat, |m: int| self.view_trace()[m].contains(atom)),
                decreases h - i,
            {
                proof {
                    self.lemma_atoms_upto(i as int, self.rows@.len(), atom);
                    assert(self.view_trace()[i as int] == self.atoms_upto(i as int, self.rows@.len()));
                    assert(!self.view_trace()[i as int].contains(atom));
                }
                w.push(false);
                i = i + 1;
                assert(w@ =~= w0 + Seq::new(i as nat, |m: int| self.view_trace()[m].contains(atom)));
            }
        } else {
            let row = &self.rows[atom];
            proof { assert(row@.len() == words_for(self.len as nat)); }
            let mut i: usize = 0;
            let mut wi: usize = 0;
            while i < h
                invariant
                    i <= h, h <= self.len, atom < self.rows@.len(), row == &self.rows@[atom as int],
                    row@.len() == words_for(self.len as nat), i == h || i == 64 * wi,
                    self.rows@.len() <= usize::MAX,
                    w@ == w0 + Seq::new(i as nat, |m: int| self.view_trace()[m].contains(atom)),
                decreases h - i,
            {
                proof { assert(wi < row@.len()) by (nonlinear_arith) requires i == 64 * wi, i < h, h <= self.len, row@.len() == (self.len + 63) / 64; }
                let word = row[wi];
                let n = if h - i < 64 { h - i } else { 64 };
                let mut k: usize = 0;
                while k < n
                    invariant
                        k <= n, n <= 64, i + n <= h, h <= self.len, i == 64 * wi, wi < row@.len(),
                        atom < self.rows@.len(), row == &self.rows@[atom as int], word == row@[wi as int],
                        self.rows@.len() <= usize::MAX,
                        w@ == w0 + Seq::new((i + k) as nat, |m: int| self.view_trace()[m].contains(atom)),
                    decreases n - k,
                {
                    let b = (word >> (k as u64)) & 1u64 == 1u64;
                    proof {
                        let step = (i + k) as int;
                        assert(step / 64 == wi as int && step % 64 == k as int) by (nonlinear_arith)
                            requires step == 64 * wi + k, k < 64;
                        self.lemma_atoms_upto(step, self.rows@.len(), atom);
                        assert(self.view_trace()[step] == self.atoms_upto(step, self.rows@.len()));
                        assert(self.holds_spec(atom as int, step) == bit(word, k as u64));
                        assert(b == bit(word, k as u64));
                        assert(b == self.view_trace()[step].contains(atom));
                    }
                    w.push(b);
                    k = k + 1;
                    assert(w@ =~= w0 + Seq::new((i + k) as nat, |m: int| self.view_trace()[m].contains(atom)));
                }
                i = i + n;
                wi = wi + 1;
            }
            assert(w@ =~= w0 + Seq::new(h as nat, |m: int| self.view_trace()[m].contains(atom)));
        }
    }
}

proof fn lemma_set_bit(w: u64, k: u64, j: u64)
    requires
        k < 64,
        j < 64,
    ensures
        bit(w | (1u64 << k), j) == (j == k || bit(w, j)),
{
    assert(((w | (1u64 << k)) >> j) & 1u64 == 1u64 <==> (j == k || (w >> j) & 1u64 == 1u64)) by (bit_vector)
        requires k < 64u64, j < 64u64;
}

proof fn lemma_zero_bit(j: u64)
    requires
        j < 64,
    ensures
        !bit(0u64, j),
{
    assert((0u64 >> j) & 1u64 != 1u64) by (bit_vector) requires j < 64u64;
}

impl BitTrace {
    /// Convert a set-per-step trace whose atoms are all below `num_atoms`.
    pub fn from_sets(t: &Trace, num_atoms: usize) -> (r: BitTrace)
        requires
            forall|i: int, a: usize| 0 <= i < t@.len() && (#[trigger] t@[i]@.contains(a)) ==> a < num_atoms,
        ensures
            r.inv(),
            r.view_trace() == trace_view(t@),
    {
        let n = t.len();
        let nw = n / 64 + if n % 64 == 0 { 0 } else { 1 };
        proof { assert(nw == words_for(n as nat)) by (nonlinear_arith) requires nw == n / 64 + if n % 64 == 0 { 0nat } else { 1nat }; }
        let mut rows: Vec<Vec<u64>> = Vec::new();
        let mut a: usize = 0;
        while a < num_atoms
            invariant
                a <= num_atoms, n == t@.len(), nw == words_for(n as nat), rows@.len() == a,
                forall|b: int| 0 <= b < a ==> (#[trigger] rows@[b])@.len() == nw,
                forall|b: usize, i: int| b < a && 0 <= i < n ==>
                    bit(rows@[b as int]@[i / 64], (i % 64) as u64) == #[trigger] t@[i]@.contains(b),
            decreases num_atoms - a,
        {
            let mut row: Vec<u64> = Vec::new();
            let mut z = 0;
            while z < nw
                invariant z <= nw, row@.len() == z, forall|j: int| 0 <= j < z ==> row@[j] == 0u64,
                decreases nw - z,
            {
                row.push(0u64);
                z = z + 1;
            }
            proof {
                assert forall|j: int| 0 <= j < 64 * nw implies !#[trigger] bit(row@[j / 64], (j % 64) as u64) by {
                    assert(0 <= j / 64 < nw && 0 <= j % 64 < 64) by (nonlinear_arith) requires 0 <= j < 64 * nw;
                    lemma_zero_bit((j % 64) as u64);
                }
            }
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n, n == t@.len(), nw == words_for(n as nat), row@.len() == nw,
                    forall|j: int| 0 <= j < i ==> bit(row@[j / 64], (j % 64) as u64) == #[trigger] t@[j]@.contains(a),
                    forall|j: int| i <= j < 64 * nw ==> !#[trigger] bit(row@[j / 64], (j % 64) as u64),
                decreases n - i,
            {
                proof {
                    assert(i / 64 < nw) by (nonlinear_arith) requires i < n, nw == (n + 63) / 64;
                }
                if t[i].contains(&a) {
                    let wi = i / 64;
                    let k = (i % 64) as u64;
                    let ghost old_row = row@;
                    let nwd = row[wi] | (1u64 << k);
                    row.set(wi, nwd);
                    proof {
                        assert forall|j: int| 0 <= j < 64 * nw implies
                            #[trigger] bit(row@[j / 64], (j % 64) as u64)
                            == (j == i || bit(old_row[j / 64], (j % 64) as u64)) by {
                            assert(0 <= j / 64 < nw && 0 <= j % 64 < 64) by (nonlinear_arith) requires 0 <= j < 64 * nw;
                            if j / 64 == wi as int {
                                lemma_set_bit(old_row[wi as int], k, (j % 64) as u64);
                                assert((j % 64 == k as int) == (j == i)) by (nonlinear_arith)
                                    requires j / 64 == i / 64, k as int == i % 64, 0 <= j, 0 <= i;
                            } else {
                                assert(j != i);
                            }
                        }
                    }
                } else {
                    proof {
                        assert(i < 64 * nw) by (nonlinear_arith) requires i < n, nw == (n + 63) / 64;
                    }
                }
                i = i + 1;
            }
            let ghost row_snapshot = row@;
            let ghost rows_before = rows@;
            rows.push(row);
            proof {
                assert(rows@[a as int]@ == row_snapshot);
                assert forall|b: usize, i: int| b < a + 1 && 0 <= i < n implies
                    bit(rows@[b as int]@[i / 64], (i % 64) as u64) == #[trigger] t@[i]@.contains(b) by {
                    if b < a {
                        assert(rows@[b as int] == rows_before[b as int]);
                    }
                }
            }
            a = a + 1;
        }
        let r = BitTrace { len: n, rows };
        proof {
            assert forall|i: int| 0 <= i < n implies #[trigger] r.view_trace()[i] == trace_view(t@)[i] by {
                assert forall|x: usize| r.view_trace()[i].contains(x) == trace_view(t@)[i].contains(x) by {
                    r.lemma_atoms_upto(i, r.rows@.len(), x);
                    assert(trace_view(t@)[i] == t@[i]@);
                    if x < num_atoms {
                        assert(bit(r.rows@[x as int]@[i / 64], (i % 64) as u64) == t@[i]@.contains(x));
                    } else {
                        assert(!t@[i]@.contains(x));
                    }
                }
                assert(r.view_trace()[i] =~= trace_view(t@)[i]);
            }
            assert(r.view_trace() =~= trace_view(t@));
        }
        r
    }
}

} // verus!
