//! UNVERIFIED PROTOTYPE (T10.4): the bottom-up algorithm of `bottom_up.rs`,
//! written once in plain Rust and made generic over how atoms are read from
//! the trace, so that trace representations can be compared with everything
//! else held fixed. Once a representation is chosen it gets proved; until
//! then this module is outside the verifier and must not be relied on.
use std::collections::HashSet;
use mltl_core::mltl::Mltl;

/// Read access to a trace: its length and "does atom `a` hold at step `i`?".
pub trait AtomRead {
    fn len(&self) -> usize;
    fn holds(&self, atom: usize, step: usize) -> bool;
    /// Append "does `atom` hold at step i" for i in 0..h to `w`.
    fn push_row(&self, atom: usize, h: usize, w: &mut Vec<bool>) {
        for i in 0..h {
            w.push(self.holds(atom, i));
        }
    }
}

/// Current representation: one hash set of true atoms per step.
impl AtomRead for [HashSet<usize>] {
    fn len(&self) -> usize { <[HashSet<usize>]>::len(self) }
    fn holds(&self, atom: usize, step: usize) -> bool { self[step].contains(&atom) }
}

/// Proposed representation: one row of bits per atom; bit `i` of row `a`
/// says whether atom `a` holds at step `i`.
pub struct BitTrace {
    len: usize,
    rows: Vec<Vec<u64>>,
}

impl BitTrace {
    /// Built once per trace.
    pub fn from_sets(t: &[HashSet<usize>]) -> BitTrace {
        let atoms = t.iter().flat_map(|s| s.iter().copied()).max().map_or(0, |m| m + 1);
        let words = (t.len() + 63) / 64;
        let mut rows = vec![vec![0u64; words]; atoms];
        for (i, s) in t.iter().enumerate() {
            for &a in s {
                rows[a][i >> 6] |= 1u64 << (i & 63);
            }
        }
        BitTrace { len: t.len(), rows }
    }
}

impl AtomRead for BitTrace {
    fn len(&self) -> usize { self.len }
    fn push_row(&self, atom: usize, h: usize, w: &mut Vec<bool>) {
        match self.rows.get(atom) {
            None => w.resize(w.len() + h, false),
            Some(row) => {
                let mut i = 0;
                for &word in row {
                    if i >= h { break; }
                    let n = (h - i).min(64);
                    for k in 0..n {
                        w.push((word >> k) & 1 == 1);
                    }
                    i += n;
                }
            }
        }
    }
    #[inline]
    fn holds(&self, atom: usize, step: usize) -> bool {
        match self.rows.get(atom) {
            Some(row) => (row[step >> 6] >> (step & 63)) & 1 == 1,
            None => false,
        }
    }
}

/// Alternative layout: one 64-bit mask per step (bit `a` = atom `a`), for
/// traces with at most 64 atoms.
pub struct StepMasks {
    masks: Vec<u64>,
}

impl StepMasks {
    pub fn from_sets(t: &[HashSet<usize>]) -> StepMasks {
        let masks = t.iter().map(|s| s.iter().fold(0u64, |m, &a| { assert!(a < 64, "StepMasks: atom >= 64"); m | (1u64 << a) })).collect();
        StepMasks { masks }
    }
}

impl AtomRead for StepMasks {
    fn len(&self) -> usize { self.masks.len() }
    #[inline]
    fn holds(&self, atom: usize, step: usize) -> bool {
        atom < 64 && (self.masks[step] >> atom) & 1 == 1
    }
}

pub fn eval_bottom_up<T: AtomRead + ?Sized>(f: &Mltl<usize>, t: &T) -> bool {
    let h = if t.len() == 0 { 0 } else { 1 };
    table(f, t, h)[0]
}

fn child_horizon(h: usize, b: usize, len: usize) -> usize {
    if h == 0 { 0 } else if b > len - h { len } else { h + b }
}

fn window_end(i: usize, b: usize, len: usize) -> usize {
    if b > len - i { len } else { i + b }
}

/// nt[j] = first index >= j where w equals `want`, or w.len() if none.
fn next(w: &[bool], want: bool) -> Vec<usize> {
    let n = w.len();
    let mut nt = vec![n; n];
    for j in (0..n).rev() {
        nt[j] = if w[j] == want { j } else if j + 1 < n { nt[j + 1] } else { n };
    }
    nt
}

/// Table for `f` on steps 0..h, plus the empty-suffix value in slot h.
fn table<T: AtomRead + ?Sized>(f: &Mltl<usize>, t: &T, h: usize) -> Vec<bool> {
    let len = t.len();
    let mut w = Vec::with_capacity(h + 1);
    match f {
        Mltl::True => w.resize(h + 1, true),
        Mltl::False => w.resize(h + 1, false),
        Mltl::Prop(q) => {
            t.push_row(*q, h, &mut w);
            w.push(false);
        }
        Mltl::Not(g) => {
            let wg = table(g, t, h);
            w.extend(wg.iter().map(|x| !x));
        }
        Mltl::And(g1, g2) => {
            let (w1, w2) = (table(g1, t, h), table(g2, t, h));
            w.extend(w1.iter().zip(&w2).map(|(x, y)| *x && *y));
        }
        Mltl::Or(g1, g2) => {
            let (w1, w2) = (table(g1, t, h), table(g2, t, h));
            w.extend(w1.iter().zip(&w2).map(|(x, y)| *x || *y));
        }
        Mltl::Future(a, b, g) => {
            let (a, b) = (*a, *b);
            let wg = table(g, t, child_horizon(h, b, len));
            let nt = next(&wg, true);
            for i in 0..h {
                let rem = len - i;
                w.push(a <= b && rem > a && nt[i + a] <= window_end(i, b, len));
            }
            w.push(false);
        }
        Mltl::Global(a, b, g) => {
            let (a, b) = (*a, *b);
            let wg = table(g, t, child_horizon(h, b, len));
            let nf = next(&wg, false);
            for i in 0..h {
                let rem = len - i;
                w.push(if a > b { false } else if rem <= a { true } else { nf[i + a] > window_end(i, b, len) });
            }
            w.push(a <= b);
        }
        Mltl::Until(g1, a, b, g2) => {
            let (a, b) = (*a, *b);
            let hc = child_horizon(h, b, len);
            let (w1, w2) = (table(g1, t, hc), table(g2, t, hc));
            let (nf1, nt2) = (next(&w1, false), next(&w2, true));
            for i in 0..h {
                let rem = len - i;
                w.push(if a <= b && rem > a {
                    let s0 = i + a;
                    let p = nt2[s0];
                    p <= window_end(i, b, len) && nf1[s0] >= p
                } else {
                    false
                });
            }
            w.push(false);
        }
        Mltl::Release(g1, a, b, g2) => {
            let (a, b) = (*a, *b);
            let hc = child_horizon(h, b, len);
            let (w1, w2) = (table(g1, t, hc), table(g2, t, hc));
            let (nt1, nf2) = (next(&w1, true), next(&w2, false));
            let bm1 = if b == 0 { 0 } else { b - 1 };
            for i in 0..h {
                let rem = len - i;
                w.push(if a > b {
                    false
                } else if rem <= a {
                    true
                } else {
                    let s0 = i + a;
                    let (e, u, q) = (window_end(i, b, len), window_end(i, bm1, len), nf2[s0]);
                    if q > e {
                        true
                    } else if q > s0 {
                        let lim = if u < q - 1 { u } else { q - 1 };
                        lim >= s0 && nt1[s0] <= lim
                    } else {
                        false
                    }
                });
            }
            w.push(a <= b);
        }
    }
    w
}
