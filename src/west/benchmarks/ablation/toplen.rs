//! Ablation variant of `../proto.rs`: every regex carries the top-level
//! formula's full length from the leaves up, and shifting keeps the length
//! fixed, as upstream WEST does. Everything else is unchanged.
use mltl_core::mltl::Mltl;

const LO: u64 = 0x5555_5555_5555_5555;

#[derive(Clone)]
pub struct Regex {
    pub n: usize,
    pub len: usize,
    pub w: usize,
    pub data: Vec<u64>, // count * w words
}

fn words_for(n: usize, len: usize) -> usize { (2 * n * len + 63) / 64 }

impl Regex {
    pub fn count(&self) -> usize { if self.w == 0 { 0 } else { self.data.len() / self.w } }
    fn empty(n: usize, len: usize) -> Regex { Regex { n, len, w: words_for(n, len), data: Vec::new() } }
    fn trace(&self, i: usize) -> &[u64] { &self.data[i * self.w..(i + 1) * self.w] }

    /// One trace of length 1 with `bit` (0b01 / 0b10 / 0b11) at atom `p`.
    fn single(n: usize, cl: usize, p: Option<(usize, u64)>) -> Regex {
        let w = words_for(n, cl);
        let mut t = vec![!0u64; w];
        if let Some((p, bits)) = p {
            let q = 2 * p;
            t[q / 64] &= !(0b11u64 << (q % 64));
            t[q / 64] |= bits << (q % 64);
        }
        Regex { n, len: cl, w, data: t }
    }

    /// Pad every trace with S to `len` steps.
    fn pad(&self, len: usize) -> Regex {
        if len == self.len { return self.clone(); }
        let w2 = words_for(self.n, len);
        let mut data = Vec::with_capacity(self.count() * w2);
        for i in 0..self.count() {
            data.extend_from_slice(self.trace(i));
            data.resize(data.len() + (w2 - self.w), !0u64);
        }
        Regex { n: self.n, len, w: w2, data }
    }

    /// Delay by `k` steps: prepend k all-S states.
    fn shift(&self, k: usize) -> Regex {
        if k == 0 { return self.clone(); }
        let len = self.len;
        let w2 = self.w;
        let s = 2 * self.n * k;
        let (ws, bs) = (s / 64, s % 64);
        let mut data = Vec::with_capacity(self.count() * w2);
        for i in 0..self.count() {
            let src = self.trace(i);
            let get = |j: isize| -> u64 { if j < 0 || j as usize >= src.len() { !0u64 } else { src[j as usize] } };
            let mut t: Vec<u64> = Vec::with_capacity(w2);
            for j in 0..w2 {
                let jj = j as isize - ws as isize;
                let v = if bs == 0 { get(jj) } else { (get(jj) << bs) | (get(jj - 1) >> (64 - bs)) };
                t.push(v);
            }
            // unused tail bits stay 1
            for q in (2 * self.n * len)..(64 * w2) { t[q / 64] |= 1u64 << (q % 64); }
            data.extend_from_slice(&t);
        }
        Regex { n: self.n, len, w: w2, data }
    }

    /// Simplify to a fixpoint: merge any two traces that differ in at most
    /// one atom at one step.
    fn simp(mut self) -> Regex {
        let w = self.w;
        loop {
            let mut changed = false;
            let mut i = 0;
            while i < self.count() {
                let mut j = i + 1;
                while j < self.count() {
                    let (a, b) = (i * w, j * w);
                    let mut diff = 0u32;
                    for k in 0..w {
                        let x = self.data[a + k] ^ self.data[b + k];
                        diff += ((x | (x >> 1)) & LO).count_ones();
                        if diff > 1 { break; }
                    }
                    if diff <= 1 {
                        for k in 0..w { self.data[a + k] |= self.data[b + k]; }
                        // swap_remove trace j
                        let last = self.count() - 1;
                        if j != last {
                            for k in 0..w { self.data[b + k] = self.data[last * w + k]; }
                        }
                        self.data.truncate(last * w);
                        changed = true;
                    } else {
                        j += 1;
                    }
                }
                i += 1;
            }
            if !changed { return self; }
        }
    }

    fn or(self, other: Regex) -> Regex {
        let len = self.len.max(other.len);
        let mut a = self.pad(len);
        let b = other.pad(len);
        a.data.extend_from_slice(&b.data);
        a.simp()
    }

    fn and(&self, other: &Regex) -> Regex {
        let len = self.len.max(other.len);
        let a = self.pad(len);
        let b = other.pad(len);
        let w = a.w;
        let mut out = Regex::empty(self.n, len);
        let mut buf = vec![0u64; w];
        for i in 0..a.count() {
            let x = a.trace(i);
            'pair: for j in 0..b.count() {
                let y = b.trace(j);
                for k in 0..w {
                    let v = x[k] & y[k];
                    if (v | (v >> 1)) & LO != LO { continue 'pair; }
                    buf[k] = v;
                }
                out.data.extend_from_slice(&buf);
            }
        }
        out.simp()
    }
}

fn global(l: &Regex, a: usize, b: usize) -> Regex {
    let mut acc = l.shift(a);
    for k in a + 1..=b { acc = l.shift(k).and(&acc); }
    acc
}

fn future(l: &Regex, a: usize, b: usize) -> Regex {
    let mut acc = l.shift(a);
    for k in a + 1..=b { acc = l.shift(k).or(acc); }
    acc
}

fn until(lp: &Regex, lq: &Regex, a: usize, b: usize) -> Regex {
    let mut acc = lq.shift(a);
    let mut g = lp.shift(a);
    for k in a + 1..=b {
        acc = acc.or(g.and(&lq.shift(k)));
        if k < b { g = lp.shift(k).and(&g); }
    }
    acc
}

fn release(lp: &Regex, lq: &Regex, a: usize, b: usize) -> Regex {
    let g = global(lq, a, b);
    if b == a { return g; }
    let mut gq = lq.shift(a);
    let mut acc = lp.shift(a).and(&gq);
    for k in a + 1..b {
        gq = lq.shift(k).and(&gq);
        acc = acc.or(gq.and(&lp.shift(k)));
    }
    g.or(acc)
}

fn reg_nnf(f: &Mltl<usize>, n: usize, cl: usize) -> Regex {
    match f {
        Mltl::True => Regex::single(n, cl, None),
        Mltl::False => Regex::empty(n, cl),
        Mltl::Prop(p) => Regex::single(n, cl, Some((*p, 0b10))),
        Mltl::Not(g) => match &**g {
            Mltl::Prop(p) => Regex::single(n, cl, Some((*p, 0b01))),
            _ => unreachable!("not in NNF"),
        },
        Mltl::Or(x, y) => reg_nnf(x, n, cl).or(reg_nnf(y, n, cl)),
        Mltl::And(x, y) => reg_nnf(x, n, cl).and(&reg_nnf(y, n, cl)),
        Mltl::Future(a, b, x) => future(&reg_nnf(x, n, cl), *a, *b),
        Mltl::Global(a, b, x) => global(&reg_nnf(x, n, cl), *a, *b),
        Mltl::Until(x, a, b, y) => until(&reg_nnf(x, n, cl), &reg_nnf(y, n, cl), *a, *b),
        Mltl::Release(x, a, b, y) => release(&reg_nnf(x, n, cl), &reg_nnf(y, n, cl), *a, *b),
    }
}

pub fn num_vars(f: &Mltl<usize>) -> usize {
    match f {
        Mltl::True | Mltl::False => 1,
        Mltl::Prop(i) => i + 1,
        Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => num_vars(g),
        Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) => num_vars(g).max(num_vars(h)),
    }
}

pub fn complen(f: &Mltl<usize>) -> usize {
    match f {
        Mltl::True | Mltl::False | Mltl::Prop(_) => 1,
        Mltl::Not(g) => complen(g),
        Mltl::And(g, h) | Mltl::Or(g, h) => complen(g).max(complen(h)),
        Mltl::Future(_, b, g) | Mltl::Global(_, b, g) => b + complen(g),
        Mltl::Until(g, _, b, h) | Mltl::Release(g, _, b, h) => b + (complen(g).saturating_sub(1)).max(complen(h)),
    }
}

/// Fast WEST: regexes of length `complen f` (padded at the end, then
/// simplified once more), `WEST_num_vars f` atoms.
pub fn fast_reg(f: &Mltl<usize>) -> Regex {
    let n = num_vars(f);
    let cl = complen(f);
    let r = reg_nnf(&mltl_core::properties::convert_nnf(f), n, cl);
    r.simp()
}

/// Decode trace `i` as `WestBit` states (for checking against `WEST_reg`).
pub fn decode(r: &Regex, i: usize) -> Vec<Vec<u8>> {
    let t = r.trace(i);
    (0..r.len).map(|s| (0..r.n).map(|v| {
        let q = 2 * (r.n * s + v);
        ((t[q / 64] >> (q % 64)) & 0b11) as u8
    }).collect()).collect()
}
