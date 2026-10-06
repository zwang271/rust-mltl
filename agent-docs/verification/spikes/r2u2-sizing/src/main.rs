// Throwaway spike (2026-10-05). Not part of the workspace, not verified.
//
// Simulates the R2U2 model of src/r2u2 (history engine: engine.rs,
// operators.rs; ring: ring.rs, ring_engine.rs) and measures, per queue, the
// smallest ring size that keeps every read equal to the unbounded read.
//
// Exact per-read rule (derived from ring_abs + ring_scan, checked by the
// `check` mode): reader pointer at logical entry j, child has `len`
// compacted entries, needed entry k (first with time >= tau). A ring of N
// slots returns the right entry for every N iff k is absent or k == len-1;
// otherwise exactly when N >= len - j (for N < len - j the pointer slot holds
// an entry later than k, or sizes that happen to align, which we ignore:
// we want the threshold above which every size works).
use std::io::Write;

#[derive(Clone, Copy, PartialEq, Debug)]
enum K { P(usize), T, F, Not, And, U(u64, u64) }

const NONE: usize = usize::MAX;

#[derive(Clone)]
struct Node { k: K, l: usize, r: usize }

#[derive(Clone)]
struct Formula { n: Vec<Node>, root: usize, wpd: Vec<u64>, bpd: Vec<u64>, parent: Vec<usize>, side: Vec<usize> }

impl Formula {
    fn finish(n: Vec<Node>) -> Formula {
        let m = n.len();
        let mut wpd = vec![0; m]; let mut bpd = vec![0; m];
        let mut parent = vec![NONE; m]; let mut side = vec![0; m];
        for i in 0..m {
            let nd = &n[i];
            match nd.k {
                K::P(_) | K::T | K::F => {}
                K::Not => { wpd[i] = wpd[nd.l]; bpd[i] = bpd[nd.l]; parent[nd.l] = i; side[nd.l] = 0; }
                K::And => {
                    wpd[i] = wpd[nd.l].max(wpd[nd.r]); bpd[i] = bpd[nd.l].min(bpd[nd.r]);
                    parent[nd.l] = i; side[nd.l] = 0; parent[nd.r] = i; side[nd.r] = 1;
                }
                K::U(a, b) => {
                    wpd[i] = b + wpd[nd.l].max(wpd[nd.r]); bpd[i] = a + bpd[nd.l].min(bpd[nd.r]);
                    parent[nd.l] = i; side[nd.l] = 0; parent[nd.r] = i; side[nd.r] = 1;
                }
            }
        }
        Formula { root: m - 1, n, wpd, bpd, parent, side }
    }
    fn show(&self, i: usize) -> String {
        let nd = &self.n[i];
        match nd.k {
            K::P(a) => format!("p{}", a), K::T => "true".into(), K::F => "false".into(),
            K::Not => format!("!({})", self.show(nd.l)),
            K::And => format!("({} & {})", self.show(nd.l), self.show(nd.r)),
            K::U(a, b) => format!("({} U[{},{}] {})", self.show(nd.l), a, b, self.show(nd.r)),
        }
    }
    fn prefix(&self, i: usize) -> String {
        let nd = &self.n[i];
        match nd.k {
            K::P(a) => format!("p{}", a), K::T => "T".into(), K::F => "F".into(),
            K::Not => format!("! {}", self.prefix(nd.l)),
            K::And => format!("& {} {}", self.prefix(nd.l), self.prefix(nd.r)),
            K::U(a, b) => format!("U {} {} {} {}", a, b, self.prefix(nd.l), self.prefix(nd.r)),
        }
    }
    fn sibling(&self, c: usize) -> usize {
        let p = self.parent[c];
        if p == NONE { return NONE; }
        let nd = &self.n[p];
        match nd.k { K::Not => NONE, _ => if nd.l == c { nd.r } else { nd.l } }
    }
    /// C2PO `compute_scq_sizes` (= Isabelle queue_size_sibling_nodes).
    fn c2po(&self, c: usize) -> u64 {
        let s = self.sibling(c);
        let sw = if s == NONE { 0 } else { self.wpd[s] };
        sw.saturating_sub(self.bpd[c]) + 1
    }
    /// Ours (ring_engine.rs : child_slots; NOT child 1).
    fn ours(&self, c: usize) -> u64 {
        let p = self.parent[c];
        if p == NONE { return 1; }
        let nd = &self.n[p];
        match nd.k {
            K::Not => 1,
            _ => self.wpd[nd.l].max(self.wpd[nd.r]).saturating_sub(self.bpd[c]) + 1,
        }
    }
}

/// Candidate size rules. x = ours - 1, y = c2po - 1 (binary parents).
fn rule_size(f: &Formula, c: usize, rule: &str) -> u64 {
    let p = f.parent[c];
    if p == NONE { return 1; }
    if let K::Not = f.n[p].k { return 1; }
    let x = f.ours(c) - 1; let y = f.c2po(c) - 1;
    match rule {
        "ours" => x + 1,
        "c2po" => y + 1,
        "half" => y + (x - y + 1) / 2 + 1,
        "half_floor" => y + (x - y) / 2 + 1,
        "third" => y + (x - y + 2) / 3 + 1,
        _ => panic!("rule"),
    }
}

impl Formula {
    /// Proved upper bound on need (ours).
    fn need_upper(&self, c: usize) -> u64 { self.ours(c) }
}

fn parse_prefix(toks: &mut std::slice::Iter<&str>, out: &mut Vec<Node>) -> usize {
    let t = *toks.next().unwrap();
    let k = match t {
        "!" => { let l = parse_prefix(toks, out); out.push(Node { k: K::Not, l, r: NONE }); return out.len() - 1; }
        "&" => { let l = parse_prefix(toks, out); let r = parse_prefix(toks, out); out.push(Node { k: K::And, l, r }); return out.len() - 1; }
        "U" => {
            let a: u64 = toks.next().unwrap().parse().unwrap(); let b: u64 = toks.next().unwrap().parse().unwrap();
            let l = parse_prefix(toks, out); let r = parse_prefix(toks, out);
            out.push(Node { k: K::U(a, b), l, r }); return out.len() - 1;
        }
        "T" => K::T, "F" => K::F,
        _ => K::P(t[1..].parse().unwrap()),
    };
    out.push(Node { k, l: NONE, r: NONE }); out.len() - 1
}

// ---------------------------------------------------------------------------
// RNG
// ---------------------------------------------------------------------------
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
    fn f(&mut self) -> f64 { (self.next() >> 11) as f64 / (1u64 << 53) as f64 }
}

fn gen(rng: &mut Rng, d: u32, maxb: u64, natoms: usize, out: &mut Vec<Node>) -> usize {
    if d == 0 || rng.f() < 0.15 {
        out.push(Node { k: K::P(rng.below(natoms as u64) as usize), l: NONE, r: NONE });
        return out.len() - 1;
    }
    match rng.below(6) {
        0 => { let l = gen(rng, d - 1, maxb, natoms, out); out.push(Node { k: K::Not, l, r: NONE }); }
        1 => { let l = gen(rng, d - 1, maxb, natoms, out); let r = gen(rng, d - 1, maxb, natoms, out); out.push(Node { k: K::And, l, r }); }
        _ => {
            let a = rng.below(maxb + 1); let b = a + rng.below(maxb + 1);
            let l = gen(rng, d - 1, maxb, natoms, out); let r = gen(rng, d - 1, maxb, natoms, out);
            out.push(Node { k: K::U(a, b), l, r });
        }
    }
    out.len() - 1
}

/// Give every leaf its own atom (true/false leaves stay); returns the atom count.
fn distinct_atoms(v: &mut Vec<Node>) -> usize {
    let mut n = 0;
    for nd in v.iter_mut() { if let K::P(_) = nd.k { nd.k = K::P(n); n += 1; } }
    n.max(1)
}

fn gen_trace(rng: &mut Rng, natoms: usize, len: usize) -> Vec<Vec<bool>> {
    let mode = rng.below(5);
    let mut tr = vec![vec![false; natoms]; len];
    for a in 0..natoms {
        match mode {
            0 => { let p = [0.1, 0.3, 0.5, 0.7, 0.9][rng.below(5) as usize]; for t in 0..len { tr[t][a] = rng.f() < p; } }
            1 => { let per = 1 + rng.below(6) as usize; let ph = rng.below(per as u64) as usize; for t in 0..len { tr[t][a] = ((t + ph) / per) % 2 == 0; } }
            2 => { // Markov bursts
                let stay = [0.5, 0.8, 0.95][rng.below(3) as usize]; let mut v = rng.f() < 0.5;
                for t in 0..len { if rng.f() > stay { v = !v; } tr[t][a] = v; }
            }
            3 => { for t in 0..len { tr[t][a] = (t + a) % 2 == 0; } }
            _ => { let p = rng.f(); for t in 0..len { tr[t][a] = rng.f() < p; } }
        }
    }
    tr
}

// ---------------------------------------------------------------------------
// Engine
// ---------------------------------------------------------------------------
#[derive(Clone)]
struct Ring { slots: Vec<Option<(bool, u64)>>, w: usize }
impl Ring {
    fn new(n: usize) -> Ring { Ring { slots: vec![None; n], w: 0 } }
    fn write(&mut self, v: (bool, u64)) { // ring.rs : ring_write
        let n = self.slots.len(); let prev = if self.w == 0 { n - 1 } else { self.w - 1 };
        let same = matches!(self.slots[prev], Some(pv) if pv.0 == v.0);
        if same { self.slots[prev] = Some(v); } else { self.slots[self.w] = Some(v); self.w = (self.w + 1) % n; }
    }
    fn read(&self, mut rd: usize, tau: u64) -> (Option<(bool, u64)>, usize) { // ring.rs : ring_scan
        let n = self.slots.len();
        for _ in 0..n {
            if self.slots[rd].is_none() && rd == 0 { return (None, rd); }
            if let Some(v) = self.slots[rd] { if v.1 >= tau { return (Some(v), rd); } }
            if (rd + 1) % n == self.w { return (None, rd); }
            rd = (rd + 1) % n;
        }
        (None, rd)
    }
}

#[derive(Clone, Copy, Default, Debug)]
struct Witness { burst_now: u64, step: u64, pass: u32, tau: u64, len: usize, j: usize, k: usize, cov_c: u64, cov_s: u64, cov_p: u64, nt_ok: bool }

struct St<'a> {
    f: &'a Formula,
    times: Vec<Vec<u64>>, vals: Vec<Vec<bool>>,
    nt: Vec<u64>, prev: Vec<Option<u64>>,
    ptr: Vec<usize>,          // per child node: logical read pointer of its reader
    need: Vec<u64>,           // per child node
    wit: Vec<Witness>,
    rings: Option<Vec<Ring>>, rd: Vec<usize>, mism: Vec<u64>,
    root_out: Vec<(bool, u64)>,
    step: u64, pass: u32,
    pushed: Vec<u64>, burst: Vec<u64>,
    log: Option<(usize, usize)>,
    psi: Vec<i64>, // max over reads of potential - (x + y)
}

impl<'a> St<'a> {
    fn new(f: &'a Formula, sizes: Option<&[u64]>) -> St<'a> {
        let m = f.n.len();
        let nt = (0..m).map(|i| match f.n[i].k { K::U(a, _) => a, _ => 0 }).collect();
        St {
            f, times: vec![vec![]; m], vals: vec![vec![]; m], nt, prev: vec![None; m],
            ptr: vec![0; m], need: vec![1; m], wit: vec![Witness::default(); m],
            rings: sizes.map(|s| s.iter().map(|&n| Ring::new(n as usize)).collect()), rd: vec![0; m], mism: vec![0; m],
            root_out: vec![], step: 0, pass: 0, pushed: vec![0; m], burst: vec![0; m], log: None, psi: vec![i64::MIN; m],
        }
    }
    fn psi_of(&self, p: usize, c: usize, b: u64) -> (i64, bool) {
        let tau = self.nt[p]; let ti = &self.times[c]; let len = ti.len();
        let k = ti.partition_point(|&t| t < tau);
        let cap = b.saturating_sub(self.f.bpd[c]) as i64;
        let mut w: i64 = 0;
        if k < len { w += ti[k] as i64 + 1 - tau as i64; for i in k + 1..len { w += ((ti[i] - ti[i - 1]) as i64).max(2); } }
        let h = (cap - (self.cov(c) as i64).max(tau as i64)).max(0);
        (w + h, k >= len)
    }
    /// Check the invariant before a pass (b = n + 1): psi <= x + y + [E = 0] for edges with x > y.
    fn check_inv(&mut self, b: u64, tag: &str) {
        for c in 0..self.f.n.len() {
            let p = self.f.parent[c]; if p == NONE || matches!(self.f.n[p].k, K::Not) { continue; }
            let x = self.f.ours(c) as i64 - 1; let y = self.f.c2po(c) as i64 - 1;
            if x <= y { continue; }
            let (ps, e0) = self.psi_of(p, c, b);
            let bound = x + y + if e0 { 1 } else { 0 };
            if ps > bound { INVFAIL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if INVFAIL.load(std::sync::atomic::Ordering::Relaxed) < 4 { eprintln!("INV FAIL {} step {} pass {} {} child {} psi {} bound {}", tag, self.step, self.pass, self.f.show(self.f.root), self.f.show(c), ps, bound); } }
            INVCHK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    }
    fn cov(&self, i: usize) -> u64 { self.times[i].last().map_or(0, |t| t + 1) }
    fn write(&mut self, i: usize, v: bool, t: u64) {
        assert!(t >= self.cov(i));
        if self.vals[i].last() == Some(&v) { *self.times[i].last_mut().unwrap() = t; }
        else { self.times[i].push(t); self.vals[i].push(v); self.pushed[i] += 1; if self.pushed[i] > self.burst[i] { self.burst[i] = self.pushed[i]; } }
        if let Some(r) = self.rings.as_mut() { r[i].write((v, t)); }
        if i == self.f.root { self.root_out.push((v, t)); }
    }
    /// Reader `p` reads child `c` at its next_time.
    fn read(&mut self, p: usize, c: usize) -> Option<(bool, u64)> {
        let tau = self.nt[p];
        let j0 = self.ptr[c];
        let len = self.times[c].len();
        let k = self.times[c].partition_point(|&t| t < tau);
        let hist = if k < len { Some((self.vals[c][k], self.times[c][k])) } else { None };
        // potential probe: W + H_eff - (x + y)
        if let Some(pk) = Some(self.f.n[p].k) { if !matches!(pk, K::Not) {
            let cap = (self.step + 1).saturating_sub(self.f.bpd[c]) as i64;
            let cov = self.cov(c) as i64; let ti = &self.times[c];
            let mut wsum: i64 = 0;
            if k < len {
                wsum += ti[k] as i64 + 1 - tau as i64;
                for i in k + 1..len { wsum += ((ti[i] - ti[i - 1]) as i64).max(2); }
            }
            let heff = cap - cov.max(tau as i64);
            let x = self.f.ours(c) as i64 - 1; let y = self.f.c2po(c) as i64 - 1;
            let v = wsum + heff - x - y;
            if v > self.psi[c] { self.psi[c] = v; }
        } }
        // need tracking (exact while all reads so far are right)
        if len > 0 {
            let j = self.ptr[c];
            if k < len {
                assert!(k >= j, "needed entry before pointer");
                if k + 1 < len {
                    let nd = (len - j) as u64;
                    if nd > self.need[c] {
                        self.need[c] = nd;
                        let s = self.f.sibling(c);
                        let cov_s = if s == NONE { 0 } else { self.cov(s) };
                        self.wit[c] = Witness { burst_now: self.pushed[c], step: self.step, pass: self.pass, tau, len, j, k,
                            cov_c: self.cov(c), cov_s, cov_p: self.cov(p), nt_ok: true };
                    }
                }
                self.ptr[c] = k;
            } else {
                self.ptr[c] = len - 1;
            }
        }
        if let Some((lp, lc)) = self.log { if lp == p {
            let s = self.f.sibling(c);
            println!("  step {:3} pass {:2} reader nt {:3} P {:3} | read {} = {:?} | child len {:3} ptr-before {:3} k {:3} cov {:3} need-now {:2} {}",
                self.step, self.pass, tau, self.cov(p), if c == lc { "C" } else { "S" }, hist, len, j0, k,
                self.cov(c), if k < len && k + 1 < len { len - j0 } else { 1 }, if s != NONE { format!("sib cov {}", self.cov(s)) } else { String::new() });
        } }
        if let Some(rings) = self.rings.as_ref() {
            let (d, rd2) = rings[c].read(self.rd[c], tau);
            self.rd[c] = rd2;
            if d != hist { self.mism[c] += 1; }
            return d;
        }
        hist
    }
    fn pass(&mut self, state: &[bool], n: u64, first: bool) -> bool {
        let mut prog = false;
        for i in 0..self.f.n.len() {
            let Node { k, l, r } = self.f.n[i].clone();
            match k {
                K::P(a) => if first { self.write(i, state[a], n); prog = true; },
                K::T => if first { self.write(i, true, n); prog = true; },
                K::F => if first { self.write(i, false, n); prog = true; },
                K::Not => {
                    if let Some((v, t)) = self.read(i, l) { self.write(i, !v, t); self.nt[i] = t + 1; prog = true; }
                }
                K::And => {
                    let ld = self.read(i, l); let rd = self.read(i, r);
                    let v = match (ld, rd) {
                        (Some(a), Some(b)) => Some(if a.0 && b.0 { (true, a.1.min(b.1)) } else if !a.0 && !b.0 { (false, a.1.max(b.1)) }
                                               else if a.0 { (false, b.1) } else { (false, a.1) }),
                        (Some(a), None) => if !a.0 { Some((false, a.1)) } else { None },
                        (None, Some(b)) => if !b.0 { Some((false, b.1)) } else { None },
                        (None, None) => None,
                    };
                    if let Some((v, t)) = v { self.write(i, v, t); self.nt[i] = t + 1; prog = true; }
                }
                K::U(lb, ub) => {
                    let ld = self.read(i, l); let rd = self.read(i, r);
                    let ef = match self.prev[i] { None => ub, Some(p) => p + ub + 1 };
                    if let Some((rv, rt)) = rd {
                        if rv {
                            let t = rt - lb; self.write(i, true, t); self.nt[i] = rt + 1; self.prev[i] = Some(t); prog = true;
                        } else if let Some((lv, lt)) = ld {
                            let tm = lt.min(rt);
                            if !lv {
                                let t = tm - lb; self.write(i, false, t); self.nt[i] = tm + 1; self.prev[i] = Some(t); prog = true;
                            } else if rt >= ef {
                                let t = rt - ub; self.write(i, false, t); self.nt[i] = (tm + 1).max(t + lb + 1); self.prev[i] = Some(t); prog = true;
                            } else {
                                self.nt[i] = tm + 1;
                                if ideal() { prog = true; }
                            }
                        } else if rt >= ef {
                            let t = rt - ub; self.write(i, false, t); self.nt[i] = self.nt[i].max(t + lb + 1); self.prev[i] = Some(t); prog = true;
                        }
                    }
                }
            }
        }
        prog
    }
    fn step(&mut self, state: &[bool], n: u64) {
        self.step = n; self.pass = 0;
        for x in self.pushed.iter_mut() { *x = 0; }
        if checking() { self.check_inv(n + 1, "pre-step"); }
        self.pass(state, n, true);
        loop {
            self.pass += 1;
            assert!(self.pass < 100000);
            if checking() { self.check_inv(n + 1, "pre-pass"); }
            if !self.pass(state, n, false) { break; }
        }
        if checking() { self.check_inv(n + 2, "post-step"); }
    }
    fn run(&mut self, tr: &[Vec<bool>]) { for (n, s) in tr.iter().enumerate() { self.step(s, n as u64); } }
}

/// Per-step root values (verdict (v,t) covers previous end+1 .. t).
static INVFAIL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static INVCHK: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
fn checking() -> bool { static I: std::sync::OnceLock<bool> = std::sync::OnceLock::new(); *I.get_or_init(|| std::env::var("CHECKINV").is_ok()) }

fn ideal() -> bool { static I: std::sync::OnceLock<bool> = std::sync::OnceLock::new(); *I.get_or_init(|| std::env::var("IDEAL").is_ok()) }

fn per_step(out: &[(bool, u64)]) -> Vec<bool> {
    let mut r = vec![];
    for &(v, t) in out { while (r.len() as u64) <= t { r.push(v); } }
    r
}

fn needs(f: &Formula, tr: &[Vec<bool>]) -> (Vec<u64>, Vec<Witness>, Vec<bool>) {
    let r = needs_b(f, tr); (r.0, r.1, r.2)
}
fn needs_b(f: &Formula, tr: &[Vec<bool>]) -> (Vec<u64>, Vec<Witness>, Vec<bool>, Vec<u64>) {
    let mut s = St::new(f, None); s.run(tr);
    (s.need, s.wit, per_step(&s.root_out), s.burst)
}

/// Ring run with given per-node sizes: (value error at root, coverage short, read mismatches per node).
fn ring_check(f: &Formula, tr: &[Vec<bool>], sizes: &[u64], ref_vals: &[bool]) -> (bool, bool, Vec<u64>) {
    let mut s = St::new(f, Some(sizes)); s.run(tr);
    let v = per_step(&s.root_out);
    let mut wrong = false;
    for (j, &x) in v.iter().enumerate() { if j < ref_vals.len() && ref_vals[j] != x { wrong = true; } }
    (wrong, v.len() < ref_vals.len(), s.mism)
}

fn mutate(rng: &mut Rng, tr: &mut Vec<Vec<bool>>) {
    let len = tr.len(); let na = tr[0].len();
    match rng.below(4) {
        0 => { let t = rng.below(len as u64) as usize; let a = rng.below(na as u64) as usize; tr[t][a] = !tr[t][a]; }
        1 => { let t = rng.below(len as u64) as usize; let w = 1 + rng.below(8) as usize; let a = rng.below(na as u64) as usize;
               let v = rng.f() < 0.5; for x in t..(t + w).min(len) { tr[x][a] = v; } }
        2 => { let t = rng.below(len as u64) as usize; let w = 1 + rng.below(12) as usize; let a = rng.below(na as u64) as usize;
               for x in t..(t + w).min(len) { tr[x][a] = (x - t) % 2 == 0; } }
        _ => { for _ in 0..3 { let t = rng.below(len as u64) as usize; let a = rng.below(na as u64) as usize; tr[t][a] = !tr[t][a]; } }
    }
}

fn json_edges(f: &Formula, best: &[u64], rnd: &[u64], wit: &[Witness], burst: &[u64]) -> String {
    let mut v = vec![];
    for c in 0..f.n.len() {
        let p = f.parent[c]; if p == NONE { continue; }
        let s = f.sibling(c);
        let (pk, a, b) = match f.n[p].k { K::Not => ("!", 0, 0), K::And => ("&", 0, 0), K::U(a, b) => ("U", a, b), _ => unreachable!() };
        let (wpd_s, bpd_s) = if s == NONE { (0, 0) } else { (f.wpd[s], f.bpd[s]) };
        let ck = match f.n[c].k { K::Not => "!", K::And => "&", K::U(..) => "U", _ => "leaf" };
        let w = &wit[c];
        v.push(format!(
            "{{\"c\":{},\"p\":{},\"pk\":\"{}\",\"ck\":\"{}\",\"side\":{},\"a\":{},\"b\":{},\"wpd_c\":{},\"bpd_c\":{},\"wpd_s\":{},\"bpd_s\":{},\"wpd_p\":{},\"bpd_p\":{},\"c2po\":{},\"ours\":{},\"need_rand\":{},\"need\":{},\"burst_c\":{},\"burst_s\":{},\"wit\":[{},{},{},{},{},{},{},{},{},{}]}}",
            c, p, pk, ck, f.side[c], a, b, f.wpd[c], f.bpd[c], wpd_s, bpd_s, f.wpd[p], f.bpd[p], f.c2po(c), f.ours(c), rnd[c], best[c], burst[c], if s == NONE { 0 } else { burst[s] },
            w.burst_now, w.step, w.pass, w.tau, w.len, w.j, w.k, w.cov_c, w.cov_s, w.cov_p));
    }
    v.join(",")
}

fn trace_len(f: &Formula, lmin: usize, lmax: usize) -> usize { ((2 * f.wpd[f.root] + 40) as usize).clamp(lmin, lmax) }

/// One formula: random traces, then hill climbing per edge.
fn study(f: &Formula, rng: &mut Rng, natoms: usize, ntr: usize, nadv: usize, lmin: usize, lmax: usize) -> String {
    let m = f.n.len();
    let len = trace_len(f, lmin, lmax);
    let c2: Vec<u64> = (0..m).map(|c| f.c2po(c)).collect();
    let ours: Vec<u64> = (0..m).map(|c| f.ours(c)).collect();
    let mut best = vec![1u64; m]; let mut wit = vec![Witness::default(); m]; let mut burst = vec![0u64; m];
    let mut c2_val_wrong = 0; let mut c2_read_wrong = 0; let mut c2_short = 0;
    let mut pool: Vec<Vec<Vec<bool>>> = vec![];
    for _ in 0..ntr {
        let tr = gen_trace(rng, natoms, len);
        let (nd, w, vals, bu) = needs_b(f, &tr);
        for c in 0..m { if bu[c] > burst[c] { burst[c] = bu[c]; } }
        let mut any_read = false;
        for c in 0..m { if nd[c] > best[c] { best[c] = nd[c]; wit[c] = w[c]; } if nd[c] > c2[c] && f.parent[c] != NONE { any_read = true; } }
        if any_read {
            c2_read_wrong += 1;
            let (vw, sh, _) = ring_check(f, &tr, &c2, &vals);
            if vw { c2_val_wrong += 1; } if sh { c2_short += 1; }
        }
        pool.push(tr);
    }
    let rnd = best.clone();
    // adversarial: target edges in turn, maximize need[target] (ties: total need)
    let edges: Vec<usize> = (0..m).filter(|&c| f.parent[c] != NONE && ours[c] > 1).collect();
    let mut adv_val_wrong = false;
    if !edges.is_empty() && nadv > 0 {
        let per = (nadv / edges.len()).max(30);
        for &e in &edges {
            if best[e] >= ours[e] { continue; }
            let mut cur = pool[rng.below(pool.len() as u64) as usize].clone();
            let (mut nd, _, _) = needs(f, &cur);
            let mut score = (nd[e], nd.iter().sum::<u64>());
            for _ in 0..per {
                let mut cand = cur.clone();
                let nm = 1 + rng.below(3);
                for _ in 0..nm { mutate(rng, &mut cand); }
                let (nd2, w2, _, bu2) = needs_b(f, &cand);
                for c in 0..m { if bu2[c] > burst[c] { burst[c] = bu2[c]; } }
                for c in 0..m { if nd2[c] > best[c] { best[c] = nd2[c]; wit[c] = w2[c]; } }
                let sc = (nd2[e], nd2.iter().sum::<u64>());
                if sc >= score { score = sc; cur = cand; nd = nd2; }
                if best[e] >= ours[e] { break; }
            }
            let _ = nd;
            // does C2PO give a wrong value on the best trace for this edge?
            let (_, _, vals) = needs(f, &cur);
            if (0..m).any(|c| f.parent[c] != NONE && needs(f, &cur).0[c] > c2[c]) {
                let (vw, _, _) = ring_check(f, &cur, &c2, &vals);
                if vw { adv_val_wrong = true; }
            }
        }
    }
    let tot = |v: &[u64]| -> u64 { (0..m).map(|c| if f.parent[c] == NONE { 1 } else { v[c] }).sum() };
    format!("{{\"f\":\"{}\",\"pre\":\"{}\",\"nodes\":{},\"wpd\":{},\"len\":{},\"ntr\":{},\"c2_read_wrong\":{},\"c2_val_wrong\":{},\"c2_short\":{},\"adv_val_wrong\":{},\"tot_c2\":{},\"tot_ours\":{},\"tot_need\":{},\"edges\":[{}]}}",
        f.show(f.root), f.prefix(f.root), m, f.wpd[f.root], len, ntr, c2_read_wrong, c2_val_wrong, c2_short, adv_val_wrong,
        tot(&c2), tot(&ours), tot(&best), json_edges(f, &best, &rnd, &wit, &burst))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args[1].as_str() {
        // check SEED N: the per-read rule against real rings (sizes need and need-1)
        "check" => {
            let seed: u64 = args[2].parse().unwrap(); let n: usize = args[3].parse().unwrap();
            let mut rng = Rng(seed * 2654435761 + 1);
            let (mut ok_at, mut fail_below, mut nonmono) = (0u64, 0u64, 0u64);
            for _ in 0..n {
                let mut v = vec![]; let d = 2 + rng.below(3) as u32; let mb = [3, 8, 20][rng.below(3) as usize];
                gen(&mut rng, d, mb, 2, &mut v); let f = Formula::finish(v);
                let tr = gen_trace(&mut rng, 2, trace_len(&f, 30, 300));
                let (nd, _, vals) = needs(&f, &tr);
                let sz: Vec<u64> = nd.clone();
                let (vw, sh, mm) = ring_check(&f, &tr, &sz, &vals);
                assert!(!vw && !sh && mm.iter().all(|&x| x == 0), "need sizes not enough: {}", f.show(f.root));
                ok_at += 1;
                // each edge with need > 1 alone at need-1 (others unbounded = huge) must mismatch a read
                for c in 0..f.n.len() {
                    if f.parent[c] == NONE || nd[c] <= 1 { continue; }
                    let mut s2: Vec<u64> = vec![tr.len() as u64 + 2; f.n.len()]; s2[c] = nd[c] - 1;
                    let (_, _, mm2) = ring_check(&f, &tr, &s2, &vals);
                    if mm2[c] > 0 { fail_below += 1; } else { nonmono += 1; }
                }
            }
            println!("check: need sizes exact-ok on {} runs; edge at need-1 mismatches {} times, does not {} times", ok_at, fail_below, nonmono);
        }
        // dump SEED N: formula prefix, trace, root outputs (unbounded, c2po rings) for the Python cross-check
        "dump" => {
            let seed: u64 = args[2].parse().unwrap(); let n: usize = args[3].parse().unwrap();
            let mut rng = Rng(seed * 2654435761 + 7);
            for _ in 0..n {
                let mut v = vec![]; gen(&mut rng, 3, 4, 2, &mut v); let f = Formula::finish(v);
                let tr = gen_trace(&mut rng, 2, 25);
                let mut s = St::new(&f, None); s.run(&tr);
                let c2: Vec<u64> = (0..f.n.len()).map(|c| f.c2po(c)).collect();
                let mut r = St::new(&f, Some(&c2)); r.run(&tr);
                let ts: Vec<String> = tr.iter().map(|s| s.iter().map(|&b| if b { '1' } else { '0' }).collect()).collect();
                let o = |x: &[(bool, u64)]| x.iter().map(|(v, t)| format!("{}{}", if *v { 'T' } else { 'F' }, t)).collect::<Vec<_>>().join(",");
                println!("{}|{}|{}|{}", f.prefix(f.root), ts.join(","), o(&s.root_out), o(&r.root_out));
            }
        }
        // run SEED NF DEPTH MAXB NTR NADV LMIN LMAX THREADS > out.jsonl
        "run" => {
            let p: Vec<u64> = args[2..11].iter().map(|x| x.parse().unwrap()).collect();
            let distinct = args.get(11).map_or(false, |x| x == "distinct");
            let (seed, nf, depth, maxb, ntr, nadv, lmin, lmax, th) = (p[0], p[1] as usize, p[2] as u32, p[3], p[4] as usize, p[5] as usize, p[6] as usize, p[7] as usize, p[8] as usize);
            let (tx, rx) = std::sync::mpsc::channel::<String>();
            let mut hs = vec![];
            for t in 0..th {
                let tx = tx.clone();
                hs.push(std::thread::spawn(move || {
                    let mut i = t;
                    while i < nf {
                        let mut rng = Rng((seed * 1_000_003 + i as u64) * 2654435761 + 12345);
                        for _ in 0..3 { rng.next(); }
                        let mut v = vec![]; gen(&mut rng, depth, maxb, 2, &mut v);
                        let na = if distinct { distinct_atoms(&mut v) } else { 2 };
                        let f = Formula::finish(v);
                        if f.n.len() >= 3 { tx.send(study(&f, &mut rng, na, ntr, nadv, lmin, lmax)).unwrap(); }
                        i += th;
                    }
                }));
            }
            drop(tx);
            let out = std::io::stdout(); let mut o = out.lock();
            for line in rx { writeln!(o, "{}", line).unwrap(); }
            for h in hs { h.join().unwrap(); }
        }
        // one PREFIX NTR NADV: study a given formula
        "one" => {
            let toks: Vec<&str> = args[2].split_whitespace().collect(); let mut v = vec![];
            parse_prefix(&mut toks.iter(), &mut v); let f = Formula::finish(v);
            let mut rng = Rng(99);
            println!("{}", study(&f, &mut rng, 2, args[3].parse().unwrap(), args[4].parse().unwrap(), 30, 2000));
        }
        // explain PREFIX CHILD ITERS: hill-climb a trace maximizing need[CHILD], then log its reader
        "explain" => {
            let toks: Vec<&str> = args[2].split_whitespace().collect(); let mut v = vec![];
            parse_prefix(&mut toks.iter(), &mut v);
            let na = v.iter().filter_map(|n| if let K::P(a) = n.k { Some(a + 1) } else { None }).max().unwrap_or(1);
            let f = Formula::finish(v);
            let e: usize = args[3].parse().unwrap(); let iters: usize = args[4].parse().unwrap();
            let len = trace_len(&f, 40, 400);
            let mut rng = Rng(4242);
            let mut best_tr = gen_trace(&mut rng, na, len); let mut best = needs(&f, &best_tr).0[e];
            for _ in 0..iters {
                let mut cur = if rng.f() < 0.1 { gen_trace(&mut rng, na, len) } else { best_tr.clone() };
                for _ in 0..1 + rng.below(3) { mutate(&mut rng, &mut cur); }
                let nd = needs(&f, &cur).0[e];
                if nd >= best { best = nd; best_tr = cur; }
            }
            println!("formula {}  child {} = {}  need {} c2po {} ours {}", f.show(f.root), e, f.show(e), best, f.c2po(e), f.ours(e));
            let ts: Vec<String> = best_tr.iter().map(|s| s.iter().map(|&b| if b { '1' } else { '0' }).collect()).collect();
            println!("trace {}", ts.join(" "));
            let mut s = St::new(&f, None); s.log = Some((f.parent[e], e));
            // track pointer for logging via wit.j: store ptr into wit[c].j before read
            for (n, st) in best_tr.iter().enumerate() { s.step(st, n as u64); }
            println!("need seen {} at {:?}", s.need[e], s.wit[e]);
        }
        // stress RULE SEED NF DEPTH MAXB ITERS THREADS [distinct]: search traces with need > rule on any edge
        "stress" => {
            let rule = args[2].clone();
            let p: Vec<u64> = args[3..9].iter().map(|x| x.parse().unwrap()).collect();
            let (seed, nf, depth, maxb, iters, th) = (p[0], p[1] as usize, p[2] as u32, p[3], p[4] as usize, p[5] as usize);
            let distinct = args.get(9).map_or(false, |x| x == "distinct");
            let (tx, rx) = std::sync::mpsc::channel::<String>();
            let mut hs = vec![];
            for t in 0..th {
                let tx = tx.clone(); let rule = rule.clone();
                hs.push(std::thread::spawn(move || {
                    let mut i = t;
                    while i < nf {
                        let mut rng = Rng((seed * 1_000_003 + i as u64) * 2654435761 + 999);
                        for _ in 0..3 { rng.next(); }
                        let mut v = vec![]; gen(&mut rng, depth, maxb, 2, &mut v);
                        let na = if distinct { distinct_atoms(&mut v) } else { 2 };
                        let f = Formula::finish(v);
                        i += th;
                        let m = f.n.len();
                        let rv: Vec<i64> = (0..m).map(|c| rule_size(&f, c, &rule) as i64).collect();
                        let edges: Vec<usize> = (0..m).filter(|&c| f.parent[c] != NONE && (f.need_upper(c) as i64) > rv[c]).collect();
                        if edges.is_empty() { tx.send(format!("{{\"f\":\"{}\",\"gap\":-99}}", f.show(f.root))).unwrap(); continue; }
                        let len = trace_len(&f, 40, 1200);
                        let mut gap = i64::MIN; let mut worst = String::new();
                        let per = (iters / edges.len()).max(50);
                        for &e in &edges {
                            let mut cur = gen_trace(&mut rng, na, len);
                            let mut sc = needs(&f, &cur).0[e] as i64 - rv[e];
                            for it in 0..per {
                                let mut cand = if it % 200 == 199 { gen_trace(&mut rng, na, len) } else { cur.clone() };
                                for _ in 0..1 + rng.below(4) { mutate(&mut rng, &mut cand); }
                                let s2 = needs(&f, &cand).0[e] as i64 - rv[e];
                                if s2 >= sc || rng.f() < 0.02 { if s2 > gap { gap = s2; if s2 > 0 {
                                    let ts: Vec<String> = cand.iter().map(|s| s.iter().map(|&b| if b { '1' } else { '0' }).collect()).collect();
                                    worst = format!(",\"edge\":{},\"child\":\"{}\",\"need\":{},\"rule\":{},\"trace\":\"{}\"", e, f.show(e), s2 + rv[e], rv[e], ts.join(" ")); } }
                                    sc = s2; cur = cand; }
                            }
                        }
                        tx.send(format!("{{\"f\":\"{}\",\"pre\":\"{}\",\"gap\":{}{}}}", f.show(f.root), f.prefix(f.root), gap, worst)).unwrap();
                    }
                }));
            }
            drop(tx);
            let out = std::io::stdout(); let mut o = out.lock();
            for line in rx { writeln!(o, "{}", line).unwrap(); }
            for h in hs { h.join().unwrap(); }
        }
        // c2cex PREFIX ITERS SEED: search a trace on which the C2PO-sized ring model gives a wrong value;
        // prints "trace <rows>" and "ref <per-step values>" and "c2 <values>" (or "none").
        "c2cex" => {
            let toks: Vec<&str> = args[2].split_whitespace().collect(); let mut v = vec![];
            parse_prefix(&mut toks.iter(), &mut v);
            let na = v.iter().filter_map(|n| if let K::P(a) = n.k { Some(a + 1) } else { None }).max().unwrap_or(1);
            let f = Formula::finish(v); let m = f.n.len();
            let iters: usize = args[3].parse().unwrap();
            let mut rng = Rng(args[4].parse::<u64>().unwrap() * 7919 + 1);
            let c2: Vec<u64> = (0..m).map(|c| f.c2po(c)).collect();
            let len = trace_len(&f, 40, 400);
            let score = |tr: &Vec<Vec<bool>>| -> (i64, bool, Vec<bool>, Vec<bool>) {
                let (nd, _, vals) = needs(&f, tr);
                let sc: i64 = (0..m).filter(|&c| f.parent[c] != NONE).map(|c| (nd[c] as i64 - c2[c] as i64).max(0)).sum();
                let mut st = St::new(&f, Some(&c2)); st.run(tr); let cv = per_step(&st.root_out);
                let wrong = cv.iter().enumerate().any(|(j, &x)| j < vals.len() && vals[j] != x);
                (sc, wrong, vals, cv)
            };
            let mut cur = gen_trace(&mut rng, na, len); let mut best = score(&cur);
            let mut it = 0;
            while !best.1 && it < iters {
                let mut cand = if it % 300 == 299 { gen_trace(&mut rng, na, len) } else { cur.clone() };
                for _ in 0..1 + rng.below(4) { mutate(&mut rng, &mut cand); }
                let s2 = score(&cand);
                if s2.1 || s2.0 >= best.0 { best = s2; cur = cand; }
                it += 1;
            }
            let b = |v: &[bool]| v.iter().map(|&x| if x { '1' } else { '0' }).collect::<String>();
            if best.1 {
                let ts: Vec<String> = cur.iter().map(|s| b(s)).collect();
                println!("trace {}", ts.join(" ")); println!("ref {}", b(&best.2)); println!("c2 {}", b(&best.3));
            } else { println!("none"); }
        }
        // psi SEED NF DEPTH MAXB ITERS THREADS: max of potential - (x+y) per edge class
        "psi" => {
            let p: Vec<u64> = args[2..8].iter().map(|x| x.parse().unwrap()).collect();
            let (seed, nf, depth, maxb, iters, th) = (p[0], p[1] as usize, p[2] as u32, p[3], p[4] as usize, p[5] as usize);
            let (tx, rx) = std::sync::mpsc::channel::<String>();
            let mut hs = vec![];
            for t in 0..th {
                let tx = tx.clone();
                hs.push(std::thread::spawn(move || {
                    let mut i = t;
                    while i < nf {
                        let mut rng = Rng((seed * 1_000_003 + i as u64) * 2654435761 + 31);
                        for _ in 0..3 { rng.next(); }
                        let mut v = vec![]; gen(&mut rng, depth, maxb, 2, &mut v);
                        let na = distinct_atoms(&mut v);
                        let f = Formula::finish(v); i += th; let m = f.n.len();
                        let len = trace_len(&f, 40, 1200);
                        let run = |tr: &Vec<Vec<bool>>| { let mut s = St::new(&f, None); s.run(tr); (s.psi, s.need) };
                        let mut best = vec![i64::MIN; m]; let mut bneed = vec![1u64; m];
                        let edges: Vec<usize> = (0..m).filter(|&c| f.parent[c] != NONE && !matches!(f.n[f.parent[c]].k, K::Not)).collect();
                        if edges.is_empty() { continue; }
                        let per = (iters / edges.len()).max(50);
                        for &e in &edges {
                            let mut cur = gen_trace(&mut rng, na, len); let mut sc = run(&cur).0[e];
                            for it in 0..per {
                                let mut cand = if it % 200 == 199 { gen_trace(&mut rng, na, len) } else { cur.clone() };
                                for _ in 0..1 + rng.below(4) { mutate(&mut rng, &mut cand); }
                                let (ps, nd) = run(&cand);
                                for c in 0..m { if ps[c] > best[c] { best[c] = ps[c]; } if nd[c] > bneed[c] { bneed[c] = nd[c]; } }
                                if ps[e] >= sc { sc = ps[e]; cur = cand; }
                            }
                        }
                        for &c in &edges {
                            let s = f.sibling(c);
                            let slow = f.wpd[c] > f.wpd[s];
                            let pk = match f.n[f.parent[c]].k { K::And => "&", _ => "U" };
                            tx.send(format!("{} {} {} {} {} {}", pk, if slow { "slow" } else { "fast" }, best[c], f.ours(c) - 1, f.c2po(c) - 1, bneed[c])).unwrap();
                        }
                    }
                }));
            }
            drop(tx);
            let out = std::io::stdout(); let mut o = out.lock();
            for line in rx { writeln!(o, "{}", line).unwrap(); }
            for h in hs { h.join().unwrap(); }
            eprintln!("invariant checked {} failed {}", INVCHK.load(std::sync::atomic::Ordering::Relaxed), INVFAIL.load(std::sync::atomic::Ordering::Relaxed));
        }
        "invstats" => { println!("checked {} failed {}", INVCHK.load(std::sync::atomic::Ordering::Relaxed), INVFAIL.load(std::sync::atomic::Ordering::Relaxed)); }
        _ => panic!("mode"),
    }
}
