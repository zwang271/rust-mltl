# Ring-buffer variant of sim.py: queues are rings of fixed size with
# Isabelle's compaction and read pointers (scq_read_aux). Compare the root
# output with the unbounded model, for child queue size = wpd(operands)+extra.
import random, sys
from sim import Node, wpd, nodes, clone, FIRST, RLNP, RLWP, prop, sem
from search3 import rf

class R:
    def __init__(s, size): s.slots = [None]*size; s.w = 0
    def write(s, v):
        n = len(s.slots); prev = n - 1 if s.w == 0 else s.w - 1
        if s.slots[prev] is not None and s.slots[prev][0] == v[0]: s.slots[prev] = v
        else: s.slots[s.w] = v; s.w = (s.w + 1) % n
    def read(s, rd, tau):
        n = len(s.slots)
        for _ in range(n):
            cur = s.slots[rd]
            if cur is None and rd == 0: return None, rd
            if cur is not None and cur[1] >= tau: return cur, rd
            if (rd + 1) % n == s.w: return None, rd
            rd = (rd + 1) % n
        return None, rd

def opw(x):
    if x.kind == '!': return wpd(x.kids[0])
    if x.kind in '&U': return max(wpd(x.kids[0]), wpd(x.kids[1]))
    return 0

def attach(x, size, extra):
    x.ring = R(size); x.rds = [0, 0]; x.out = []
    for c in x.kids: attach(c, opw(x) + extra, extra)

def write(x, val, t):
    x.write_hist = True
    x.out.append((val, t)); x.ring.write((val, t)); x.cov = t + 1

def update(x, st, n, prog):
    ps = [update(c, st, n, prog) for c in x.kids]
    k = x.kind
    if k in 'PTF':
        if prog == FIRST: write(x, st[x.atom] if k == 'P' else (k == 'T'), n); return RLWP
        return RLNP
    reads = []
    for i, c in enumerate(x.kids):
        d, x.rds[i] = c.ring.read(x.rds[i], x.nt); reads.append(d)
    if k == '!':
        d = reads[0]
        if d: write(x, not d[0], d[1]); x.nt = d[1] + 1; p = RLWP
        else: p = prop([prog])
        return prop(ps + [p])
    if k == '&':
        l, r = reads; v = None
        if l and r:
            if l[0] and r[0]: v = (True, min(l[1], r[1]))
            elif not l[0] and not r[0]: v = (False, max(l[1], r[1]))
            elif l[0]: v = (False, r[1])
            else: v = (False, l[1])
        elif l and not l[0]: v = (False, l[1])
        elif r and not r[0]: v = (False, r[1])
        if v: write(x, *v); x.nt = v[1] + 1; p = RLWP
        else: p = prop([prog])
        return prop(ps + [p])
    a, b = x.a, x.b; l, r = reads; wait = prop([prog]); p = wait
    ef = b if x.prev is None else x.prev + b + 1
    if r:
        if r[0]: t = r[1] - a; write(x, True, t); x.prev = t; x.nt = r[1] + 1; p = RLWP
        elif l:
            tm = min(l[1], r[1])
            if not l[0]: t = tm - a; write(x, False, t); x.prev = t; x.nt = tm + 1; p = RLWP
            elif r[1] >= ef: t = r[1] - b; write(x, False, t); x.prev = t; x.nt = max(tm + 1, t + a + 1); p = RLWP
            else: x.nt = tm + 1
        elif r[1] >= ef: t = r[1] - b; write(x, False, t); x.prev = t; x.nt = max(x.nt, t + a + 1); p = RLWP
    return prop(ps + [p])

def run(f, tr):
    for n, st in enumerate(tr):
        update(f, st, n, FIRST)
        while update(f, st, n, RLNP) != RLNP: pass
    return f.out

random.seed(int(sys.argv[1])); N = int(sys.argv[2])
for extra in (3, 2, 1, 0):
    bad = 0; ex = None
    random.seed(int(sys.argv[1]))
    for it in range(N):
        f = rf(3, 4); tr = [[random.random() < 0.5 for _ in range(2)] for _ in range(25)]
        ref = clone(f); attach(ref, 1, 10**6); out_ref = run(ref, tr)      # effectively unbounded
        g = clone(f); attach(g, 1, extra); out = run(g, tr)
        if out != out_ref:
            bad += 1
            if ex is None or len(repr(f)) < len(ex): ex = repr(f)
    print(f'child size wpd(operands)+{extra}: {bad}/{N} runs differ from unbounded', ('e.g. ' + ex) if ex else '')
