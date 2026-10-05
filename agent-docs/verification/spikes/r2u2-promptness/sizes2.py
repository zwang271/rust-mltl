import random, sys
exec(open('/tmp/r2sim/ringhook.py').read().replace("    HOOK(x)\n",""))
from search3 import rf
def bpd(x):
    if x.kind in 'PTF': return 0
    if x.kind == '!': return bpd(x.kids[0])
    if x.kind == '&': return min(map(bpd, x.kids))
    return x.a + min(map(bpd, x.kids))
def sib_rule(extra):
    def att(x, size):
        x.ring = R(size); x.rds = [0, 0]; x.out = []
        if x.kind == '!': att(x.kids[0], 1 + extra)
        elif x.kind in '&U':
            l, r = x.kids
            att(l, max(wpd(r) - bpd(l), 0) + 1 + extra); att(r, max(wpd(l) - bpd(r), 0) + 1 + extra)
    return att
def old(x, size):
    x.ring = R(size); x.rds = [0, 0]; x.out = []
    for c in x.kids: old(c, opw(x) + 1)
def new(x, size):
    x.ring = R(size); x.rds = [0, 0]; x.out = []
    if x.kind == '!': new(x.kids[0], 1)
    elif x.kind in '&U':
        w = opw(x)
        for c in x.kids: new(c, max(w - bpd(c), 0) + 1)
def total(x): return len(x.ring.slots) + sum(total(c) for c in x.kids)
rules = [("C2PO/Isabelle (sibling)", sib_rule(0)), ("old: wpd(operands)+1", old), ("new: max(w-bpd(c),0)+1", new)]
random.seed(11); N = int(sys.argv[1])
stats = {n: [0, 0, None] for n, _ in rules}
for it in range(N):
    f = rf(3, 4); tr = [[random.random() < 0.5 for _ in range(2)] for _ in range(30)]
    ref = clone(f); attach(ref, 1, 10**6); o = run(ref, tr)
    for name, att in rules:
        g = clone(f); att(g, 1); o2 = run(g, tr)
        stats[name][1] += total(g)
        if o2 != o:
            stats[name][0] += 1
            if stats[name][2] is None or len(repr(f)) < len(stats[name][2]): stats[name][2] = repr(f)
base = stats["C2PO/Isabelle (sibling)"][1]
for name, (bad, tot, ex) in stats.items():
    print(f"{name:26} wrong runs {bad:5}/{N}   total slots {tot/base:.2f}x C2PO   {('e.g. ' + ex) if ex else ''}")
