import random, sys, collections
exec(open('/tmp/r2sim/ringhook.py').read().replace("    HOOK(x)\n", ""))
from sim import wpd, nodes
def cov(c): return getattr(c, 'cov', 0)
def ents(c): return [v for v in c.ring.slots if v is not None]
bad = collections.Counter(); tot = collections.Counter(); newmax = collections.Counter()
random.seed(int(sys.argv[1]))
for it in range(int(sys.argv[2])):
    f = rf(3, 4); tr = [[random.random() < random.choice([.2,.5,.8]) for _ in range(2)] for _ in range(40)]
    g = clone(f); attach(g, 100, 100); ns = [x for x in nodes(g) if x.kind in '&U']
    for n, st in enumerate(tr):
        before = {id(x): len(ents(x)) for x in nodes(g)}
        update(g, st, n, FIRST)
        while update(g, st, n, RLNP) != RLNP: pass
        for x in nodes(g):
            d = len(ents(x)) - before[id(x)]; newmax[(x.kind, d)] += 1
        for x in ns:
            l, r = x.kids; tot[x.kind] += 1
            if x.nt < min(cov(l), cov(r)): bad[x.kind] += 1
print("end-of-step  next_time >= min(cov_l, cov_r):  violations", dict(bad), "of", dict(tot))
print("compacted entries added per step, by node kind:", sorted(newmax.items()))
