import random, sys
from sim import *
from search3 import rf
random.seed(int(sys.argv[1])); N = int(sys.argv[2])
viol_local = 0; viol_any = 0; cases = 0; ex = None; h1 = 0
for it in range(N):
    f = rf(3, 4); L = 30
    tr = [[random.random() < 0.5 for _ in range(2)] for _ in range(L)]
    ff, fi = clone(f), clone(f); nf, ni = list(nodes(ff)), list(nodes(fi))
    prev_ideal = [0]*len(ni)
    for n, st in enumerate(tr):
        update(ff, st, n, FIRST, 'faithful')
        while update(ff, st, n, RLNP, 'faithful') != RLNP: pass
        update(fi, st, n, FIRST, 'ideal')
        while update(fi, st, n, RLNP, 'ideal') != RLNP: pass
        for k, x in enumerate(nf):
            if x.kind == 'U':
                cases += 1
                m = min(x.kids[0].cov, x.kids[1].cov)
                if x.cov + x.b < m:
                    viol_local += 1
                    if ex is None: ex = (repr(f), n, repr(x), x.cov, x.b, x.kids[0].cov, x.kids[1].cov)
            if x.cov < prev_ideal[k]: h1 += 1
        prev_ideal = [y.cov for y in ni]
print('UNTIL node-steps:', cases, ' with P + b < min(child cov):', viol_local, ' example:', ex)
print('faithful(n) < ideal(n-1):', h1)
