import random, sys
from sim import *
from search3 import rf
random.seed(int(sys.argv[1])); N = int(sys.argv[2])
viol = 0; cases = 0; ex = None; maxgap = 0
for it in range(N):
    f = rf(3, 4); L = 30
    tr = [[random.random() < 0.5 for _ in range(2)] for _ in range(L)]
    ff = clone(f); nf = list(nodes(ff))
    for n, st in enumerate(tr):
        update(ff, st, n, FIRST, 'faithful')
        while update(ff, st, n, RLNP, 'faithful') != RLNP: pass
        for x in nf:
            if x.kind == 'U':
                cases += 1
                G = n + 1 - max(wpd(x.kids[0]), wpd(x.kids[1]))
                m = min(x.kids[0].cov, x.kids[1].cov, G)
                if x.cov + x.b < m:
                    viol += 1
                    if ex is None: ex = (repr(f), n, repr(x), x.cov, x.b, x.kids[0].cov, x.kids[1].cov, G)
                maxgap = max(maxgap, m - (x.cov + x.b))
print('UNTIL node-steps:', cases, ' violating P + b >= min(cov_l, cov_r, guaranteed):', viol, ex, 'max gap', maxgap)
