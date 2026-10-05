import random, sys
src = open('/tmp/r2sim/ringsim.py').read().split("random.seed(int(sys.argv[1])); N")[0]
exec(src)
def rfu(d, maxb, natoms):
    if d == 0 or random.random() < 0.12: return Node('P', atom=random.randrange(natoms))
    k = random.choice('U!&UUUU')
    if k == '!': return Node('!', rfu(d - 1, maxb, natoms))
    if k == '&': return Node('&', rfu(d - 1, maxb, natoms), rfu(d - 1, maxb, natoms))
    a = random.randint(0, maxb); b = a + random.randint(0, maxb)
    return Node('U', rfu(d - 1, maxb, natoms), rfu(d - 1, maxb, natoms), a=a, b=b)
seed, N, D, M, L = map(int, sys.argv[1:6])
random.seed(seed)
res = {1: [0, None], 2: [0, None]}
for it in range(N):
    f = rfu(D, M, 2); p = random.random()
    tr = [[random.random() < p for _ in range(2)] for _ in range(L)]
    ref = clone(f); attach(ref, 1, 10**6); o = run(ref, tr)
    for extra in (1, 2):
        g = clone(f); attach(g, 1, extra)
        if run(g, tr) != o:
            res[extra][0] += 1
            if res[extra][1] is None or len(repr(f)) < len(res[extra][1][0]): res[extra][1] = (repr(f), tr)
for e in (1, 2): print(f'+{e}: {res[e][0]}/{N} differ', res[e][1][0] if res[e][1] else '')
