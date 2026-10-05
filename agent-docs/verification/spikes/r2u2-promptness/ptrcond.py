import random, sys
exec(open('/tmp/r2sim/ringhook.py').read())
def rfu(d, maxb, natoms):
    if d == 0 or random.random() < 0.12: return Node('P', atom=random.randrange(natoms))
    k = random.choice('U!&UUUU')
    if k == '!': return Node('!', rfu(d - 1, maxb, natoms))
    if k == '&': return Node('&', rfu(d - 1, maxb, natoms), rfu(d - 1, maxb, natoms))
    a = random.randint(0, maxb); b = a + random.randint(0, maxb)
    return Node('U', rfu(d - 1, maxb, natoms), rfu(d - 1, maxb, natoms), a=a, b=b)
class LR:   # unbounded compacted list; pointer = logical index
    def __init__(s): s.ent = []
    def write(s, v):
        if s.ent and s.ent[-1][0] == v[0]: s.ent[-1] = v
        else: s.ent.append(v)
    def read(s, j, tau):
        if not s.ent: return None, 0
        while True:
            if s.ent[j][1] >= tau: return s.ent[j], j
            if j + 1 == len(s.ent): return None, j
            j += 1
def attachL(x):
    x.ring = LR(); x.rds = [0, 0]; x.out = []
    for c in x.kids: attachL(c)
stats = {}
def HOOK(x):
    for i, c in enumerate(x.kids):
        L = len(c.ring.ent); j = x.rds[i]
        if L == 0: continue
        tau = x.nt
        f = next((k for k in range(L) if c.ring.ent[k][1] >= tau), L)
        for extra in (1, 2):
            N = opw(x) + extra
            key = (x.kind, extra)
            st = stats.setdefault(key, [0, 0, 0, None])
            st[0] += 1
            if j < L - N:                       # pointer slot overwritten
                st[1] += 1
                start = j + N * ((L - 1 - j) // N)
                if start > f:
                    st[2] += 1
                    if st[3] is None: st[3] = CUR
                assert f >= L - N, ('needed entry not live', CUR)
random.seed(int(sys.argv[1])); N = int(sys.argv[2])
for it in range(N):
    f = rfu(4, 4, 2); p = random.random(); CUR = repr(f)
    tr = [[random.random() < p for _ in range(2)] for _ in range(35)]
    attachL(f); run(f, tr)
for (k, e), (reads, over, bad, ex) in sorted(stats.items()):
    print(f'reader {k}, size wpd(operands)+{e}: {reads} reads, pointer slot overwritten in {over}, wrong entry would be read in {bad}', ex or '')
