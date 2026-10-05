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
worst = {}
def HOOK(x):
    for i, c in enumerate(x.kids):
        lag = len(c.ring.ent) - x.rds[i] - opw(x)
        if lag > worst.get(x.kind, (-99, None))[0]: worst[x.kind] = (lag, CUR)
random.seed(int(sys.argv[1])); N = int(sys.argv[2])
for it in range(N):
    f = rfu(4, 4, 2); p = random.random(); CUR = repr(f)
    tr = [[random.random() < p for _ in range(2)] for _ in range(35)]
    attachL(f); run(f, tr)
for k, (lag, ex) in worst.items(): print(f'reader {k}: max entries-from-pointer - wpd(operands) = {lag}   e.g. {ex}')
