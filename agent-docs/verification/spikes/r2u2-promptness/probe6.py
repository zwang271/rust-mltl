import random, sys, collections
src = open('/tmp/r2sim/ringhook.py').read()
exec(src.replace("    HOOK(x)\n", "    HOOK(x, n, prog)\n").replace("def update(x, st, n, prog):", "def update(x, st, n, prog):\n    global CUR_N\n    CUR_N = n"))
from sim import wpd
def bpd(x):
    if x.kind in 'PTF': return 0
    if x.kind == '!': return bpd(x.kids[0])
    if x.kind == '&': return min(map(bpd, x.kids))
    return x.a + min(map(bpd, x.kids))
def ents(c): return [v for v in c.ring.slots if v is not None]   # unbounded: compacted history in order
def cov(c): return getattr(c, 'cov', 0)
STAT = collections.Counter(); WORST = {}
def HOOK(x, n, prog):
    if x.kind not in '&U': return
    for i, c in enumerate(x.kids):
        s = x.kids[1 - i]
        if wpd(c) <= wpd(s): continue          # rule #5 only bites for the slower child
        bl = cov(c) - x.nt
        ex = bl - max(wpd(s) - bpd(c), 0)
        key = (x.kind, 'first' if prog == FIRST else 'reloop')
        STAT[(key, ex)] += 1
        if key not in WORST or ex > WORST[key][0]: WORST[key] = (ex, repr(x), n)
random.seed(int(sys.argv[1])); N = int(sys.argv[2])
for it in range(N):
    f = rf(3, 4); tr = [[random.random() < random.choice([.2,.5,.8]) for _ in range(2)] for _ in range(40)]
    g = clone(f); attach(g, 100, 100); run(g, tr)
for k in sorted(WORST): print(k, "max excess", WORST[k])
for k in sorted(STAT): 
    if k[1] >= 0: print(k, STAT[k])
