# P = entries of child c from the reader's pointer to the end (what the ring must hold), at each read,
# unbounded rings (no wrap: slot index = logical index). Split by regime:
#   timed:  reader's next_time >= (n+1) - wpd(s)   (time bound applies)
#   behind: otherwise
import random, sys, collections
src = open('/tmp/r2sim/ringhook.py').read()
exec(src.replace("    HOOK(x)\n", "    HOOK(x, n, prog)\n"))
from sim import wpd
def bpd(x):
    if x.kind in 'PTF': return 0
    if x.kind == '!': return bpd(x.kids[0])
    if x.kind == '&': return min(map(bpd, x.kids))
    return x.a + min(map(bpd, x.kids))
def ents(c): return [v for v in c.ring.slots if v is not None]
ST = collections.Counter(); W = {}
def HOOK(x, n, prog):
    if x.kind not in '&U': return
    for i, c in enumerate(x.kids):
        s = x.kids[1 - i]
        if wpd(c) <= wpd(s): continue
        L = len(ents(c))
        if L == 0: continue
        P = sum(1 for v in ents(c) if v[1] >= x.nt)
        sib = max(wpd(s) - bpd(c), 0)
        reg = 'tau>=cov_s' if x.nt >= getattr(s,'cov',0) else 'tau<cov_s'
        key = (x.kind, reg, 'first' if prog == FIRST else 'reloop')
        ex = P - sib
        ST[(key, ex)] += 1
        if key not in W or ex > W[key][0]: W[key] = (ex, repr(x), n)
random.seed(int(sys.argv[1]))
for it in range(int(sys.argv[2])):
    f = rf(int(sys.argv[3]), int(sys.argv[4])); tr = [[random.random() < random.choice([.2,.5,.8]) for _ in range(2)] for _ in range(int(sys.argv[5]))]
    g = clone(f); attach(g, 600, 600); run(g, tr)
print("B = entries >= tau at read. tau>=cov_s: B - sib ; tau<cov_s: B")
for k in sorted(W): print(k, "max", W[k])
for k in sorted(ST):
    if k[1] >= 1: print(k, ST[k])
