# Cross-check the Rust simulator against the Python one of ../r2u2-promptness
# (sim.py / ringhook.py): same root outputs, unbounded and with C2PO sizes.
import sys, subprocess
sys.path.insert(0, '../r2u2-promptness')
src = open('../r2u2-promptness/ringhook.py').read().replace("    HOOK(x)\n", "")
src = src.replace("from search3 import rf\n", "")
exec(src)
from sim import Node
def parse(toks):
    t = toks.pop(0)
    if t == '!': return Node('!', parse(toks))
    if t == '&': l = parse(toks); r = parse(toks); return Node('&', l, r)
    if t == 'U':
        a, b = int(toks.pop(0)), int(toks.pop(0)); l = parse(toks); r = parse(toks); return Node('U', l, r, a=a, b=b)
    if t in 'TF': return Node(t)
    return Node('P', atom=int(t[1:]))
def bpd(x):
    if x.kind in 'PTF': return 0
    if x.kind == '!': return bpd(x.kids[0])
    if x.kind == '&': return min(map(bpd, x.kids))
    return x.a + min(map(bpd, x.kids))
def c2(x, size):
    x.ring = R(size); x.rds = [0, 0]; x.out = []
    if x.kind == '!': c2(x.kids[0], 1)
    elif x.kind in '&U':
        l, r = x.kids
        c2(l, max(wpd(r) - bpd(l), 0) + 1); c2(r, max(wpd(l) - bpd(r), 0) + 1)
fmt = lambda o: ','.join(('T' if v else 'F') + str(t) for v, t in o)
out = subprocess.run(['target/release/r2u2-sizing', 'dump', sys.argv[1], sys.argv[2]], capture_output=True, text=True).stdout
ok = bad = 0
for line in out.strip().split('\n'):
    pre, trs, ou, oc = line.split('|')
    tr = [[c == '1' for c in s] for s in trs.split(',')]
    f = parse(pre.split()); g = clone(f); attach(g, 1, 10**4); pu = fmt(run(g, tr))
    h = clone(f); c2(h, 1); pc = fmt(run(h, tr))
    if pu == ou and pc == oc: ok += 1
    else:
        bad += 1
        if bad < 3: print('DIFF', pre, trs, '\n rust', ou, oc, '\n py  ', pu, pc)
print('xcheck agree', ok, 'differ', bad)
