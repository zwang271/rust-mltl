import random, subprocess, sys, os
from sim import *
def rf(d, maxb):
    if d == 0 or random.random() < 0.15: return Node('P', atom=random.randrange(2))
    k = random.choice('U!&UUU')
    if k == '!': return Node('!', rf(d - 1, maxb))
    if k == '&': return Node('&', rf(d - 1, maxb), rf(d - 1, maxb))
    a = random.randint(0, maxb); b = a + random.randint(0, maxb)
    return Node('U', rf(d - 1, maxb), rf(d - 1, maxb), a=a, b=b)
def c2(x):
    if x.kind == 'P': return f's{x.atom}'
    if x.kind == '!': return f'!({c2(x.kids[0])})'
    if x.kind == '&': return f'(({c2(x.kids[0])}) && ({c2(x.kids[1])}))'
    return f'(({c2(x.kids[0])}) U[{x.a},{x.b}] ({c2(x.kids[1])}))'
def root_cov(f, tr, v):
    covs = []
    for n, st in enumerate(tr):
        update(f, st, n, FIRST, v)
        while update(f, st, n, RLNP, v) != RLNP: pass
        covs.append(f.cov)
    return covs
def rust_cov(f, tr):
    open('/tmp/r2real/c.c2po', 'w').write(f"INPUT\n    s0,s1: bool;\n\nFTSPEC\n    {c2(f)};\n")
    r = subprocess.run(['python3', '/Users/wangzili/Documents/MLTL_R2U2-/r2u2/compiler/c2po.py', '--impl', 'rust', '--no-rewrite',
                        '--no-cse', '--scq-constant', '64', '--map', '/tmp/r2real/t.map', '-o', '/tmp/r2real/c.bin', '-q', '/tmp/r2real/c.c2po'],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stdout + r.stderr
    trs = ';'.join(''.join('1' if b else '0' for b in s) for s in tr)
    out = subprocess.run(['/tmp/r2real/driver/target/release/driver', '/tmp/r2real/c.bin', trs], capture_output=True, text=True).stdout
    covs, cov, verd = [], 0, {}
    for line in out.strip().split('\n'):
        for tok in line.split(':', 1)[1].split():
            t, v = tok.split(':')[1].split(',')
            for j in range(cov, int(t) + 1): verd[j] = (v == 'T')
            cov = max(cov, int(t) + 1)
        covs.append(cov)
    return covs, verd
random.seed(int(sys.argv[1])); shown = 0; agree = disagree = 0
for it in range(int(sys.argv[2])):
    f = rf(3, 4); L = 30
    tr = [[random.random() < 0.5 for _ in range(2)] for _ in range(L)]
    cf, ci = root_cov(clone(f), tr, 'faithful'), root_cov(clone(f), tr, 'ideal')
    if cf == ci: continue
    cr, verd = rust_cov(f, tr)
    for j, v in verd.items(): assert sem(f, tr, j) == v, ('RUST UNSOUND', f, j)
    if cr == cf: agree += 1
    else:
        disagree += 1
        if disagree <= 2: print('MISMATCH sim-faithful vs rust:', f, '\n faithful', cf, '\n rust    ', cr)
    if shown < 1:
        shown += 1
        print('formula:', f, ' wpd =', wpd(f)); print('trace s0s1:', ' '.join(''.join('1' if b else '0' for b in s) for s in tr))
        print('root covered-up-to after each step:'); print(' ideal   ', ci); print(' faithful', cf); print(' rust    ', cr)
print('cases where faithful lags ideal at the root: rust == faithful in', agree, ', differs in', disagree)
