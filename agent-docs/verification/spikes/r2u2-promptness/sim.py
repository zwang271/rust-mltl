# Throwaway simulator of the idealized R2U2 model (history queues, compaction,
# Isabelle operators). variant='faithful': UNTIL's skip reports no progress
# (Isabelle/Rust); 'ideal': it reports progress.
import random, sys
RLNP, RLWP, FIRST = 'RLNP', 'RLWP', 'FIRST'
def prop(ps): return RLNP if all(p == RLNP for p in ps) else RLWP

class Node:
    def __init__(s, kind, *kids, a=0, b=0, atom=None):
        s.kind, s.kids, s.a, s.b, s.atom = kind, list(kids), a, b, atom
        s.ent = []          # compacted entries [(val, time)]
        s.cov = 0           # next_after
        s.nt = a if kind == 'U' else 0
        s.prev = None
    def write(s, val, t):
        assert t >= s.cov, (s, val, t, s.cov)
        if s.ent and s.ent[-1][0] == val: s.ent[-1] = (val, t)
        else: s.ent.append((val, t))
        s.cov = t + 1
    def __repr__(s):
        k = s.kind
        if k == 'P': return f'p{s.atom}'
        if k in ('T', 'F'): return {'T': 'true', 'F': 'false'}[k]
        if k == '!': return f'!({s.kids[0]})'
        if k == '&': return f'({s.kids[0]} & {s.kids[1]})'
        return f'({s.kids[0]} U[{s.a},{s.b}] {s.kids[1]})'

def read(parent, child):
    for v, t in child.ent:
        if t >= parent.nt: return (v, t)
    return None

def wpd(x):
    if x.kind in 'PTF': return 0
    if x.kind == '!': return wpd(x.kids[0])
    if x.kind == '&': return max(map(wpd, x.kids))
    return x.b + max(map(wpd, x.kids))

def update(x, state, n, prog, variant):
    ps = [update(c, state, n, prog, variant) for c in x.kids]
    k = x.kind
    if k in 'PTF':
        if prog == FIRST:
            x.write(state[x.atom] if k == 'P' else (k == 'T'), n); return RLWP
        return RLNP
    if k == '!':
        d = read(x, x.kids[0])
        if d: x.write(not d[0], d[1]); x.nt = d[1] + 1; p = RLWP
        else: p = prop([prog])
        return prop(ps + [p])
    if k == '&':
        l, r = read(x, x.kids[0]), read(x, x.kids[1])
        v = None
        if l and r:
            if l[0] and r[0]: v = (True, min(l[1], r[1]))
            elif not l[0] and not r[0]: v = (False, max(l[1], r[1]))
            elif l[0]: v = (False, r[1])
            else: v = (False, l[1])
        elif l and not l[0]: v = (False, l[1])
        elif r and not r[0]: v = (False, r[1])
        if v: x.write(*v); x.nt = v[1] + 1; p = RLWP
        else: p = prop([prog])
        return prop(ps + [p])
    # UNTIL
    a, b = x.a, x.b
    l, r = read(x, x.kids[0]), read(x, x.kids[1])
    wait = prop([prog])
    ef = b if x.prev is None else x.prev + b + 1
    p = wait
    if r:
        if r[0]:
            t = r[1] - a; x.write(True, t); x.prev = t; x.nt = r[1] + 1; p = RLWP
        elif l:
            tm = min(l[1], r[1])
            if not l[0]:
                t = tm - a; x.write(False, t); x.prev = t; x.nt = tm + 1; p = RLWP
            elif r[1] >= ef:
                t = r[1] - b; x.write(False, t); x.prev = t; x.nt = max(tm + 1, t + a + 1); p = RLWP
            else:
                x.nt = tm + 1; p = (RLWP if variant == 'ideal' else wait)
        elif r[1] >= ef:
            t = r[1] - b; x.write(False, t); x.prev = t; x.nt = max(x.nt, t + a + 1); p = RLWP
    return prop(ps + [p])

def nodes(x):
    yield x
    for c in x.kids: yield from nodes(c)

def run(f, trace, variant):
    """Returns list of (step, node, cov, required) violations of cov >= n+1-wpd."""
    bad = []
    for n, st in enumerate(trace):
        update(f, st, n, FIRST, variant)
        while update(f, st, n, RLNP, variant) != RLNP: pass
        for x in nodes(f):
            need = n + 1 - wpd(x)
            if x.cov < need: bad.append((n, repr(x), x.cov, need))
    return bad

def sem(x, tr, i):   # AFP finite-trace semantics at position i
    k = x.kind; L = len(tr)
    if k == 'T': return True
    if k == 'F': return False
    if k == 'P': return i < L and tr[i][x.atom]
    if k == '!': return not sem(x.kids[0], tr, i)
    if k == '&': return sem(x.kids[0], tr, i) and sem(x.kids[1], tr, i)
    a, b = x.a, x.b
    if not (L - i > a): return False   # len (drop i π) > a
    return any(sem(x.kids[1], tr, i + k2) and all(sem(x.kids[0], tr, i + j) for j in range(a, k2))
               for k2 in range(a, b + 1))

def check_sound(f, tr):
    for x in nodes(f):
        prev = -1
        for v, t in x.ent:
            for j in range(prev + 1, t + 1):
                assert sem(x, tr, j) == v, ('UNSOUND', x, j)
            prev = t

def rand_f(d, natoms):
    if d == 0 or random.random() < 0.25:
        return Node('P', atom=random.randrange(natoms)) if random.random() < 0.9 else Node(random.choice('TF'))
    k = random.choice('!&UU')
    if k == '!': return Node('!', rand_f(d - 1, natoms))
    if k == '&': return Node('&', rand_f(d - 1, natoms), rand_f(d - 1, natoms))
    a = random.randint(0, 3); b = a + random.randint(0, 3)
    return Node('U', rand_f(d - 1, natoms), rand_f(d - 1, natoms), a=a, b=b)

def clone(x):
    y = Node(x.kind, *[clone(c) for c in x.kids], a=x.a, b=x.b, atom=x.atom); return y

if __name__ == '__main__':
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    found = None
    for it in range(200000):
        f = rand_f(3, 2)
        tr = [[random.random() < 0.5 for _ in range(2)] for _ in range(random.randint(1, 14))]
        fi, ff = clone(f), clone(f)
        bi = run(fi, tr, 'ideal'); check_sound(fi, tr)
        bf = run(ff, tr, 'faithful'); check_sound(ff, tr)
        assert not bi, ('IDEAL MISSES', f, tr, bi)
        if bf and (found is None or (len(repr(f)), len(tr)) < (len(repr(found[0])), len(found[1]))):
            found = (f, tr, bf)
    if found:
        f, tr, bf = found
        print('formula:', f); print('trace:', [''.join('1' if v else '0' for v in s) for s in tr]); print('misses:', bf[:5])
    else:
        print('no counterexample')
