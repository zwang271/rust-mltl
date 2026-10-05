import random, sys
from sim import *
def rand_f2(d, natoms, maxb):
    if d == 0 or random.random() < 0.2:
        return Node('P', atom=random.randrange(natoms)) if random.random() < 0.9 else Node(random.choice('TF'))
    k = random.choice('!&UUU')
    if k == '!': return Node('!', rand_f2(d - 1, natoms, maxb))
    if k == '&': return Node('&', rand_f2(d - 1, natoms, maxb), rand_f2(d - 1, natoms, maxb))
    a = random.randint(0, maxb); b = a + random.randint(0, maxb)
    return Node('U', rand_f2(d - 1, natoms, maxb), rand_f2(d - 1, natoms, maxb), a=a, b=b)
random.seed(int(sys.argv[1])); D, M, L, N = map(int, sys.argv[2:6])
found = None
for it in range(N):
    f = rand_f2(D, 3, M)
    tr = [[random.random() < 0.5 for _ in range(3)] for _ in range(random.randint(1, L))]
    ff = clone(f); bf = run(ff, tr, 'faithful'); check_sound(ff, tr)
    if bf:
        fi = clone(f); bi = run(fi, tr, 'ideal'); check_sound(fi, tr); assert not bi, ('IDEAL MISSES', f, tr, bi)
        key = (len(repr(f)), len(tr))
        if found is None or key < found[0]: found = (key, f, tr, bf)
if found:
    _, f, tr, bf = found
    print('formula:', f); print('trace:', [''.join('1' if v else '0' for v in s) for s in tr]); print('misses:', bf[:4])
else: print('no counterexample')
