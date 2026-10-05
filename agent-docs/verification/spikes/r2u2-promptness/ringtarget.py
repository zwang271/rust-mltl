import random, sys, itertools
src = open('/tmp/r2sim/ringsim.py').read().split("random.seed(int(sys.argv[1])); N")[0]
exec(src)
P = lambda i: Node('P', atom=i)
def small(depth):
    if depth == 0: return P(random.randrange(2))
    k = random.choice('PU!U&')
    if k == 'P': return P(random.randrange(2))
    if k == '!': return Node('!', small(depth - 1))
    if k == '&': return Node('&', small(depth - 1), small(depth - 1))
    a = random.randint(0, 1); b = a + random.randint(0, 2)
    return Node('U', small(depth - 1), small(depth - 1), a=a, b=b)
random.seed(int(sys.argv[1])); N = int(sys.argv[2])
found = {1: None, 2: None}; cnt = {1: 0, 2: 0}
for it in range(N):
    X, Y = small(2), small(2)
    a = random.randint(0, 2); b = a + random.randint(0, 3)
    f = Node('U', X, Y, a=a, b=b)
    if random.random() < 0.3: f = Node('!', f)
    pp = random.choice([0.2, 0.5, 0.8])
    tr = [[random.random() < pp for _ in range(2)] for _ in range(random.randint(10, 40))]
    ref = clone(f); attach(ref, 1, 10**6); o = run(ref, tr)
    for e in (1, 2):
        g = clone(f); attach(g, 1, e)
        if run(g, tr) != o:
            cnt[e] += 1
            if found[e] is None or len(repr(f)) < len(found[e][0]): found[e] = (repr(f), [''.join('1' if v else '0' for v in s) for s in tr])
print(cnt, found[1], found[2])
