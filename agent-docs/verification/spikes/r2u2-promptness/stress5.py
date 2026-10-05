import random, sys
exec(open('sizes3.py').read().split('rules = [("ours"')[0])
from search3 import rf
random.seed(int(sys.argv[1])); N = int(sys.argv[2]); MB = int(sys.argv[3]); L = int(sys.argv[4])
rules = [("C2PO", sib_rule(0)), ("ours #4", mk(None, None)), ("#5 &+1 U+2", mk(1, 2)), ("&+2 U+3", mk(2, 3))]
st = {n: [0, None] for n, _ in rules}
for it in range(N):
    f = rf(3, MB)
    p = random.choice([.1, .3, .5, .7, .9]); mode = random.random()
    if mode < 0.3: tr = [[(t // random.randint(1,3)) % 2 == 0, random.random() < p] for t in range(L)]
    elif mode < 0.5: tr = [[t % 2 == 0, t % 3 == 0] for t in range(L)]
    else: tr = [[random.random() < p for _ in range(2)] for _ in range(L)]
    ref = clone(f); attach(ref, 1, 10**4); o = per_step(run(ref, tr))
    for name, att in rules:
        g = clone(f); att(g, 1); o2 = per_step(run(g, tr))
        if any(j in o and o[j] != o2[j] for j in o2):
            st[name][0] += 1
            if st[name][1] is None or len(repr(f)) < len(st[name][1]): st[name][1] = repr(f)
for n, (b, ex) in st.items(): print(f"maxb {MB} len {L}: {n:12} wrong {b}/{N}  {ex or ''}")
