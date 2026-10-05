import random, sys
exec(open('sizes2.py').read().split("rules = [")[0])
def per_step(out):
    v = {}; s = 0
    for val, t in out:
        for j in range(s, t + 1): v[j] = val
        s = max(s, t + 1)
    return v
def mk(kand, kuntil):
    def att(x, size):
        x.ring = R(size); x.rds = [0, 0]; x.out = []
        if x.kind == '!': att(x.kids[0], 1)
        elif x.kind in '&U':
            w = opw(x); k = kand if x.kind == '&' else kuntil
            for i, c in enumerate(x.kids):
                s = x.kids[1 - i]
                ours = max(w - bpd(c), 0) + 1
                sz = ours if k is None else min(ours, max(wpd(s) - bpd(c), 0) + 1 + k)
                att(c, sz)
    return att
rules = [("ours", mk(None, None))] + [(f"&:sib+{a} U:{'ours' if u is None else 'sib+'+str(u)}", mk(a, u))
         for a, u in [(0, None), (1, None), (2, None), (None, 1), (None, 2), (None, 3), (1, 2)]]
rules.insert(0, ("C2PO", sib_rule(0)))
random.seed(int(sys.argv[2])); N = int(sys.argv[1])
st = {n: [0, 0, None] for n, _ in rules}
for it in range(N):
    f = rf(3, 4); tr = [[random.random() < random.choice([0.2,0.5,0.8]) for _ in range(2)] for _ in range(30)]
    ref = clone(f); attach(ref, 1, 10**6); o = per_step(run(ref, tr))
    for name, att in rules:
        g = clone(f); att(g, 1); o2 = per_step(run(g, tr)); st[name][1] += total(g)
        if any(j in o and o[j] != o2[j] for j in o2):
            st[name][0] += 1
            if st[name][2] is None or len(repr(f)) < len(st[name][2]): st[name][2] = repr(f)
b = st["C2PO"][1]
for n, (bad, tot, ex) in st.items(): print(f"{n:22} wrong {bad:5}/{N}  slots {tot/b:.2f}x C2PO  {ex or ''}")
