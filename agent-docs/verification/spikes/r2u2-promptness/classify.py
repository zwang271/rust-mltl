import random
exec(open('sizes2.py').read().split("rules = [")[0])
def per_step(out):
    v = {}; s = 0
    for val, t in out:
        for j in range(s, t + 1): v[j] = val
        s = max(s, t + 1)
    return v
random.seed(11); N = 20000; wrongval = missing = 0; ex = None
for it in range(N):
    f = rf(3, 4); tr = [[random.random() < 0.5 for _ in range(2)] for _ in range(30)]
    ref = clone(f); attach(ref, 1, 10**6); o = per_step(run(ref, tr))
    g = clone(f); sib_rule(0)(g, 1); o2 = per_step(run(g, tr))
    if o != o2:
        if any(j in o and o[j] != o2[j] for j in o2):
            wrongval += 1
            if ex is None or len(repr(f)) < len(ex): ex = repr(f)
        else: missing += 1
print("C2PO rule: wrong value", wrongval, " only coverage differs", missing, " e.g.", ex)
