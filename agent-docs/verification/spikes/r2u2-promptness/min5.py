import random, sys
exec(open('stress5.py').read().split("random.seed(")[0])
def size(x): return 1 + sum(size(c) for c in x.kids) + (x.b if x.kind == 'U' else 0)
r5 = mk(1, 2); best = None
random.seed(int(sys.argv[1]))
for it in range(int(sys.argv[2])):
    f = rf(random.randint(2, 4), random.randint(4, 20))
    for t in range(15):
        p = random.choice([.2,.5,.8]); L = random.randint(10, 80)
        tr = [[random.random() < p for _ in range(2)] for _ in range(L)]
        ref = clone(f); attach(ref, 1, 10**4); o = per_step(run(ref, tr))
        g = clone(f); r5(g, 1); o2 = per_step(run(g, tr))
        bad = [j for j in o2 if j in o and o[j] != o2[j]]
        if bad:
            # shorten the trace
            while len(tr) > 1:
                t2 = tr[:-1]; ref = clone(f); attach(ref, 1, 10**4); o = per_step(run(ref, t2))
                g = clone(f); r5(g, 1); o2 = per_step(run(g, t2))
                if any(j in o and o[j] != o2[j] for j in o2): tr = t2
                else: break
            key = (size(f), len(tr))
            if best is None or key < best[0]: best = (key, repr(f), tr); print(best[0], best[1], flush=True)
            break
print("BEST", best)
