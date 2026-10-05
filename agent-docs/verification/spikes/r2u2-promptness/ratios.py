import random, statistics
exec(open('sizes3.py').read().split("random.seed(")[0])
random.seed(11); r_ours=[]; r_c=[]; so=sc=sb=0
for it in range(20000):
    f = rf(3, 4)
    g=clone(f); sib_rule(0)(g,1); b=total(g)
    g=clone(f); mk(None,None)(g,1); o=total(g)
    g=clone(f); mk(1,2)(g,1); c=total(g)
    r_ours.append(o/b); r_c.append(c/b); so+=o; sc+=c; sb+=b
for n, r, s in [("ours (#4)", r_ours, so), ("candidate (#5)", r_c, sc)]:
    q = statistics.quantiles(r, n=20)
    print(f"{n:15} sum-ratio {s/sb:.2f}  mean {statistics.mean(r):.2f}  median {statistics.median(r):.2f}  p95 {q[18]:.2f}  max {max(r):.2f}  equal-to-C2PO {sum(x==1 for x in r)/len(r):.0%}")
print("C2PO slots per formula: mean", sb/20000)
