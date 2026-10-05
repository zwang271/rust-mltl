import random, sys
exec(open('stress5.py').read().split("random.seed(")[0])
from sim import Node
def P(i): return Node('P', atom=i)
def U(l,a,b,r): return Node('U', l, r, a=a, b=b)
def A(l,r): return Node('&', l, r)
def Nn(x): return Node('!', x)
f = A(P(1), A(U(U(P(0),16,28,P(0)),18,35,U(P(0),10,23,P(1))), Nn(Nn(P(0)))))
print(repr(f))
rules = [("C2PO", sib_rule(0)), ("ours #4", mk(None, None)), ("#5", mk(1, 2)), ("&+2 U+3", mk(2, 3))]
random.seed(1); bad = {n:0 for n,_ in rules}; T = 3000
for it in range(T):
    p = random.choice([.1,.3,.5,.7,.9]); tr = [[random.random() < p for _ in range(2)] for _ in range(150)]
    ref = clone(f); attach(ref, 1, 10**4); o = per_step(run(ref, tr))
    for name, att in rules:
        g = clone(f); att(g, 1); o2 = per_step(run(g, tr))
        if any(j in o and o[j] != o2[j] for j in o2): bad[name] += 1
print(bad, "of", T)
