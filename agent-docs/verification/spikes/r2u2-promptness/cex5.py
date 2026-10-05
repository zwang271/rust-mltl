exec(open('stress5.py').read().split("random.seed(")[0])
from sim import Node, sem
P=lambda i: Node('P', atom=i); U=lambda l,a,b,r: Node('U', l, r, a=a, b=b); A=lambda l,r: Node('&', l, r)
f = A(U(A(U(P(1),3,7,P(0)), U(P(1),1,3,P(1))), 1, 5, P(0)), P(0))
T = [[True, False], [True, True], [True, True], [False, True], [True, False], [False, False], [True, True], [False, False], [True, False]]
for name, att in [("unbounded", lambda g,_: attach(g, 1, 10**4)), ("#4", mk(None,None)), ("#5", mk(1,2))]:
    g = clone(f); att(g, 1); print(f"{name:10}", per_step(run(g, T)))
print("sizes #5: top-& children", [len(c.ring.slots) for c in (lambda g: (mk(1,2)(g,1), g)[1])(clone(f)).kids])
