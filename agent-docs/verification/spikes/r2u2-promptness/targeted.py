from sim import *
import itertools
best = None
for K in range(1, 7):
  for B in range(0, 4):
    for A in range(0, B + 1):
      for L in range(4, 20):
        for pat in itertools.product([0, 1], repeat=3):
          # atoms: 0=p, 1=q, 2=r ; inner = p U[0,K] q ; outer = r U[A,B] inner
          def mk():
              inner = Node('U', Node('P', atom=0), Node('P', atom=1), a=0, b=K)
              return Node('U', Node('P', atom=2), inner, a=A, b=B)
          tr = []
          for n in range(L):
              p = 1 if n < K - 1 else pat[0]
              q = pat[1] if n == L - 1 else 0
              r = (n + pat[2]) % 2
              tr.append([bool(p), bool(q), bool(r)])
          ff = mk(); bf = run(ff, tr, 'faithful'); check_sound(ff, tr)
          fi = mk(); bi = run(fi, tr, 'ideal'); check_sound(fi, tr)
          assert not bi
          if bf:
              key = (K + B, L)
              if best is None or key < best[0]: best = (key, repr(ff), tr, bf)
if best:
    _, f, tr, bf = best
    print('formula:', f); print('trace (p q r):', [''.join('1' if v else '0' for v in s) for s in tr]); print('misses:', bf[:4])
else: print('none')
