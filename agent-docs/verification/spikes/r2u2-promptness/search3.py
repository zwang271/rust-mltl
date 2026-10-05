import random, sys
from sim import *
def rf(d, maxb):
    if d == 0 or random.random() < 0.15: return Node('P', atom=random.randrange(2))
    k = random.choice('U!&UUU')
    if k == '!': return Node('!', rf(d - 1, maxb))
    if k == '&': return Node('&', rf(d - 1, maxb), rf(d - 1, maxb))
    a = random.randint(0, maxb); b = a + random.randint(0, maxb)
    return Node('U', rf(d - 1, maxb), rf(d - 1, maxb), a=a, b=b)
if __name__ == "__main__":
  random.seed(int(sys.argv[1])); D, M, L, N = map(int, sys.argv[2:6])
  miss = 0; lagdiff = 0; worst = None
  for it in range(N):
      f = rf(D, M); tr = [[random.random() < 0.5 for _ in range(2)] for _ in range(L)]
      ff, fi = clone(f), clone(f)
      # step both in lockstep, compare root-and-node coverage
      nf, ni = list(nodes(ff)), list(nodes(fi))
      for n, st in enumerate(tr):
          for x, v in ((ff, 'faithful'), (fi, 'ideal')):
              update(x, st, n, FIRST, v)
              while update(x, st, n, RLNP, v) != RLNP: pass
          for a_, b_ in zip(nf, ni):
              if a_.cov < n + 1 - wpd(a_): miss += 1; worst = worst or (repr(f), n)
              if a_.cov < b_.cov:
                  lagdiff += 1
                  d = b_.cov - a_.cov
                  if worst is None or (isinstance(worst, tuple) and len(worst) == 3 and d > worst[2]): worst = (repr(a_), n, d)
  print('deadline misses:', miss, ' node-steps where faithful lags ideal:', lagdiff, ' example:', worst)
