#!/usr/bin/env python3
"""Random MLTL formulas for the WEST differential test, one per line in
prefix form: T F (P n) (N x) (A x y) (O x y) (Fu a b x) (G a b x)
(U x a b y) (R x a b y). Deterministic for a given seed."""
import random, sys

def formula(r, depth, atoms, maxb):
    if depth == 0 or r.random() < 0.25:
        k = r.random()
        return "T" if k < 0.08 else "F" if k < 0.16 else f"(P {r.randrange(atoms)})"
    a = r.randrange(maxb + 1)
    b = a + r.randrange(maxb + 1 - a)
    op = r.randrange(8)
    sub = lambda: formula(r, depth - 1, atoms, maxb)
    if op == 0 or op == 7: return f"(N {sub()})"
    if op == 1: return f"(A {sub()} {sub()})"
    if op == 2: return f"(O {sub()} {sub()})"
    if op == 3: return f"(Fu {a} {b} {sub()})"
    if op == 4: return f"(G {a} {b} {sub()})"
    if op == 5: return f"(U {sub()} {a} {b} {sub()})"
    return f"(R {sub()} {a} {b} {sub()})"

if __name__ == "__main__":
    n, seed = int(sys.argv[1]), int(sys.argv[2])
    depth, atoms, maxb = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    r = random.Random(seed)
    for _ in range(n):
        print(formula(r, depth, atoms, maxb))
