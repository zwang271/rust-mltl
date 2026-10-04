"""Generate formula-progression benchmark workloads as plain text files.

Layout: workloads/<experiment>/<param>/{formulas.txt,traces.txt,meta.json}

Formulas are written in prefix notation, one per line, so that both drivers
(Rust and the Isabelle-exported Haskell) parse them with a few lines of code:
  true | false | p<k> | ! f | & f g | "|" f g | F a b f | G a b f | U a b f g | R a b f g
Traces: one per line, steps separated by spaces, each step one '0'/'1' per atom.

Experiments
  length   Trace length n grows, interval bounds grow with it (about n), so no
           formula is decided before the last step. The common case for
           progression: an invariant checked over a whole run.
  width    Fixed n = 512; nested windows of width w, e.g. G[0,w] F[0,w] p1.
           Every open window is a pending obligation, so the progressed
           formula holds O(w) subformulas at every step.
  random   Random formulas (depth <= 4, bounds <= 10, 3 atoms) on random
           traces of length n; many are decided early.
"""
import json, random, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "workloads"


def write(exp, param, formulas, traces, **meta):
    d = OUT / exp / str(param)
    d.mkdir(parents=True, exist_ok=True)
    (d / "formulas.txt").write_text("\n".join(formulas) + "\n")
    (d / "traces.txt").write_text("\n".join(traces) + "\n")
    (d / "meta.json").write_text(json.dumps(dict(experiment=exp, param=param, **meta)))


def trace_line(steps):
    return " ".join("".join("1" if x else "0" for x in s) for s in steps)


def periodic(n, period, off):
    """p0 always true, p1 true every `period` steps, p2 never."""
    return trace_line([[True, (k + off) % period == 0, False] for k in range(n)])


def length_formulas(n):
    b = n - 6
    return [
        f"G 0 {b} | ! p0 F 0 5 p1",          # G[0,n-6] (!p0 | F[0,5] p1)
        f"G 0 {b} U 0 5 p0 p1",              # G[0,n-6] (p0 U[0,5] p1)
        f"G 0 {b} F 0 5 p1",                 # G[0,n-6] F[0,5] p1
        f"F 0 {n - 1} & p0 & p1 p2",         # F[0,n-1] (p0 & p1 & p2): p2 never holds
    ]


def random_formula(rng, depth):
    if depth == 0 or rng.random() < 0.25:
        r = rng.randrange(5)
        return "true" if r == 0 else "false" if r == 1 else f"p{rng.randrange(3)}"
    a = rng.randrange(6)
    b = a + rng.randrange(5)
    sub = lambda: random_formula(rng, depth - 1)
    op = rng.randrange(7)
    return [f"! {sub()}", f"& {sub()} {sub()}", f"| {sub()} {sub()}", f"F {a} {b} {sub()}",
            f"G {a} {b} {sub()}", f"U {a} {b} {sub()} {sub()}", f"R {a} {b} {sub()} {sub()}"][op]


def main(quick=False):
    rng = random.Random(20261003)
    ns = [8, 16, 32, 64, 128, 256] if quick else [8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384]
    for n in ns:
        write("length", n, length_formulas(n), [periodic(n, 4, off) for off in range(4)], n=n)
    ws = [2, 4, 8, 16, 32] if quick else [2, 4, 8, 16, 32, 64, 128, 256]
    for w in ws:
        n = 512
        formulas = [f"G 0 {n} F 0 {w} p1", f"G 0 {n} U 0 {w} p0 p1", f"G 0 {n} G 0 {w} F 0 {w} p1"]
        write("width", w, formulas, [periodic(n, max(w // 2, 1), off) for off in range(2)], n=n, w=w)
    formulas = [random_formula(rng, 4) for _ in range(100)]
    for n in ([16, 64] if quick else [16, 64, 256, 1024]):
        traces = [trace_line([[rng.random() < 0.5 for _ in range(3)] for _ in range(n)]) for _ in range(10)]
        write("random", n, formulas, traces, n=n)


if __name__ == "__main__":
    main(quick="--quick" in sys.argv)
