"""Generate benchmark workloads (formulas + traces) as plain text files.

Every evaluator (both verified Rust evaluators and libmltl) reads the same
files, so their timings are comparable and their answers can be cross-checked.

Layout: workloads/<experiment>/<param>/{formulas.txt,traces.txt,meta.json}

Experiments
  length   Trace length n grows; interval bounds grow with it (w = n/4), so the
           formula's horizon grows linearly with n. Two trace regimes:
             random    each atom true with probability 1/2 (early exits are cheap)
             periodic  p0 always true, p1 true every w steps (early exits are
                       late: the worst case for top-down evaluation)
  width    Fixed n; interval width w grows (periodic regime).
  depth    G[0,w] G[0,w] ... G[0,w] p0 with d nested operators on an all-true trace.
  libmltl  libmltl's own benchmark: its formulas.txt with every bound set to
           [0, n/2], random traces over 4 atoms.
  large-length  Heavy workload: G[0, n-64] over a conjunction of 7 clauses
           (response, nested recurrence, until, release, depth-3 nesting;
           ~45 nodes, windows up to 32) on traces of up to 2M steps. Traces
           are generated so that every clause holds at every step, so no
           evaluator can stop early.
  large-size    Same, at fixed n = 2^18, with k = 1 .. 32 copies of the clause
           group (bounds shifted by the copy index, so copies are distinct).
"""
import json, random, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "workloads"
LIBMLTL_FORMULAS = ROOT.parents[2] / "external/libmltl/tests/perf_compare/MLTL_interpreter/formulas.txt"


def family(w):
    """Formulas with two nested temporal operators, each with interval [0, w]."""
    return [
        f"G[0,{w}] (F[0,{w}] p1)",
        f"G[0,{w}] (p0 U[0,{w}] p1)",
        f"G[0,{w}] (!p0 | F[0,{w}] p1)",
        f"(p1 R[0,{w}] (F[0,{w}] p1))",
    ]


def trace_line(steps):
    return " ".join("".join("1" if x else "0" for x in s) for s in steps)


def random_traces(rng, count, n, atoms):
    return [trace_line([[rng.random() < 0.5 for _ in range(atoms)] for _ in range(n)]) for _ in range(count)]


def periodic_traces(rng, count, n, w):
    out = []
    for _ in range(count):
        off = rng.randrange(w)
        out.append(trace_line([[True, (k + off) % w == 0] for k in range(n)]))
    return out


def clause_group(j):
    """Seven clauses that hold at every step of a `structured_trace`; `j`
    shifts every window so that different copies are distinct formulas."""
    w = lambda x: x + j
    return [
        f"(!p0 | F[0,{w(16)}] p1)",
        f"G[0,{w(32)}] (F[0,{w(8)}] p2)",
        f"(p3 U[0,{w(24)}] p4)",
        f"(p5 R[0,{w(20)}] (p3 | p6))",
        f"G[0,{w(16)}] (!p6 | F[0,{w(16)}] (p1 & F[0,{w(8)}] p2))",
        f"F[0,{w(24)}] (p4 & (p3 U[0,{w(8)}] p2))",
        f"(p0 | p5 | p7 | F[0,{w(16)}] p1)",
    ]


def big_formula(n, copies):
    clauses = [c for j in range(copies) for c in clause_group(j)]
    body = " & ".join(f"({c})" for c in clauses)
    # every clause group j has horizon <= 3j + 41; keep all windows inside the trace
    return f"G[0,{n - 64 - 4 * copies}] ({body})"


def structured_trace(rng, n):
    """p1 occurs once in every block of 8 steps, p2 in every block of 4, p4
    in every block of 12 (so consecutive occurrences are < 2·period apart);
    p3 always holds; p0, p5, p6, p7 are random noise."""
    def recurring(period):
        on = [False] * n
        for start in range(0, n, period):
            on[min(n - 1, start + rng.randrange(period))] = True
        return on
    p1, p2, p4 = recurring(8), recurring(4), recurring(12)
    steps = []
    for k in range(n):
        r = rng.getrandbits(4)
        steps.append([r & 1, p1[k], p2[k], True, p4[k], r & 2, r & 4, r & 8])
    return trace_line(steps)


def write(exp, param, formulas, traces, **meta):
    d = OUT / exp / str(param)
    d.mkdir(parents=True, exist_ok=True)
    (d / "formulas.txt").write_text("\n".join(formulas) + "\n")
    (d / "traces.txt").write_text("\n".join(traces) + "\n")
    (d / "meta.json").write_text(json.dumps(dict(experiment=exp, param=param, **meta)))


def main(quick=False):
    rng = random.Random(20261003)
    lengths = [2 ** k for k in range(6, 12 if quick else 15)]       # 64 .. 16384
    for regime in ["random", "periodic"]:
        for n in lengths:
            w = n // 4
            traces = random_traces(rng, 16, n, 2) if regime == "random" else periodic_traces(rng, 16, n, w)
            write(f"length-{regime}", n, family(w), traces, n=n, w=w, regime=regime)

    n = 2048 if quick else 8192
    for k in range(0, 10 if quick else 12):                          # w = 1 .. 2048
        w = 2 ** k
        write("width", w, family(w), periodic_traces(rng, 16, n, w), n=n, w=w, regime="periodic")

    w, n = 8, 128
    for d in range(1, 8):
        f = "p0"
        for _ in range(d):
            f = f"G[0,{w}] ({f})"
        write("depth", d, [f], [trace_line([[True]] * n)] * 4, n=n, w=w, d=d)

    for n in [2 ** k for k in range(12, 16 if quick else 22)]:      # 4K .. 2M
        write("large-length", n, [big_formula(n, 1)], [structured_trace(rng, n) for _ in range(2)], n=n, copies=1)
    n = 2 ** (14 if quick else 18)
    traces = [structured_trace(rng, n) for _ in range(2)]
    for copies in [1, 2, 4, 8, 16, 32]:
        write("large-size", copies, [big_formula(n, copies)], traces, n=n, copies=copies)

    base = [l.strip() for l in LIBMLTL_FORMULAS.read_text().splitlines() if l.strip()]
    for n in [2 ** k for k in range(2, 10 if quick else 13)]:        # 4 .. 4096
        formulas = [re.sub(r"\[0,\d+\]", f"[0,{n // 2}]", f) for f in base]
        write("libmltl", n, formulas, random_traces(rng, 64, n, 4), n=n)


if __name__ == "__main__":
    main(quick="--quick" in sys.argv)
