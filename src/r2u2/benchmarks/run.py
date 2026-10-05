#!/usr/bin/env python3
"""Benchmark the verified monitor (src/r2u2) against R2U2's r2u2_core.

Usage: R2U2_ROOT=<path to the r2u2 repo> python3 run.py [steps]
Builds both drivers, compiles each formula with C2PO (default options, as
shipped), runs both on the same random trace, compares the step-by-step
verdicts, prints a table (and writes results/results.tsv).
"""
import os, random, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
R2U2 = Path(os.environ.get("R2U2_ROOT", "")).resolve()
STEPS = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
ATOMS = 3

# ---- formulas: (name, tree); trees: ('p',i) ('!',x) ('&',x,y) ('|',x,y) ('F'|'G',a,b,x) ('U'|'R',x,a,b,y)
def afp(t):
    k = t[0]
    if k == 'p': return f"p{t[1]}"
    if k == '!': return f"!({afp(t[1])})"
    if k in '&|': return f"({afp(t[1])} {k} {afp(t[2])})"
    if k in 'FG': return f"{k}[{t[1]},{t[2]}]({afp(t[3])})"
    return f"({afp(t[1])} {k}[{t[2]},{t[3]}] {afp(t[4])})"
def c2po(t):
    k = t[0]
    if k == 'p': return f"s{t[1]}"
    if k == '!': return f"!({c2po(t[1])})"
    if k in '&|': return f"(({c2po(t[1])}) {k*2} ({c2po(t[2])}))"
    if k in 'FG': return f"{k}[{t[1]},{t[2]}]({c2po(t[3])})"
    return f"(({c2po(t[1])}) {k}[{t[2]},{t[3]}] ({c2po(t[4])}))"
def rand_tree(r, d, mb):
    if d == 0 or r.random() < 0.15: return ('p', r.randrange(ATOMS))
    k = r.choice('!&|FGUUR')
    a = r.randint(0, mb); b = a + r.randint(0, mb)
    if k == '!': return ('!', rand_tree(r, d-1, mb))
    if k in '&|': return (k, rand_tree(r, d-1, mb), rand_tree(r, d-1, mb))
    if k in 'FG': return (k, a, b, rand_tree(r, d-1, mb))
    return (k, rand_tree(r, d-1, mb), a, b, rand_tree(r, d-1, mb))
P = lambda i: ('p', i)
FORMULAS = [
    ("atom", P(0)),
    ("response G[0,10](!p0 | F[0,5] p1)", ('G', 0, 10, ('|', ('!', P(0)), ('F', 0, 5, P(1))))),
    ("until p0 U[0,20] p1", ('U', P(0), 0, 20, P(1))),
    ("nested G[0,5](!p0 | (p1 U[2,8] p2))", ('G', 0, 5, ('|', ('!', P(0)), ('U', P(1), 2, 8, P(2))))),
    ("wide F[0,100] p0 & G[0,100] p1", ('&', ('F', 0, 100, P(0)), ('G', 0, 100, P(1)))),
]
r = random.Random(1)
for i in range(10):
    FORMULAS.append((f"random{i} (depth 4)", rand_tree(r, 4, 5)))

def sh(cmd, **kw):
    p = subprocess.run(cmd, capture_output=True, text=True, **kw)
    if p.returncode != 0:
        raise RuntimeError(f"{cmd}\n{p.stdout}\n{p.stderr}")
    return p.stdout

def main():
    assert (R2U2 / "monitors/rust/r2u2_core").is_dir(), "set R2U2_ROOT"
    sh(["cargo", "build", "--release", "-p", "r2u2", "--example", "r2u2_bench"], cwd=REPO)
    ours = REPO / "target/release/examples/r2u2_bench"
    build = HERE / "build"; build.mkdir(exist_ok=True)
    d = build / "r2u2_core_driver"; (d / "src").mkdir(parents=True, exist_ok=True)
    (d / "Cargo.toml").write_text(f'''[package]
name = "driver"
version = "0.1.0"
edition = "2021"
[workspace]
[dependencies]
r2u2_core = {{ path = "{R2U2 / 'monitors/rust/r2u2_core'}" }}
[profile.release]
debug = false
''')
    (d / "src/main.rs").write_text((HERE / "r2u2_core_driver/main.rs").read_text())
    sh(["cargo", "+1.85.1", "build", "--release"], cwd=d)
    theirs = d / "target/release/driver"
    rr = random.Random(7)
    trace = build / "trace.txt"
    trace.write_text("".join("".join(rr.choice("01") for _ in range(ATOMS)) + "\n" for _ in range(STEPS)))
    (build / "atoms.map").write_text("".join(f"s{i}:{i}\n" for i in range(ATOMS)))
    rows = []
    for name, t in FORMULAS:
        spec = build / "spec.bin"; c = build / "spec.c2po"
        c.write_text(f"INPUT\n    {','.join(f's{i}' for i in range(ATOMS))}: bool;\n\nFTSPEC\n    {c2po(t)};\n")
        try:
            sh(["python3", str(R2U2 / "compiler/c2po.py"), "--impl", "rust", "-q", "--map", str(build / "atoms.map"),
                "-o", str(spec), str(c)])
        except RuntimeError as e:
            rows.append((name, None, None, f"c2po failed")); continue
        o1, o2 = build / "ours.out", build / "theirs.out"
        a = sh([str(ours), afp(t), str(trace), str(o1)]).split()
        b = sh([str(theirs), str(spec), str(trace), str(o2)]).split()
        v1, v2 = o1.read_text().split(), o2.read_text().split()
        n = min(len(v1), len(v2))
        diff = sum(1 for i in range(n) if v1[i] != v2[i])
        rows.append((name, int(a[0]), int(b[0]), f"covered {len(v1)}/{len(v2)}, {diff} differ"))
    out = HERE / "results"; out.mkdir(exist_ok=True)
    with open(out / "results.tsv", "w") as f:
        f.write(f"# steps={STEPS} atoms={ATOMS}\nformula\tours_us\tr2u2_core_us\tratio\tnote\n")
        print(f"{'formula':45} {'ours ms':>9} {'r2u2 ms':>9} {'ours/r2u2':>9}  check")
        for name, x, y, note in rows:
            ratio = f"{x / y:.1f}" if x and y else "-"
            print(f"{name:45} {x / 1000 if x else 0:9.1f} {y / 1000 if y else 0:9.1f} {ratio:>9}  {note}")
            f.write(f"{name}\t{x}\t{y}\t{ratio}\t{note}\n")

if __name__ == "__main__":
    main()
