"""Build the drivers, run every workload, and write results/<experiment>.csv.

  python3 run.py [--quick] [--min-seconds S] [--budget S] [--only exp1,exp2]

Implementations (all on the same input files):
  rust       verified `prog` (this crate), system allocator
  rust-mi    the same code, driver linked with mimalloc
  haskell    `prog` exported from Isabelle (ROOT/formula_progression_api/
             codegen/formula_progression.hs, unchanged), ghc -O2
Modes: `prog` (whole trace at once) everywhere; `prog-step` (one state at a
time, as the deployed API does) on the `length` experiment.

Each point repeats the whole workload until --min-seconds have passed and
reports time per (formula, trace) pair. Answers must agree: every driver
hashes its result formulas, and the hashes are compared (assertion).

Experiment `api` times the deployed API binary itself (`run_prog`, built
from the same codegen directory), one process per request with its own
input format, on the `length` workloads; it is compared with the in-process
`prog-step` of `rust`.
"""
import csv, json, os, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
CODEGEN = Path(os.environ["FP_CODEGEN"]) if "FP_CODEGEN" in os.environ else None  # .../formula_progression_api/codegen
BUILD = ROOT / "build"
RESULTS = ROOT / "results"
RUST = REPO / "target/release/examples/fp_bench"
RUST_MI = REPO / "target/mimalloc/release/examples/fp_bench"
HS = BUILD / "fp_hs"
RUN_PROG = BUILD / "run_prog"
IMPLS = {"rust": RUST, "rust-mi": RUST_MI, "haskell": HS}


def build():
    if CODEGEN is None or not (CODEGEN / "formula_progression.hs").is_file():
        sys.exit("set FP_CODEGEN to the formula_progression_api/codegen directory of the MLTL_R2U2- repo")
    cargo = ["cargo", "build", "--release", "-q", "--example", "fp_bench", "-p", "formula_progression"]
    subprocess.run(cargo, cwd=REPO, check=True)
    subprocess.run(cargo + ["--target-dir", "target/mimalloc"], cwd=REPO, check=True,
                   env=dict(os.environ, RUSTFLAGS="--cfg fp_bench_mimalloc"))
    for name, src, extra in [("fp_hs", ROOT / "driver.hs", ["-fno-full-laziness"]),
                             ("run_prog", CODEGEN / "run_prog.hs", [])]:
        out = BUILD / ("hs-" + name)
        out.mkdir(parents=True, exist_ok=True)
        subprocess.run(["ghc", "-O2", *extra, f"-i{CODEGEN}", "-outputdir", str(out), "-o", str(BUILD / name),
                        str(src)], check=True, capture_output=True)


def run_point(impl, mode, d, min_s):
    cmd = [str(IMPLS[impl]), mode, str(d / "formulas.txt"), str(d / "traces.txt"), str(min_s)]
    out = subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=3600).stdout.strip()
    name, nf, nt, reps, total, ns, h = out.split(",")
    return dict(impl=impl, mode=mode, formulas=int(nf), traces=int(nt), reps=int(reps),
                total_s=float(total), ns_per_call=float(ns), hash=h)


# --- deployed API binary: its input is Haskell `read` syntax -------------------
def hs_nat(k):
    return "Zero_nat" if k == 0 else "(Suc " * k + "Zero_nat" + ")" * k


def hs_formula(tokens):
    t = tokens.pop(0)
    if t == "true": return "True_mltl"
    if t == "false": return "False_mltl"
    if t.startswith("p"): return f"(Prop_mltl {hs_nat(int(t[1:]))})"
    if t == "!": return f"(Not_mltl {hs_formula(tokens)})"
    if t in "&|":
        a = hs_formula(tokens); b = hs_formula(tokens)
        return f"({'And_mltl' if t == '&' else 'Or_mltl'} {a} {b})"
    a, b = hs_nat(int(tokens.pop(0))), hs_nat(int(tokens.pop(0)))
    if t in "FG":
        return f"({'Future_mltl' if t == 'F' else 'Global_mltl'} {a} {b} {hs_formula(tokens)})"
    x = hs_formula(tokens); y = hs_formula(tokens)
    return f"({'Until_mltl' if t == 'U' else 'Release_mltl'} {x} {a} {b} {y})"


def hs_trace(line):
    steps = line.split()
    sets = ["Set [" + ",".join(hs_nat(i) for i, c in enumerate(s) if c == "1") + "]" for s in steps]
    return "[" + ",".join(sets) + "]"


def run_api(d, min_s):
    fs = [l for l in (d / "formulas.txt").read_text().splitlines() if l]
    ts = [l for l in (d / "traces.txt").read_text().splitlines() if l]
    inputs = [f"{hs_formula(f.split())}\n{hs_trace(t)}\n" for f in fs for t in ts]
    reps, t0 = 0, time.perf_counter()
    while True:
        for inp in inputs:
            subprocess.run([str(RUN_PROG)], input=inp, capture_output=True, text=True, check=True)
        reps += 1
        if time.perf_counter() - t0 >= min_s:
            break
    total = time.perf_counter() - t0
    return dict(impl="api-binary", mode="prog-step", formulas=len(fs), traces=len(ts), reps=reps,
                total_s=total, ns_per_call=total * 1e9 / (reps * len(inputs)), hash="")


def main():
    args = sys.argv[1:]
    quick = "--quick" in args
    min_s = float(args[args.index("--min-seconds") + 1]) if "--min-seconds" in args else (0.1 if quick else 0.5)
    budget = float(args[args.index("--budget") + 1]) if "--budget" in args else (5.0 if quick else 20.0)
    only = args[args.index("--only") + 1].split(",") if "--only" in args else None
    import gen_workloads
    gen_workloads.main(quick=quick)
    build()
    RESULTS.mkdir(exist_ok=True)
    plan = {"length": ["prog", "prog-step"], "width": ["prog"], "random": ["prog"]}
    for exp in ["length", "width", "random", "api"]:
        if only and exp not in only:
            continue
        rows, skipped = [], set()
        src = "length" if exp == "api" else exp
        for d in sorted((ROOT / "workloads" / src).iterdir(), key=lambda p: int(p.name)):
            meta = json.loads((d / "meta.json").read_text())
            jobs = ([("api-binary", "prog-step"), ("rust", "prog-step")] if exp == "api"
                    else [(i, m) for m in plan[exp] for i in IMPLS])
            ref = {}
            for impl, mode in jobs:
                if (impl, mode) in skipped:
                    continue
                r = run_api(d, min_s) if impl == "api-binary" else run_point(impl, mode, d, min_s)
                if r["hash"]:
                    assert ref.setdefault(mode, r["hash"]) == r["hash"], f"{impl} {mode} disagrees on {d}"
                rows.append(dict(meta, **r))
                per_pass = r["total_s"] / r["reps"]
                print(f"{exp:7} {d.name:>5} {impl:10} {mode:9} {r['ns_per_call'] / 1e3:12.2f} us/call", flush=True)
                if per_pass > budget:
                    skipped.add((impl, mode))
        with open(RESULTS / f"{exp}.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)


if __name__ == "__main__":
    t0 = time.time()
    main()
    print(f"done in {time.time() - t0:.0f}s")
