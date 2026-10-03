"""Build the drivers, run every workload, and write results/<experiment>.csv.

  python run.py [--quick] [--min-seconds S] [--budget S] [--only exp1,exp2] [--impls a,b]

Each (workload, evaluator) point is timed by repeating the full workload
until at least --min-seconds have passed. Once an evaluator needs more than
--budget seconds for one pass at some point of an experiment, its larger
points are skipped (it has left the plot's range).

Results of the two verified evaluators must agree everywhere (checked).
libmltl implements MLTL incorrectly on short traces, and R2U2 (an online
monitor without an end-of-trace flush) leaves some short-trace verdicts
undecided, so their answers are only compared, never required to match; the
`agrees` column records the outcome, `undecided` counts R2U2's missing
verdicts.

R2U2 needs each formula compiled by C2PO (external/r2u2/compiler) into a
spec binary; these are cached next to the workload (specs/), keyed by a hash
of formulas.txt.
"""
import csv, hashlib, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
LIB = REPO / "external/libmltl"
BUILD = ROOT / "build"
RESULTS = ROOT / "results"
RUST_DRIVER = REPO / "target/release/examples/bench_driver"
CPP_DRIVER = BUILD / "libmltl_driver"
R2U2 = REPO / "external/r2u2"
R2U2_DIR = ROOT / "r2u2_driver"
R2U2_DRIVER = R2U2_DIR / "target/release/r2u2_driver"
R2U2_QUEUE_SLOTS = "1048576"         # compile-time SCQ arena size of the R2U2 monitor
R2U2_TL_INSTRUCTIONS = "8192"        # compile-time instruction-table size (large-size needs ~1.5k)
EVALUATORS = ["topdown", "bottomup", "libmltl", "r2u2"]


def build():
    subprocess.run(["cargo", "build", "--release", "-q", "--example", "bench_driver"], cwd=REPO, check=True)
    BUILD.mkdir(exist_ok=True)
    # Flags follow libmltl's own Makefile (-O2 -DNDEBUG -fno-rtti -flto).
    subprocess.run(["g++", "-std=c++17", "-O2", "-DNDEBUG", "-fno-rtti", "-flto", f"-I{LIB}/include",
                    str(ROOT / "libmltl_driver.cc"), str(LIB / "src/ast.cc"), str(LIB / "src/parser.cc"),
                    "-o", str(CPP_DRIVER)], check=True)
    # R2U2's memory bounds are compile-time constants read from the environment.
    env = dict(os.environ, R2U2_MAX_QUEUE_SLOTS=R2U2_QUEUE_SLOTS, R2U2_MAX_TL_INSTRUCTIONS=R2U2_TL_INSTRUCTIONS)
    # const_env reads the bounds at compile time; cargo does not track them, so rebuild.
    subprocess.run(["cargo", "clean", "--release", "-q", "-p", "r2u2_core"], cwd=R2U2_DIR, env=env, check=True)
    subprocess.run(["cargo", "build", "--release", "-q"], cwd=R2U2_DIR, env=env, check=True)


def compile_specs(d):
    """C2PO-compile every formula of workload `d` into d/specs/<i>.bin (cached)."""
    text = (d / "formulas.txt").read_text()
    key = hashlib.sha256(text.encode()).hexdigest()
    specs = d / "specs"
    if (specs / "KEY").exists() and (specs / "KEY").read_text() == key:
        return specs
    specs.mkdir(exist_ok=True)
    formulas = [l for l in text.splitlines() if l.strip()]

    def one(i):
        src = specs / f"{i}.mltl"
        src.write_text(re.sub(r"p(\d+)", r"a\1", formulas[i]) + "\n")   # C2PO's MLTL format names atoms a<N>
        out = specs / f"{i}.bin"
        out.unlink(missing_ok=True)
        (specs / f"{i}.const").unlink(missing_ok=True)
        # C2PO rejects constant formulas (also ones its rewrites reduce to a constant);
        # those get no .bin and the driver reports them as unsupported.
        subprocess.run([sys.executable, str(R2U2 / "compiler/c2po.py"), "-q", "--spec", str(src),
                        "--output", str(out)], capture_output=True)
        if not out.exists():
            return
        # R2U2 bug: some constant ("direct") operands make `monitor_step` loop
        # forever (check_operand_data returns a fresh verdict on every engine
        # re-loop). Detect empirically with a short trial run; exclude hangers.
        # The hang happens within the first steps, so a 256-step prefix of one
        # trace is enough (full traces can take longer than the timeout).
        trial = specs / f"trial{i}"
        trial.mkdir(exist_ok=True)
        (trial / "COUNT").write_text("1")
        (trial / "0.bin").write_bytes(out.read_bytes())
        first = (d / "traces.txt").open().readline().split()[:256]
        (trial / "trace.txt").write_text(" ".join(first) + "\n")
        try:
            subprocess.run([str(R2U2_DRIVER), str(trial), str(trial / "trace.txt"), "0"],
                           capture_output=True, timeout=1.5)
        except subprocess.TimeoutExpired:
            out.unlink()
            (specs / f"{i}.const").write_text("")
        finally:
            for f in trial.iterdir():
                f.unlink()
            trial.rmdir()

    with ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
        list(pool.map(one, range(len(formulas))))
    (specs / "COUNT").write_text(str(len(formulas)))
    (specs / "CONST").write_text(str(len(list(specs.glob("*.const")))))
    (specs / "KEY").write_text(key)
    return specs


def run_point(evaluator, d, min_s):
    f, t = str(d / "formulas.txt"), str(d / "traces.txt")
    if evaluator == "libmltl":
        cmd = [str(CPP_DRIVER), f, t, str(min_s)]
    elif evaluator == "r2u2":
        cmd = [str(R2U2_DRIVER), str(compile_specs(d)), t, str(min_s)]
    else:
        cmd = [str(RUST_DRIVER), evaluator, f, t, str(min_s)]
    proc = subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=1800)
    name, nf, nt, reps, total, ns, trues, h = proc.stdout.strip().split(",")
    extra = dict(re.findall(r"(\w+)=(\w+)", proc.stderr))
    if extra.get("overflow") == "true":
        raise RuntimeError(f"R2U2 SCQ overflow on {d}; raise R2U2_QUEUE_SLOTS")
    return dict(evaluator=name, formulas=int(nf), traces=int(nt), reps=int(reps), total_s=float(total),
                ns_per_eval=float(ns), trues=int(trues), hash=h, undecided=int(extra.get("undecided", 0)),
                unsupported=int(extra.get("unsupported", 0)),
                constant_operand=int((d / "specs/CONST").read_text()) if evaluator == "r2u2" else 0)


def main():
    args = sys.argv[1:]
    quick = "--quick" in args
    min_s = float(args[args.index("--min-seconds") + 1]) if "--min-seconds" in args else (0.05 if quick else 0.3)
    budget = float(args[args.index("--budget") + 1]) if "--budget" in args else (5.0 if quick else 30.0)
    import gen_workloads
    gen_workloads.main(quick=quick)
    build()
    RESULTS.mkdir(exist_ok=True)
    only = args[args.index("--only") + 1].split(",") if "--only" in args else None
    evaluators = args[args.index("--impls") + 1].split(",") if "--impls" in args else EVALUATORS
    for exp_dir in sorted((ROOT / "workloads").iterdir()):
        if only and exp_dir.name not in only:
            continue
        rows, skipped = [], set()
        points = sorted(exp_dir.iterdir(), key=lambda p: int(p.name))
        for d in points:
            meta = json.loads((d / "meta.json").read_text())
            ref = None
            for ev in evaluators:
                if ev in skipped:
                    continue
                # R2U2 hangs on most of libmltl's formulas (constant operands, an R2U2
                # bug), so it is benchmarked only on our own constant-free workloads.
                if ev == "r2u2" and exp_dir.name == "libmltl":
                    continue
                r = run_point(ev, d, min_s)
                if ref is None:
                    ref = r
                agrees = r["hash"] == ref["hash"]
                if ev in ("bottomup", "proto-hash", "proto-bits", "proto-masks"):
                    assert agrees, f"{ev} disagrees with top-down on {d}"
                if ev == "r2u2" and r["undecided"] == 0 and r["unsupported"] == 0 and not agrees:
                    print(f"  note: R2U2 decided every verdict on {d} but disagrees with AFP", flush=True)
                rows.append(dict(meta, **r, agrees=agrees))
                per_pass = r["total_s"] / r["reps"]
                print(f"{exp_dir.name:16} {d.name:>6} {ev:9} {r['ns_per_eval']:14.1f} ns/eval  pass {per_pass:7.3f}s"
                      f"{'' if agrees else '  (differs from top-down)'}"
                      f"{'  undecided=' + str(r['undecided']) if r['undecided'] else ''}"
                      f"{'  unsupported=' + str(r['unsupported']) if r['unsupported'] else ''}", flush=True)
                if per_pass > budget:
                    skipped.add(ev)
        with open(RESULTS / f"{exp_dir.name}.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)


if __name__ == "__main__":
    t0 = time.time()
    main()
    print(f"done in {time.time() - t0:.0f}s")
