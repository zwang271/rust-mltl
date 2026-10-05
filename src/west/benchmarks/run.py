#!/usr/bin/env python3
"""WEST benchmarks: the verified faithful port, the fast prototype, and
upstream WEST's Rust and C++ implementations, on upstream's datasets
(experiments/benchmarking/{d,n,m}). Each implementation runs as one process
per dataset file; a formula that takes longer than --timeout seconds is
recorded as a timeout and the process is restarted after it.

Needs a local clone of https://github.com/zwang271/WEST (env WEST_UPSTREAM).
Usage: run.py [--impls faithful,fast,proto,upstream_rust,upstream_cpp]
              [--timeout 10] [--limit N] [--sets d,n,m] [--hard]
Writes results/<set>/<file>.<impl>.tsv and prints a summary."""
import argparse, os, pathlib, select, subprocess, sys, time

here = pathlib.Path(__file__).resolve().parent
root = here.parents[2]
build = here / "build"
upstream = pathlib.Path(os.environ["WEST_UPSTREAM"])

def build_all(impls):
    build.mkdir(exist_ok=True)
    bins = {}
    if {"faithful", "proto", "fast"} & set(impls):
        subprocess.run(["cargo", "build", "--release", "-q", "-p", "west", "--example", "west_bench"], cwd=root, check=True)
        b = root / "target/release/examples/west_bench"
        bins["faithful"] = [str(b), "faithful"]
        bins["proto"] = [str(b), "proto"]
        bins["fast"] = [str(b), "fast"]
    if "upstream_rust" in impls:
        proj = build / "upstream_rust"
        (proj / "src").mkdir(parents=True, exist_ok=True)
        (proj / "Cargo.toml").write_text(
            '[package]\nname = "upstream_rust_bench"\nversion = "0.1.0"\nedition = "2024"\n\n'
            f'[dependencies]\nwest_rust = {{ path = "{upstream / "src/west_rust"}" }}\n\n'
            '[profile.release]\nopt-level = 3\n\n[workspace]\n')
        (proj / "src/main.rs").write_text((here / "upstream_rust.rs").read_text())
        subprocess.run(["cargo", "build", "--release", "-q"], cwd=proj, check=True)
        bins["upstream_rust"] = [str(proj / "target/release/upstream_rust_bench")]
    if "upstream_cpp" in impls:
        src = upstream / "src/WEST"
        out = build / "upstream_cpp"
        subprocess.run(["c++", "-std=c++17", "-O2", "-I", str(src), str(here / "upstream_cpp.cc"),
                        str(src / "reg.cpp"), str(src / "utils.cpp"), str(src / "parser.cpp"), "-o", str(out)], check=True)
        bins["upstream_cpp"] = [str(out)]
    return bins

def run_file(cmd, path, n_lines, timeout):
    """Yields (index, microseconds | "timeout" | "skip", count). Reads the
    pipe unbuffered: a buffered reader would hold lines select() can't see."""
    start = 0
    while start < n_lines:
        p = subprocess.Popen(cmd + [str(path), str(start)], stdout=subprocess.PIPE, bufsize=0)
        fd = p.stdout.fileno()
        buf = b""
        nxt = start
        done = False
        while not done:
            while b"\n" in buf:
                line, buf = buf.split(b"\n", 1)
                parts = line.decode().split("\t")
                i = int(parts[0])
                yield (i, parts[1], parts[2] if len(parts) > 2 else "")
                nxt = i + 1
            deadline = time.monotonic() + timeout
            r, _, _ = select.select([fd], [], [], timeout)
            if not r:
                p.kill(); p.wait()
                yield (nxt, "timeout", "")
                start = nxt + 1
                break
            chunk = os.read(fd, 65536)
            if not chunk:
                p.wait()
                start = n_lines
                done = True
            buf += chunk

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--impls", default="faithful,fast,upstream_rust,upstream_cpp")
    ap.add_argument("--timeout", type=float, default=10.0)
    ap.add_argument("--limit", type=int, default=0, help="formulas per file (0 = all)")
    ap.add_argument("--sets", default="d,n,m")
    ap.add_argument("--hard", action="store_true",
                    help="use upstream's harder datasets (gen_formulas_hard.py, seed 2026; generated into build/)")
    a = ap.parse_args()
    impls = a.impls.split(",")
    bins = build_all(impls)
    data = upstream / "experiments/benchmarking"
    results = here / "results"
    if a.hard:
        gen = build / "gen"
        gen.mkdir(exist_ok=True)
        if not (gen / "hard").exists():
            env = dict(os.environ, PYTHONPATH=str(data))
            subprocess.run([sys.executable, str(data / "gen_formulas_hard.py")], cwd=gen, env=env, check=True, stdout=subprocess.DEVNULL)
        data = gen / "hard"
        results = here / "results" / "hard"
    for s in a.sets.split(","):
        files = sorted((data / s).glob("*.txt"), key=lambda p: int(p.stem))
        for f in files:
            lines = f.read_text().splitlines()
            if a.limit:
                lines = lines[:a.limit]
            tmp = build / f"{"hard_" if a.hard else ""}{s}_{f.stem}.txt"
            tmp.write_text("\n".join(lines) + "\n")
            (results / s).mkdir(parents=True, exist_ok=True)
            summary = []
            for impl in impls:
                rows = list(run_file(bins[impl], tmp, len(lines), a.timeout))
                (results / s / f"{f.stem}.{impl}.tsv").write_text("".join(f"{i}\t{t}\t{c}\n" for i, t, c in rows))
                done = [int(t) for _, t, _ in rows if t not in ("timeout", "skip")]
                tos = sum(1 for _, t, _ in rows if t == "timeout")
                skips = sum(1 for _, t, _ in rows if t == "skip")
                summary.append(f"{impl}: {sum(done)/1e6:.3f}s over {len(done)}" + (f", {tos} timeouts" if tos else "") + (f", {skips} skipped" if skips else ""))
            print(f"{s}={f.stem}: " + " | ".join(summary), flush=True)

if __name__ == "__main__":
    main()
