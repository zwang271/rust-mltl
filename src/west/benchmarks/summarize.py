#!/usr/bin/env python3
"""Summarize results/ (or results/hard/): per dataset file, how many
formulas each implementation finished within the timeout, and on the
formulas *all* listed implementations finished, total time and the
geometric-mean speedup of each over the first one.
Usage: summarize.py [results-dir] [impl,impl,...]"""
import math, pathlib, sys

here = pathlib.Path(__file__).resolve().parent
res = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else here / "results"
impls = sys.argv[2].split(",") if len(sys.argv) > 2 else ["fast", "faithful", "upstream_rust", "upstream_cpp"]

def load(f):
    out = {}
    for line in f.read_text().splitlines():
        parts = line.split("\t")
        out[int(parts[0])] = None if parts[1] in ("timeout", "skip") else (int(parts[1]), int(parts[2]))
    return out

print(f"{'set':10} " + " ".join(f"{i:>22}" for i in impls))
for d in sorted(p for p in res.iterdir() if p.is_dir() and p.name in "dnm"):
    for stem in sorted({f.name.split(".")[0] for f in d.glob("*.tsv")}, key=int):
        data = {}
        for i in impls:
            f = d / f"{stem}.{i}.tsv"
            if f.exists():
                data[i] = load(f)
        if len(data) < len(impls):
            continue
        idx = set.intersection(*(set(v) for v in data.values()))
        common = [k for k in idx if all(data[i][k] is not None for i in impls)]
        cells = []
        for i in impls:
            solved = sum(1 for k in idx if data[i][k] is not None)
            t = sum(data[i][k][0] for k in common) / 1e6
            if i == impls[0] or not common:
                cells.append(f"{solved:3d} ok {t:8.3f}s")
            else:
                gm = math.exp(sum(math.log(max(data[i][k][0], 1) / max(data[impls[0]][k][0], 1)) for k in common) / len(common))
                cells.append(f"{solved:3d} ok {t:7.3f}s x{gm:6.1f}")
        print(f"{d.name}={stem:7} " + " ".join(f"{c:>22}" for c in cells) + f"   (common: {len(common)})")
