#!/usr/bin/env python3
"""Differential test: verified WEST (this crate) vs Isabelle's Haskell export
of AFP WEST. Both must print identical regexes, since the exec code is
proved equal to the spec of WEST_Algorithms.thy.

Needs GHC and the export directory of `isabelle export` (env WEST_EXPORT,
see agent-docs/modules/west.md). Usage: run.py [count] [seed]."""
import os, pathlib, re, subprocess, sys

here = pathlib.Path(__file__).resolve().parent
build = here / "build"
build.mkdir(exist_ok=True)
export = pathlib.Path(os.environ["WEST_EXPORT"])
src = next(export.glob("**/WEST_simp_pad.hs"))
hs = src.read_text()
# The export hides constructors; expose them for the driver.
hs = re.sub(r"module WEST_simp_pad\([^)]*\)", "module WEST_simp_pad(Nat(..), Mltl(..), WEST_bit(..), wEST_reg, simp_pad_WEST_reg)", hs, count=1)
(build / "WEST_simp_pad.hs").write_text(hs)
(build / "driver.hs").write_text((here / "driver.hs").read_text())
subprocess.run(["ghc", "-O2", "-o", "isa_west", "driver.hs"], cwd=build, check=True, stdout=subprocess.DEVNULL)
subprocess.run(["cargo", "build", "--release", "-q", "-p", "west", "--example", "west_diff"], check=True)
root = here.parents[2]
rust_bin = root / "target" / "release" / "examples" / "west_diff"

count = int(sys.argv[1]) if len(sys.argv) > 1 else 500
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
total = 0
for (depth, atoms, maxb) in [(2, 2, 2), (3, 2, 2), (3, 3, 3), (4, 2, 2)]:
    formulas = subprocess.run([sys.executable, str(here / "gen.py"), str(count), str(seed), str(depth), str(atoms), str(maxb)],
                              check=True, capture_output=True, text=True).stdout
    isa = subprocess.run([str(build / "isa_west")], input=formulas, check=True, capture_output=True, text=True, timeout=3600).stdout.splitlines()
    rs = subprocess.run([str(rust_bin)], input=formulas, check=True, capture_output=True, text=True).stdout.splitlines()
    lines = formulas.splitlines()
    assert len(isa) == len(rs) == 2 * len(lines), (len(isa), len(rs), len(lines))
    for k, f in enumerate(lines):
        for j, name in enumerate(["WEST_reg", "simp_pad_WEST_reg"]):
            if isa[2 * k + j] != rs[2 * k + j]:
                print(f"MISMATCH {name} on {f}\n  isabelle: {isa[2*k+j]}\n  rust:     {rs[2*k+j]}")
                sys.exit(1)
    total += len(lines)
    print(f"depth {depth}, atoms {atoms}, bounds <= {maxb}: {len(lines)} formulas identical")
print(f"all {total} formulas: identical output (WEST_reg and simp_pad_WEST_reg)")
