"""Plot results/*.csv to plots/*.png and print speedups and growth exponents.

  python3 plot.py      (needs matplotlib, numpy; e.g. the venv of
                        src/mltl-eval/benchmarks)
"""
import csv
from collections import defaultdict
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
LABEL = {"rust": "Rust (verified), system malloc", "rust-mi": "Rust (verified), mimalloc",
         "haskell": "Haskell (Isabelle export)", "api-binary": "deployed API binary, per request"}
XLABEL = {"length": "trace length n (bounds ≈ n)", "width": "window width w (n = 512)",
          "random": "trace length n", "api": "trace length n (bounds ≈ n)"}
COLOR = {"rust": "#2a6fdb", "rust-mi": "#12a37f", "haskell": "#d1495b", "api-binary": "#8a5a00"}


def exponent(xs, ys):
    k = len(xs) // 2
    return np.polyfit(np.log(xs[k:]), np.log(ys[k:]), 1)[0]


def main():
    (ROOT / "plots").mkdir(exist_ok=True)
    for f in sorted((ROOT / "results").glob("*.csv")):
        exp = f.stem
        series = defaultdict(list)
        for r in csv.DictReader(f.open()):
            series[(r["impl"], r["mode"])].append((int(r["param"]), float(r["ns_per_call"])))
        modes = sorted({m for _, m in series})
        fig, axes = plt.subplots(1, len(modes), figsize=(6.4 * len(modes), 4.6), squeeze=False)
        print(f"\n== {exp}")
        for ax, mode in zip(axes[0], modes):
            for (impl, m), pts in sorted(series.items()):
                if m != mode:
                    continue
                pts.sort()
                xs, ys = np.array([p for p, _ in pts]), np.array([t for _, t in pts]) / 1e3
                e = exponent(xs, ys) if len(xs) >= 4 else float("nan")
                ax.plot(xs, ys, "o-", color=COLOR[impl], label=f"{LABEL[impl]}  (slope {e:.2f})")
            ax.set_xscale("log", base=2)
            ax.set_yscale("log")
            ax.set_xlabel(XLABEL[exp])
            ax.set_ylabel("µs per (formula, trace)")
            ax.set_title(f"{exp}: {mode}")
            ax.grid(True, which="both", alpha=0.3)
            ax.legend(fontsize=8)
            # speedup table vs Haskell (or vs the API binary)
            base = "api-binary" if exp == "api" else "haskell"
            b = dict(series.get((base, mode), []))
            for impl in ["rust", "rust-mi"]:
                s = dict(series.get((impl, mode), []))
                common = sorted(set(b) & set(s))
                if common:
                    sp = [b[p] / s[p] for p in common]
                    print(f"  {mode:9} {impl:8} vs {base}: " +
                          "  ".join(f"{p}:{x:.2f}x" for p, x in zip(common, sp)))
        fig.tight_layout()
        fig.savefig(ROOT / "plots" / f"{exp}.png", dpi=130)
        plt.close(fig)


if __name__ == "__main__":
    main()
