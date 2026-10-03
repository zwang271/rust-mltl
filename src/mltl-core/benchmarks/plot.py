"""Plot benchmark results (results/*.csv) into plots/.

  python plot.py

For every experiment, plots time per evaluation against the experiment's
parameter on log-log axes (semi-log for the depth experiment), and reports
the empirical growth exponent of each evaluator: the slope of a least-squares
line through the upper half of its points. A slope of 1 is linear growth,
2 is quadratic.
"""
import csv
from collections import defaultdict
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent
RESULTS, PLOTS = ROOT / "results", ROOT / "plots"
STYLE = {
    "topdown": dict(label="top-down (verified)", color="#d62728", marker="o"),
    "bottomup": dict(label="bottom-up (verified)", color="#1f77b4", marker="s"),
    "libmltl": dict(label="libmltl", color="#7f7f7f", marker="^"),
    "r2u2": dict(label="R2U2 (Rust monitor)", color="#2ca02c", marker="D"),
}
EXPERIMENTS = {
    "length-periodic": ("Trace length (late witnesses)", "trace length n   (intervals [0, n/4])", "loglog"),
    "length-random": ("Trace length (random traces)", "trace length n   (intervals [0, n/4])", "loglog"),
    "width": ("Interval width", "interval width w   (n fixed)", "loglog"),
    "depth": ("Nesting depth: G[0,8] ... G[0,8] p", "nesting depth d", "semilogy"),
    "libmltl": ("libmltl's benchmark workload", "trace length n   (intervals [0, n/2])", "loglog"),
    "large-length": ("Heavy formula (~45 nodes), long traces", "trace length n", "loglog"),
    "large-size": ("Heavy formula, n = 2^18: formula size", "clause groups k   (~45 nodes each)", "loglog"),
}


def load(name):
    path = RESULTS / f"{name}.csv"
    if not path.exists():
        return None
    data = defaultdict(list)
    for r in csv.DictReader(path.open()):
        data[r["evaluator"]].append((float(r["param"]), float(r["ns_per_eval"]), r["agrees"] == "True"))
    return {k: sorted(v) for k, v in data.items()}


def slope(points):
    pts = [(x, y) for x, y, _ in points if x > 0 and y > 0]
    pts = pts[len(pts) // 2:]
    if len(pts) < 2:
        return None
    x, y = np.log(np.array(pts).T)
    return np.polyfit(x, y, 1)[0]


def draw(ax, name):
    title, xlabel, scale = EXPERIMENTS[name]
    data = load(name)
    if data is None:
        ax.set_visible(False)
        return
    for ev, style in STYLE.items():
        if ev not in data:
            continue
        xs, ys, ok = zip(*data[ev])
        label = style["label"]
        if scale == "loglog":
            s = slope(data[ev])
            if s is not None:
                label += f"   (slope {s:.2f})"
        ax.plot(xs, ys, color=style["color"], marker=style["marker"], ms=4, lw=1.5, label=label)
        bad = [(x, y) for x, y, a in data[ev] if not a]
        if bad:
            bx, by = zip(*bad)
            ax.scatter(bx, by, s=90, facecolors="none", edgecolors="black", zorder=5,
                       label="answer differs from AFP semantics")
    if scale == "loglog":
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
    else:
        ax.set_yscale("log")
    ax.set_title(title)
    ax.set_xlabel(xlabel)
    ax.set_ylabel("time per evaluation (ns)")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=8)


def main():
    PLOTS.mkdir(exist_ok=True)
    for name in EXPERIMENTS:
        fig, ax = plt.subplots(figsize=(6.4, 4.6))
        draw(ax, name)
        fig.tight_layout()
        fig.savefig(PLOTS / f"{name}.png", dpi=160)
        plt.close(fig)
    fig, axes = plt.subplots(3, 2, figsize=(12.8, 13.8))
    for ax, name in zip(axes.flat, ["length-periodic", "length-random", "width", "depth",
                                    "large-length", "large-size"]):
        draw(ax, name)
    fig.suptitle("MLTL evaluation: verified top-down and bottom-up vs. libmltl and R2U2")
    fig.tight_layout(rect=(0, 0, 1, 0.98))
    fig.savefig(PLOTS / "summary.png", dpi=160)
    plt.close(fig)
    for name in EXPERIMENTS:
        data = load(name)
        if data and EXPERIMENTS[name][2] == "loglog":
            print(name, {ev: (round(s, 2) if (s := slope(p)) is not None else None) for ev, p in data.items()})


if __name__ == "__main__":
    main()
