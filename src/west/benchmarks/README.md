# WEST benchmarks

Compares four WEST implementations on upstream WEST's own benchmark
formulas: the verified fast version ([`fast_reg_checked`](../src/api.rs#L40)),
the verified faithful port ([`simp_pad_WEST_reg`](../src/exec.rs#L1359)),
and upstream WEST's Rust and C++ (bitset) versions.

## Result (hard sets, 30 formulas per file, 10 s limit per formula)

Upstream's harder datasets vary nesting depth (`d`), number of atoms (`n`)
and largest interval bound (`m`). "Done" counts formulas finished in 10 s.
The time is the total over formulas that *all four* finished. "×" is how
many times slower than the fast version, as a geometric mean over those
formulas.

| set | fast: done, time | faithful | upstream Rust | upstream C++ |
|---|---|---|---|---|
| d=3 | 30, 0.022 s | 30, 3.9 s, ×7 | 30, 7.6 s, ×2.8 | 30, 7.6 s, ×5.1 |
| d=5 | 21, 0.006 s | 20, ×11 | 17, ×4.5 | 20, ×4.5 |
| d=6 | 19, 0.004 s | 14, ×8.5 | 16, ×2.9 | 15, ×2.4 |
| m=20 | 27, 0.009 s | 26, 10.8 s, ×11 | 26, 0.6 s, ×3.5 | 26, 1.0 s, ×4.9 |
| m=40 | 23 | 19, ×10 | 21, ×1.8 | 11, ×2.2 |
| n=5 | 30, 0.39 s | 30, 4.2 s, ×9 | 29, 4.0 s, ×2.9 | 30, 5.8 s, ×3.7 |
| n=7 | 29, 0.12 s | 28, 3.3 s, ×8.6 | 28, 0.8 s, ×3.4 | 26, 0.2 s, ×3.1 |

All sets: [`results/hard/summary.txt`](results/hard/summary.txt). The
fast version finishes the most formulas in every set. The formulas nobody
finishes have regex lists that grow to millions of pairs inside one
operator; that comes from the algorithm, not the implementation. Upstream
Rust sometimes returns no regexes for satisfiable formulas (a bug, so some
of its times are too good). Upstream C++ only handles formulas up to 512
bits.

## Why the fast version is faster

Not because it does less: it returns the same number of regexes as
upstream C++ on 300 of the 349 formulas both finish.

The cause is **simplification order**. Simplifying a list of regexes means
merging any two that differ in one place, until no pair merges. Upstream
WEST (C++ and Rust) and the Isabelle algorithm restart the pair scan from
the first pair after *every* merge. That repeats an all-pairs scan once per
merge, so a list of a few thousand regexes costs billions of comparisons.
The fast version finishes its pass and only repeats a pass that merged
something.

To show this, [`ablation/`](ablation/) holds copies of the prototype
[`proto.rs`](proto.rs) that each change one design choice to upstream's,
and nothing else:

| variant | what changes | finished (of 450) | total time where both finish | worst case |
|---|---|---|---|---|
| [`restart.rs`](ablation/restart.rs) | restart the pair scan after every merge | 383 (vs 397) | 1.40 s → 30.3 s (×22) | 5 ms → 3.4 s (×692) |
| [`quad.rs`](ablation/quad.rs) | U and R rebuild `G[a,k]` at every step | 396 | 16.1 s → 20.9 s (×1.3) | |
| [`toplen.rs`](ablation/toplen.rs) | every regex has the full formula's length from the start | 397 | 22.35 s → 22.52 s (×1.0) | |

So restarting is the main cost: typical formulas lose only about 1.5×
(geometric mean), but formulas whose lists grow large lose 100–700×, and
14 formulas no longer finish in 10 s. Rebuilding `G[a,k]` costs a little
on the heaviest formulas; the regex length makes no difference. Upstream's
C++ adds copying on top: its `simplify` restarts by a recursive call that
copies the whole list each time.

The two orders also reach different final lists. Neither is smaller in
general: restarting gives fewer regexes on 14 formulas and more on 16, and
the same on the other 353.

All four variants are checked on every short trace against the verified
evaluator ([`tests/proto.rs`](../tests/proto.rs)), so the comparison is
between correct implementations. Per-set figures:
[`results/hard/summary_ablation.txt`](results/hard/summary_ablation.txt).

## Running

Needs a clone of [upstream WEST](https://github.com/zwang271/WEST) named
by `WEST_UPSTREAM` and a C++ compiler:

```
WEST_UPSTREAM=/path/to/WEST python3 run.py --hard --limit 30 --timeout 10
python3 summarize.py results/hard
```

The ablation: `run.py --hard --limit 30 --timeout 10 --impls
proto,proto_restart,proto_toplen,proto_quad`, then `summarize.py
results/hard proto,proto_restart,proto_toplen,proto_quad --sizes`.

[`run.py`](run.py) builds everything and writes [`results/`](results/);
[`summarize.py`](summarize.py) prints the table. Drivers:
[`driver.rs`](driver.rs) (ours), [`upstream_rust.rs`](upstream_rust.rs),
[`upstream_cpp.cc`](upstream_cpp.cc). [`proto.rs`](proto.rs) is the
unverified prototype the fast version was designed from; the verified
version runs at the same speed.
