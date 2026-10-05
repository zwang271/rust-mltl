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

## Running

Needs a clone of [upstream WEST](https://github.com/zwang271/WEST) named
by `WEST_UPSTREAM` and a C++ compiler:

```
WEST_UPSTREAM=/path/to/WEST python3 run.py --hard --limit 30 --timeout 10
python3 summarize.py results/hard
```

[`run.py`](run.py) builds everything and writes [`results/`](results/);
[`summarize.py`](summarize.py) prints the table. Drivers:
[`driver.rs`](driver.rs) (ours), [`upstream_rust.rs`](upstream_rust.rs),
[`upstream_cpp.cc`](upstream_cpp.cc). [`proto.rs`](proto.rs) is the
unverified prototype the fast version was designed from; the verified
version runs at the same speed.
