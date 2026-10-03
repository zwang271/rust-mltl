# Benchmarks

Timing experiments for the two verified MLTL evaluators of `mltl-eval`
(top-down `mltl_eval`, bottom-up `mltl_eval_bottom_up`) and, for reference,
[libmltl](https://github.com/lmarzen/libmltl) (submodule `external/libmltl`)
and the Rust monitor of [R2U2](https://github.com/R2U2/r2u2) (submodule
`external/r2u2`). The algorithms and their complexity are explained in
`../EVAL_MLTL.md`; these experiments measure them.

## Running

```bash
git submodule update --init external/libmltl external/r2u2   # once, from the repo root
cd src/mltl-eval/benchmarks
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt
.venv/bin/python run.py          # full run (~13 minutes on an M-series Mac); --quick for a smoke test,
                                 # --only exp1,exp2 for a subset
.venv/bin/python plot.py         # writes plots/*.png and prints growth exponents
```

`run.py` generates the workloads (`gen_workloads.py`), builds the drivers,
times every evaluator on every workload, and writes `results/*.csv`.
Timings cover evaluation only: formulas are parsed (and, for R2U2, compiled
by C2PO, about 0.4 s per formula) before timing starts, and R2U2's monitor
re-initialisation between traces is not timed. All
evaluators read the same input files, so their answers can be compared. The
two verified evaluators must always agree (checked); a circled point marks
where libmltl's answer differs from the AFP semantics.

## Experiments

| Plot | What varies | What it shows |
|---|---|---|
| `length-periodic` | trace length n, intervals [0, n/4]; witnesses appear late in each window | bottom-up grows linearly in n; top-down and libmltl quadratically |
| `length-random` | the same, on random traces | early exits make every evaluator roughly linear here |
| `width` | interval width w at fixed n | bottom-up linear in w, the others quadratic |
| `depth` | nesting depth d of G[0,8] ... G[0,8] p | top-down and libmltl exponential in d, bottom-up near-linear |
| `libmltl` | libmltl's own benchmark (its formulas, bounds [0, n/2]); R2U2 not run | random workload; libmltl differs from AFP on short traces |
| `large-length` | a ~45-node formula (G[0, n−c] over 7 clauses, windows ≤ 32) on traces of up to 2M steps; traces make every clause hold everywhere, so nobody can stop early | heavy, realistic load: all four linear, bottom-up fastest |
| `large-size` | n = 2¹⁸, 1 to 32 copies of the clause group (up to ~1,400 nodes) | growth in formula size |

Each plot's legend gives an empirical growth exponent: the slope of a
least-squares fit through the upper half of the points on log-log axes
(1 = linear, 2 = quadratic).

## Results (2026-10-03, Apple M-series laptop)

Growth exponents fitted on log-log axes:

| Experiment | top-down | bottom-up | libmltl | R2U2 |
|---|---|---|---|---|
| length, late witnesses | 1.99 | **1.04** | 1.97 | **1.00** |
| length, random traces | 1.03 | 1.25 | 1.14 | 1.02 |
| width | 1.97 | **0.99** | 1.95 | **0.98** |
| libmltl workload | 1.78 | 1.12 | 1.88 | — |
| heavy formula, length | 1.01 | 0.98 | 1.00 | 1.00 |
| heavy formula, size | 1.22 | 0.98 | 1.21 | 0.89 |

Time per evaluation at the largest point:

| Experiment | top-down | bottom-up | libmltl | R2U2 |
|---|---|---|---|---|
| length, late witnesses (n = 16384) | 59.8 ms | **98 µs** | 11.4 ms | 321 µs |
| length, random (n = 16384) | 47 µs | 158 µs | **25 µs** | 167 µs |
| width (w = 2048) | 14.9 ms | **50 µs** | 3.0 ms | 154 µs |
| depth (d = 7) | 35.8 ms | **1.2 µs** | 6.8 ms | 1.9 µs |
| libmltl workload (n = 4096) | 130 µs | **71 µs** | 212 µs | — |
| heavy formula (n = 2²¹ ≈ 2M) | 4.44 s | **0.51 s** | 1.36 s | 1.29 s |
| heavy formula ×32 (n = 2¹⁸) | 25.7 s | **2.03 s** | 7.57 s | 2.98 s |

- **Heavy, realistic formulas.** With fixed windows every evaluator is linear
  in n, so the difference is the constant factor. Bottom-up is about 2.6×
  faster than libmltl and R2U2 and 8.8× faster than top-down at 2M steps.
  Growing the formula 32-fold costs bottom-up exactly 32×. Top-down and
  libmltl grow faster (exponent ≈ 1.2), because the shifted copies also have
  wider windows, which multiply their per-position cost. R2U2 grows a little
  slower than linear (0.89), plausibly because its compiler shares common
  subformulas across copies.
- **Bottom-up is linear wherever the work is.** With late witnesses it is
  about 600× faster than top-down and 115× faster than libmltl at
  n = 16384.
- **R2U2 is also linear.** Like bottom-up, it never re-evaluates a subformula
  at the same time step. It is about 3× slower than bottom-up here. It is
  measured on stepping alone: monitor re-initialisation between traces is
  excluded.
- **On random traces early exits are cheap,** so top-down and libmltl are
  roughly linear too, with smaller constants. Bottom-up's exponent of 1.25 is
  not algorithmic. It does the same amount of work on random and periodic
  traces (same formulas, same horizons), but random data costs more per entry
  at large n. The likely causes are branch mispredictions and tables
  outgrowing the CPU caches; this has not been measured separately.
- **On libmltl's own workload, bottom-up overtakes both from n ≈ 2048.**
  libmltl's answers differ from the AFP semantics at n = 4, 8 and 16, where
  formula windows extend past the end of the trace.
- **R2U2 agreed with the AFP semantics on every workload it ran.** It is
  omitted from the libmltl workload: most of those formulas contain `true`
  or `false`, and constant operands make R2U2's monitor loop forever (an
  R2U2 bug). In general R2U2 also emits no verdict when a window extends
  past the end of the trace (no end-of-trace handling). None of our
  workloads hit that case.

## Files

- `gen_workloads.py`: deterministic workload generator.
- `driver.rs`: driver for the Rust evaluators (built as the cargo example
  `bench_driver`). Its formula parser is unverified benchmark scaffolding.
- `libmltl_driver.cc`: the same driver for libmltl.
- `r2u2_driver/`: the same driver for R2U2's Rust monitor (separate crate on
  R2U2's pinned toolchain; formulas are compiled by R2U2's C2PO). It works
  around an R2U2 bug where `Monitor::reset` does not clear the temporal-logic
  instruction count.
- `run.py`, `plot.py`: run everything; plot results.

Agent context: agent-docs/modules/mltl-eval.md,
agent-docs/project/plan.md (M10).
