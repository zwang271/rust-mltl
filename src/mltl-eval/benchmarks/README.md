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

"Bit rows" is the same verified bottom-up algorithm reading atoms from a
bit-row trace instead of a set per step (see `../README.md`).

Growth exponents fitted on log-log axes:

| Experiment | top-down | bottom-up | bottom-up, bit rows | libmltl | R2U2 |
|---|---|---|---|---|---|
| length, late witnesses | 2.00 | 1.02 | **0.86** | 1.97 | 0.97 |
| length, random traces | 1.07 | 1.33 | 1.21 | 1.13 | 1.01 |
| width | 1.96 | 0.99 | **0.85** | 1.94 | 0.98 |
| libmltl workload | 1.74 | 1.05 | 0.93 | 1.86 | — |
| heavy formula, length | 1.00 | 0.98 | 0.94 | 1.00 | 1.00 |
| heavy formula, size | 1.23 | 1.02 | 0.97 | 1.21 | 0.90 |

Time per evaluation at the largest point:

| Experiment | top-down | bottom-up | bottom-up, bit rows | libmltl | R2U2 |
|---|---|---|---|---|---|
| length, late witnesses (n = 16384) | 60.1 ms | 94 µs | **25 µs** | 11.5 ms | 320 µs |
| length, random (n = 16384) | 54 µs | 190 µs | 59 µs | **30 µs** | 190 µs |
| width (w = 2048) | 14.9 ms | 49 µs | **12 µs** | 2.9 ms | 158 µs |
| depth (d = 7) | 36.2 ms | 1.3 µs | **1.0 µs** | 7.2 ms | 2.1 µs |
| libmltl workload (n = 4096) | 150 µs | 73 µs | **24 µs** | 220 µs | — |
| heavy formula (n = 2²¹ ≈ 2M) | 4.50 s | 485 ms | **141 ms** | 1.35 s | 1.28 s |
| heavy formula ×32 (n = 2¹⁸) | 26.4 s | 2.06 s | **0.66 s** | 7.54 s | 2.99 s |

- **The bit-row trace makes bottom-up 3–4× faster** wherever atoms are read
  often (1.1–1.5× on formulas with a single atom, such as the depth
  experiment). On the heavy formula it is now about 9× faster than libmltl
  and R2U2 and 32× faster than top-down. Converting a trace costs about
  0.1 s per million steps, once per trace. An unverified prototype of the
  same change reaches about 6×; the difference is in the verified code's
  table building, not in the trace format.
- **Heavy, realistic formulas.** With fixed windows every evaluator is linear
  in n, so the difference is the constant factor. Growing the formula
  32-fold costs bottom-up 32×. Top-down and libmltl grow faster (exponent
  ≈ 1.2), because the shifted copies also have wider windows, which multiply
  their per-position cost. R2U2 grows a little slower than linear (0.90),
  plausibly because its compiler shares common subformulas across copies.
- **Bottom-up is linear wherever the work is.** With late witnesses, at
  n = 16384, the bit-row version is about 2,400× faster than top-down and
  460× faster than libmltl. Exponents below 1 for the bit-row version mean
  its fixed per-call overhead is still a visible share at small sizes.
- **R2U2 is also linear.** Like bottom-up, it never re-evaluates a subformula
  at the same time step. It is measured on stepping alone: monitor
  re-initialisation between traces is excluded.
- **On random traces early exits are cheap,** so top-down and libmltl are
  roughly linear too, with small constants; libmltl stays fastest there.
  Bottom-up's exponent above 1 is not algorithmic. It does the same work on
  random and periodic traces, but random data costs more per entry at large
  n, likely from branch mispredictions and cache misses (not measured
  separately).
- **libmltl's answers differ from the AFP semantics** at n = 4, 8 and 16 of
  its own workload, where formula windows extend past the end of the trace.
- **R2U2 agreed with the AFP semantics on every workload it ran.** It is
  omitted from the libmltl workload: most of those formulas contain `true`
  or `false`, and constant operands make R2U2's monitor loop forever (an
  R2U2 bug). R2U2 also emits no verdict when a window extends past the end
  of the trace; none of our workloads hit that case.

## Files

- `gen_workloads.py`: deterministic workload generator.
- `driver.rs`: driver for the Rust evaluators (built as the cargo example
  `bench_driver`). Its formula parser is unverified benchmark scaffolding.
- `proto.rs`: unverified prototype used to try trace representations before
  proving them (`--impls proto-hash,proto-bits,proto-masks`).
- `libmltl_driver.cc`: the same driver for libmltl.
- `r2u2_driver/`: the same driver for R2U2's Rust monitor (separate crate on
  R2U2's pinned toolchain; formulas are compiled by R2U2's C2PO). It works
  around an R2U2 bug where `Monitor::reset` does not clear the temporal-logic
  instruction count.
- `run.py`, `plot.py`: run everything; plot results.

Agent context: agent-docs/modules/mltl-eval.md,
agent-docs/project/plan.md (M10).
