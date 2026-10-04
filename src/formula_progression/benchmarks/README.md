# Benchmarks: verified Rust `prog` vs the Isabelle-exported Haskell

How fast is the verified simplified progression (`prog`) compared with the
code it replaces: `prog` exported from Isabelle to Haskell, as used by
`formula_progression_api` (in the `MLTL_R2U2-` repo)?

## What is compared

| Name | What |
|---|---|
| Rust | this crate's verified `prog`, release build, system allocator |
| Rust + mimalloc | the same code; only the benchmark driver links the mimalloc allocator |
| Haskell | `codegen/formula_progression.hs` exported from Isabelle, unchanged, `ghc -O2` (GHC 9.14.1) |
| API binary | the deployed `codegen/run_prog`, one process per request, fed in its own input format |

Both in-process drivers read the same files and hash every result formula.
The hashes are compared on every point, so both implementations give
**identical output** everywhere. Timings cover progression only: parsing is
done before timing starts. The API binary is timed end to end, including
process start and text I/O, but not the Python service in front of it.

| Experiment | Workload |
|---|---|
| `length` | 4 invariants such as `G[0,n-6] (!p0 \| F[0,5] p1)`, on traces of length n that decide them only at the last step. Both whole-trace (`prog`) and one state at a time (`prog-step`, as the API does). |
| `width` | Nested windows such as `G[0,512] F[0,w] p1`: every open window is a pending obligation, so the formula stays large. |
| `random` | 100 random formulas × 10 random traces; most are decided early. |
| `api` | `length` workloads through the deployed binary vs an in-process call. |

## Results (2026-10-03, one laptop run)

Speedup of the verified Rust over the Haskell export (above 1 = Rust is faster):

| Experiment | Rust | Rust + mimalloc |
|---|---|---|
| `length`, whole trace (n = 8 … 16,384) | 0.64–0.69× | 1.09–1.21× |
| `length`, one state at a time | 0.65–0.77× | 1.12–1.30× |
| `random` | 0.96–0.99× | 1.28–1.37× |
| `width` (w = 2 … 128) | 0.65–0.83× | 0.99–1.23× |
| `width`, w = 256 | 1.37× | 1.75× |

Against the deployed API binary, an in-process Rust call is 66× faster on
the longest traces (n = 16,384: 7.4 ms vs 0.49 s) and up to 19,000× faster
on short ones (n = 8). Short requests are dominated by the ~30 ms process start.

- **The algorithm itself runs at about Haskell's speed.** Both grow
  linearly in trace length (fitted slopes 1.00–1.03). The work is creating
  and discarding many small formula nodes. GHC's allocator does that very
  cheaply, the system `malloc` used here does not, which is why the allocator decides
  who wins. A program using this crate picks its own allocator.
- **The deployed path loses mostly to overhead, not to Haskell**: process
  start, and reading/printing formulas with numbers in unary.
- An early version of the verified Rust copied subformulas instead of moving
  them and was 3–5× slower than Haskell. Profiling showed that 75% of its time
  was in `malloc`/`free`. Passing ownership fixed it without changing any proof
  statement.

Plots: `plots/*.png` (time per (formula, trace), log-log, with fitted slopes).

## Running

Needs GHC and a checkout of the `MLTL_R2U2-` repo. Point `FP_CODEGEN` at its
`formula_progression_api/codegen` directory.

```bash
cd src/formula_progression/benchmarks
export FP_CODEGEN=/path/to/MLTL_R2U2-/formula_progression_api/codegen
python3 run.py                   # ~2 minutes; --quick for a smoke test, --only length,api
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt
.venv/bin/python plot.py         # plots/*.png and the speedup tables
```

Agent context: [agent-docs/modules/formula-progression.md](../../../agent-docs/modules/formula-progression.md).
