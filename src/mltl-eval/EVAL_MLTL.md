# How the evaluators work

This crate answers one question: does a finite trace satisfy an MLTL
formula? It has two verified evaluators. Both are proved to give exactly
the answer of the AFP semantics; they differ in how much work they do.

## One subtlety: the end of the trace

In the AFP semantics, a window that runs past the end of the trace still
counts: those steps see the *empty* trace, where every proposition is
false. On the one-step trace `[{p}]`:

- `F[0,2] ¬p` is **true** (at step 1 the trace is empty, so ¬p holds);
- `G[0,2] p` is **false** (at step 1, p does not hold).

Tools that stop scanning at the end of the trace (libmltl, for example)
get both wrong. Both evaluators here treat every step past the end as one
shared "empty" step.

## Top-down: `mltl_eval`

Read the formula as a program and evaluate from the top. For
`F[a,b] φ` at step s, check φ at steps s+a, …, s+b and stop at the first
success. G stops at the first failure; U and R scan similarly.

Example: `G[0,2] (p U[0,1] q)` on

| step | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| state | {p} | {q} | {p} | {q} |

G checks the Until at steps 0, 1 and 2, and each check scans up to two
steps of its own. The answer is true, but "does q hold at step 1?" gets
asked twice. With wide or nested intervals, the same question is asked
thousands of times.

**Cost:** widths multiply down nested operators. With widths up to W and
nesting depth d, it costs up to about |φ|·W^d steps. `G[0,100]` nested
three deep is a million steps. Early exits make typical inputs much
cheaper, and memory is tiny.

## Bottom-up: `mltl_eval_bottom_up`

Compute every fact once. For each subformula, fill a table "does it hold
at step i?", starting from the propositions and working up. Each table
covers only the steps that can matter: the root needs step 0, and a
temporal operator with upper bound b needs its children b steps further
out. For the example above:

| step | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| p | T | F | T | F |
| q | F | T | F | T |
| p U[0,1] q | T | T | T | |
| G[0,2] (…) | T | | | |

Intervals are answered in constant time with a "next true step" array.
For a child row `F F T F F`, the next true step from each position is
`2 2 2 · ·`. Then `F[a,b] φ` holds at i exactly when the next true step
from i+a is at most i+b.

**Cost:** about |φ| × (number of steps that matter). That is linear in the
trace length, and independent of interval widths. For the nested
`G[0,100]` example, it is a few hundred table entries instead of a
million steps.

## Which is faster

Neither always wins. On random traces with wide windows, top-down's early
exits usually find the answer within a step or two. When windows must be
scanned fully, bottom-up's linear cost wins by large factors.

| workload (from [`benchmarks/`](benchmarks/)) | top-down | bottom-up | bottom-up, bit rows | libmltl | R2U2 |
|---|---|---|---|---|---|
| ~45-node formula, 2M steps | 4.5 s | 0.49 s | **0.14 s** | 1.4 s | 1.3 s |
| intervals scanned fully, 16K steps | 60 ms | 94 µs | **25 µs** | 11 ms | 0.32 ms |
| random traces, 16K steps | 54 µs | 190 µs | 59 µs | **30 µs** | 190 µs |

"Bit rows" is the same bottom-up algorithm on a faster trace format
([`README.md`](README.md)).

Plots, methodology and all experiments: [`benchmarks/README.md`](benchmarks/README.md).

## Compared with R2U2

R2U2 is a runtime monitor for flight hardware. Like bottom-up, it never
evaluates a subformula twice at the same step, so it is also linear. The
difference is the job:

- **R2U2 is online.** It reads one state at a time and outputs a verdict
  for every step, in memory fixed before launch. That is ideal on board.
  But it gives no verdict when a window runs past the end of the trace,
  and in our tests it was about 3× slower than bottom-up.
- **Bottom-up is offline.** It needs the relevant part of the trace in
  memory and answers for step 0. Its memory is also bounded by the formula
  for that one answer. It handles the end of the trace exactly, and its
  tables are what a batched, many-traces-at-once evaluator would build on.

## What is proved

`mltl_eval(f, t)` and `mltl_eval_bottom_up(f, t)` both equal
`semantics_mltl(t, f)`, the transcription of the AFP definition in
`mltl-core`. Nothing is assumed beyond Verus, its solver, the Rust
compiler and the standard library's specifications.
