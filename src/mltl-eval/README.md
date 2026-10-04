# mltl-eval

Verified evaluation of MLTL formulas on traces: does a trace satisfy a
formula? Every evaluator here is proved, in Verus, to return exactly the
AFP semantics [`semantics_mltl`](../mltl-core/src/mltl.rs#L163) of the
`mltl-core` crate. Each evaluator's `ensures` clause is that statement.

## Start here

- **[`mltl_eval`](src/top_down.rs#L19)** (top-down): read the semantics as
  a program, scanning each interval and stopping as soon as the answer is
  known. `ensures r == semantics_mltl(trace_view(t), f)`, and it also equals
  the Isabelle evaluator [`mltl_eval_spec`](../mltl-core/src/properties.rs#L1908).
- **[`mltl_eval_bottom_up`](src/bottom_up.rs#L288)** (bottom-up):
  compute each subformula once, at every position that matters, in a table.
  Same `ensures`. It requires `t.len() < usize::MAX`, so that every position,
  including one past the end, fits in a `usize`.
- **[`mltl_eval_bottom_up_bits`](src/bottom_up.rs#L298)**: the
  same algorithm on a bit-row trace (below). Build one with
  [`BitTrace::from_sets`](src/bit_trace.rs#L163) (every atom must be below
  its `num_atoms` argument). Its `ensures` says the result is well-formed
  (`inv`) and stands for exactly the same trace.

**Which one to use.** Quick numbers from the benchmarks (one laptop; ratios matter more than absolute times):

| Scenario | Use | Why |
|---|---|---|
| Many formulas on the same trace (formula search), or large traces / wide or nested windows | `mltl_eval_bottom_up_bits` | Fastest almost everywhere: linear in trace length × formula size, 3–4× faster than plain bottom-up, ~30× faster than top-down on a heavy 2M-step workload (141 ms vs 485 ms vs 4.5 s). Converting the trace costs ~0.1 s per million steps, once. |
| One-off checks on a set-per-step trace | `mltl_eval_bottom_up` | Same linear cost, no conversion step. |
| Small inputs, or traces where answers are found early (e.g. random data) | `mltl_eval` | Stops as soon as it knows, and uses almost no memory. On random traces it matches the bit-row version (54 µs vs 59 µs at n = 16384). But it can blow up: cost grows with window width to the power of nesting depth (36 ms vs 1 µs for 7 nested `G[0,8]`). |

The bottom-up versions keep a table of up to n booleans per subformula; top-down
keeps no tables. Full results, with libmltl and R2U2 for comparison:
[`benchmarks/README.md`](benchmarks/README.md). How the algorithms work and
what they cost: [`EVAL_MLTL.md`](EVAL_MLTL.md).

## What the guarantees mean

A trace in memory stands for a mathematical trace, a list of finite sets of
atoms, and the `ensures` clauses talk about that. For a set-per-step trace
it is [`trace_view`](src/trace.rs#L16). For a bit-row trace it is
[`view_trace`](src/bit_trace.rs#L61): atom `a` is in step `i` iff bit `i`
of row `a` is set. The bottom-up evaluator runs on any format that
implements [`AtomRead`](src/atom_read.rs#L13). Its contract says what reading
a trace must return, so the algorithm is proved once for all formats.

## Two ways to store a trace

Every executable trace format stands for the same mathematical object: a
finite list of finite sets of atoms. That is what the proofs talk about. A
format just has to be proved to denote it. Take this 4-step trace over
atoms p (= 0) and q (= 1):

| step | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| true atoms | {p} | {q} | {p, q} | {} |

**Set per step** (`Vec<HashSet<usize>>`, type [`Trace`](src/trace.rs#L13)):
the list `[{0}, {1}, {0, 1}, {}]`. Asking "is p true at step 2?" means a
hash lookup in step 2's set. It is general, compact when few atoms are true,
and maps directly onto the mathematical trace.

**Bit row per atom** ([`BitTrace`](src/bit_trace.rs#L14)): one row of bits per
atom, bit i = "true at step i". Here p = `1010` and q = `0110`. Asking "is
p true at step 2?" means reading one bit instead of a hash lookup. Build one
once per trace with `BitTrace::from_sets(&trace, num_atoms)`, which is proved
to denote the same trace. Only the trace changes: the evaluator's tables and
interval logic are exactly those of the set-per-step version. Both are one
algorithm, proved once, written against a small "read the atoms" interface
([`src/atom_read.rs`](src/atom_read.rs)).

What uses what: the top-down evaluator stays on set-per-step, since it reads
a few positions at a time. Bottom-up runs on either format. The bit-row
format pays off when the same trace is checked against many formulas, as in
formula search. On the heavy benchmark (a ~45-node formula on 1M steps) it
is about 4× faster; see [`benchmarks/README.md`](benchmarks/README.md).

## Running

From the repository root: [`scripts/verify.sh`](../../scripts/verify.sh) (proofs) and
`cargo test -p mltl-eval --release` (runtime cross-checks of the
evaluators).

Agent context: [agent-docs/modules/mltl-eval.md](../../agent-docs/modules/mltl-eval.md), [agent-docs/decisions.md](../../agent-docs/decisions.md).
