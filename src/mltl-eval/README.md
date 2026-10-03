# mltl-eval

Verified evaluation of MLTL formulas on traces: does a trace satisfy a
formula? Every evaluator here is proved, in Verus, to return exactly the
AFP semantics defined in the `mltl-core` crate (`semantics_mltl`).

| Evaluator | File | Idea | Status |
|---|---|---|---|
| `mltl_eval` | `src/top_down.rs` | Read the semantics as a program: scan each interval, stop as soon as the answer is known. | verified |
| `mltl_eval_bottom_up` | `src/bottom_up.rs` | Compute each subformula once, at every position that matters, in a table. | verified |
| bit-row bottom-up | — | The bottom-up algorithm on a faster trace format (below). | planned |

How the two algorithms work and what they cost: `EVAL_MLTL.md`. How they
compare with libmltl and R2U2 in practice: `benchmarks/README.md`.

## Two ways to store a trace

Every executable trace format stands for the same mathematical object: a
finite list of finite sets of atoms. That is what the proofs talk about. A
format just has to be proved to denote it. Take this 4-step trace over
atoms p (= 0) and q (= 1):

| step | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| true atoms | {p} | {q} | {p, q} | {} |

**Set per step** (`Vec<HashSet<usize>>`, type `Trace` in `src/trace.rs`):
the list `[{0}, {1}, {0, 1}, {}]`. Asking "is p true at step 2?" means a
hash lookup in step 2's set. It is general, compact when few atoms are true,
and maps directly onto the mathematical trace. Both current evaluators use
it.

**Bit row per atom** (planned): one row of bits per atom, bit i = "true at
step i". Here p = `1010` and q = `0110`. Asking "is p true at step 2?"
means reading one bit, and combining whole rows is one machine instruction
per 64 steps (`p AND q = 0010`). That makes it much faster for the
bottom-up algorithm, which works on whole rows anyway. It is built once per
trace from the set-per-step format, with a proof that both denote the same
trace. This pays off when the same trace is checked against many formulas,
as in formula search.

What uses what: the top-down evaluator stays on set-per-step, since it reads
a few positions at a time and gains little. The current bottom-up evaluator
stays as the verified reference. The new bit-row evaluator will take
bit-row traces.

## Running

From the repository root: `scripts/verify.sh` (proofs) and
`cargo test -p mltl-eval --release` (runtime cross-checks of the
evaluators).

Agent context: agent-docs/modules/mltl-eval.md, agent-docs/decisions.md.
