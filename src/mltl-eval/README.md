# mltl-eval

Verified evaluation of MLTL formulas on traces: does a trace satisfy a
formula? Every evaluator here is proved, in Verus, to return exactly the
AFP semantics defined in the `mltl-core` crate (`semantics_mltl`).

| Evaluator | File | Idea | Status |
|---|---|---|---|
| `mltl_eval` | `src/top_down.rs` | Read the semantics as a program: scan each interval, stop as soon as the answer is known. | verified |
| `mltl_eval_bottom_up` | `src/bottom_up.rs` | Compute each subformula once, at every position that matters, in a table. | verified |
| `mltl_eval_bottom_up_bits` | `src/bottom_up.rs` | The same algorithm, reading atoms from a bit-row trace (below). | verified |

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

**Bit row per atom** (`BitTrace`, `src/bit_trace.rs`): one row of bits per
atom, bit i = "true at step i". Here p = `1010` and q = `0110`. Asking "is
p true at step 2?" means reading one bit instead of a hash lookup. Build one
once per trace with `BitTrace::from_sets(&trace, num_atoms)`, which is proved
to denote the same trace. Only the trace changes: the evaluator's tables and
interval logic are exactly those of the set-per-step version. Both are one
algorithm, proved once, written against a small "read the atoms" interface
(`src/atom_read.rs`).

What uses what: the top-down evaluator stays on set-per-step, since it reads
a few positions at a time. Bottom-up runs on either format. The bit-row
format pays off when the same trace is checked against many formulas, as in
formula search. On the heavy benchmark (a ~45-node formula on 1M steps) it
is about 4× faster; see `benchmarks/README.md`.

## Running

From the repository root: `scripts/verify.sh` (proofs) and
`cargo test -p mltl-eval --release` (runtime cross-checks of the
evaluators).

Agent context: agent-docs/modules/mltl-eval.md, agent-docs/decisions.md.
