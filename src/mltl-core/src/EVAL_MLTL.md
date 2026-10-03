# Evaluating MLTL formulas on traces

This note explains the two verified evaluators in `eval.rs`:
`mltl_eval` (top-down) and `mltl_eval_bottom_up` (bottom-up). Both answer
the same question and are proved to agree with the formal semantics; they
differ in how much work they do, and on which inputs.

## 1. The problem

Given a formula φ of Mission-time Linear Temporal Logic (MLTL) and a finite
trace π, does π satisfy φ? A trace is a sequence of states π₀, π₁, …, πₙ₋₁,
each the set of atomic propositions that hold at that step.

This question sits at the heart of several tasks. Offline runtime
verification asks it once per recorded run. Specification mining asks it
far more often: a search procedure that learns a formula from labelled
example traces proposes thousands of candidate formulas and scores each
against every example. There the evaluator is the inner loop, and its speed
bounds the whole search.

## 2. Semantics in one page

MLTL formulas are built from `true`, `false`, propositions p, the Boolean
connectives ¬, ∧, ∨, and four temporal operators with integer intervals
[a, b]:

| Formula | Holds on π when … |
|---|---|
| F[a,b] φ | φ holds on *some* suffix starting at a step i with a ≤ i ≤ b |
| G[a,b] φ | φ holds on *every* such suffix |
| φ U[a,b] ψ | ψ holds at some step i in [a, b], and φ holds at every step from a up to (not including) i |
| φ R[a,b] ψ | ψ holds throughout [a, b], or until φ releases it: φ holds at some step j in [a, b−1] and ψ holds from a up to and including j |

All four are evaluated *relative to the current position*: "step i" means
the suffix of π that starts i steps later. Our definition follows the
Isabelle/HOL formalization in the Archive of Formal Proofs
(`Mission_Time_LTL`), with one difference: our states are finite sets.

**The end of the trace.** Two details matter for short traces:

- F and U require the trace to reach the start of the interval
  (|π| > a); G and R hold vacuously when it does not.
- Inside the interval, steps that fall *past* the end of the trace are
  still examined: there the subformula is evaluated on the *empty* suffix.
  On the empty trace a proposition is false, so its negation is true.

So on the one-step trace π = [{p}], the formula F[0,2] ¬p is **true**:
at step 1 the suffix is empty and ¬p holds there. Likewise G[0,2] p is
**false**. An evaluator that simply stops scanning at the end of the trace
gets both of these wrong (libmltl, for example, does). Both evaluators below
treat every step past the end as one shared "empty suffix" position.

## 3. Top-down evaluation (`mltl_eval`)

### The algorithm

The top-down evaluator reads the semantics as a program. To evaluate a
formula at position s:

- `true`, `false`, p: look at state s (p is false if s is past the end).
- ¬, ∧, ∨: evaluate the operands at s and combine.
- F[a,b] φ: scan k = a, a+1, …, b and evaluate φ at s + k; stop at the
  first success.
- G[a,b] φ: the same scan, stopping at the first failure.
- φ U[a,b] ψ: scan k upward; succeed as soon as ψ holds at s + k; fail as
  soon as φ does not.
- φ R[a,b] ψ: scan k upward; fail as soon as ψ does not hold; succeed as
  soon as φ holds (at k ≤ b−1).

Every scan stops at the end of the trace, since all positions past the end
are the same empty suffix. Scans are loops, so the call stack grows only
with the nesting depth of the formula, never with interval widths.

### An example

Take φ = G[0,2] (p U[0,1] q) on the trace

| step | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| state | {p} | {q} | {p} | {q} |

At position 0, G scans positions 0, 1, 2. At each one it evaluates the
inner Until, which scans up to two positions of its own:

- at 0: q fails at 0, p holds at 0, then q holds at 1, so U is true;
- at 1: q holds at 1, so U is true immediately;
- at 2: q fails at 2, p holds at 2, then q holds at 3, so U is true.

All three succeed, so φ holds. The inner formula was evaluated three times,
and each evaluation re-read part of the trace.

### Cost

Let the *width* of an interval [a, b] be w = b − a + 1. Evaluating a
temporal operator at one position evaluates its operand(s) at up to w
positions. Writing T(φ) for the number of evaluation steps:

- T(p) = 1, T(¬φ) = 1 + T(φ), T(φ ∧ ψ) = 1 + T(φ) + T(ψ),
- T(F[a,b] φ) = T(G[a,b] φ) ≤ 1 + w · T(φ),
- T(φ U[a,b] ψ) = T(φ R[a,b] ψ) ≤ 1 + w · (T(φ) + T(ψ)).

Widths multiply down every chain of nested temporal operators. If W is the
largest width and d the deepest nesting of temporal operators, then

  T(φ) = O(|φ| · W^d),

independent of the trace length (the evaluator never reads beyond the
formula's horizon). The bound is tight. Evaluating G[0,w] G[0,w] … G[0,w] p
(d nested G's) on a trace where p always holds examines (w+1)^d
positions; with w = 100 and d = 3, that is about a million.

Early exits make the typical case far better than the worst case. On random
traces, F[0,100] p usually finds a true p within a step or two. Memory use is
proportional to the nesting depth.

## 4. Bottom-up evaluation (`mltl_eval_bottom_up`)

### The idea

Top-down evaluation recomputes the same facts. In the example above, "does
q hold at position 1?" was asked twice, and with wider intervals each fact
can be asked thousands of times. Bottom-up evaluation computes each fact
exactly once: for every subformula ψ it builds a table

  table_ψ[i] = "does ψ hold on the suffix starting at position i?"

working from the propositions upward. A parent's table is built from its
children's tables, and the answer is the root's entry at position 0.

### Only the positions that matter

The root needs one position, 0. A temporal operator with upper bound b,
needed at positions 0 … h−1, consults its operands at positions up to
h − 1 + b. So each subformula ψ gets a *horizon*:

  h_ψ = min(|π|, 1 + sum of the upper bounds of ψ's temporal ancestors).

Each table holds entries for positions 0 … h_ψ − 1, plus one extra slot for
the empty suffix, the value of ψ on the empty trace. That value never
depends on the trace: F and U are false there, G and R are true (given
a ≤ b), and the Boolean operators combine their operands' values as usual.

### Answering an interval in constant time

A naive table for F[a,b] φ would still OR together w entries of φ's table
at every position. Instead, after building φ's table we sweep it once from
right to left, recording for each position j the *next* position ≥ j where
φ is true:

| position | 0 | 1 | 2 | 3 | 4 | empty |
|---|---|---|---|---|---|---|
| φ | F | F | T | F | F | T |
| next true | 2 | 2 | 2 | 5 | 5 | 5 |

Here the last column (index 5) is the empty-suffix slot.

Then F[a,b] φ holds at i exactly when the next true position from i + a
lies within the window, that is at or before min(i + b, |π|). Every interval
query becomes one lookup:

- F[a,b] φ at i: nextTrue_φ(i+a) ≤ end.
- G[a,b] φ at i: nextFalse_φ(i+a) > end.
- φ U[a,b] ψ at i: let k = nextTrue_ψ(i+a). It holds iff k ≤ end and φ
  does not fail before k, i.e. nextFalse_φ(i+a) ≥ k.
- φ R[a,b] ψ at i: let k = nextFalse_ψ(i+a). If k > end, ψ holds
  throughout. Otherwise φ must release ψ strictly before k (and no later
  than b−1): nextTrue_φ(i+a) ≤ min(k − 1, i + b − 1).

Here end = min(i + b, |π|), with index |π| standing for the empty suffix.
Each operator's guard (|π| − i > a for F and U; vacuous truth for G and R)
is checked first, exactly as in the semantics.

### The example again

For φ = G[0,2] (p U[0,1] q) on the four-step trace above: the root needs
position 0, so the Until needs positions 0 … 2 and its operands 0 … 3. The
tables are

| position | 0 | 1 | 2 | 3 | empty |
|---|---|---|---|---|---|
| p | T | F | T | F | F |
| q | F | T | F | T | F |
| p U[0,1] q | T | T | T | — | F |
| G[0,2] (…) | T | | | | |

Each entry is computed once, with a constant number of lookups.

### Cost

Building a table costs time proportional to its size, and so does each
next-position sweep. The total is

  O( Σ_ψ (h_ψ + 1) ) ⊆ O( |φ| · min(|π|, complen(φ)) ),

where complen(φ) is the formula's computation length (the trace prefix it
can depend on). The cost is *linear* in the trace length and does not
depend on interval widths at all. On the nested-G example above, top-down
needs (w+1)^d steps, while bottom-up builds d tables of sizes about w, 2w,
…, dw: roughly d²·w/2 entries in total. Memory is the sum of the table
sizes.

## 5. Comparing the two

| | top-down | bottom-up |
|---|---|---|
| time, worst case | O(\|φ\| · W^d) | O(\|φ\| · min(\|π\|, complen φ)) |
| depends on interval widths | multiplicatively | no |
| early exit | yes | no; every relevant entry is computed |
| memory | O(nesting depth) | O(total table size) |

Neither dominates. Top-down wins when early exits are common and intervals
are narrow or shallowly nested. Bottom-up wins when intervals are wide, or
nested, or when the trace is adversarial for early exits.

A measurement makes this concrete. On libmltl's own benchmark (2048 random
traces over 4 propositions; 1,662 small formulas, about two temporal
operators deep, with every interval set to [0, |π|/2]; one machine,
2026-10-03; libmltl compiled with its own flags; both sides draw traces from
the same distribution, not the same traces):

| trace length | libmltl | `mltl_eval` | `mltl_eval_bottom_up` |
|---|---|---|---|
| 4 | 0.07 s | 0.11 s | 1.20 s |
| 64 | 0.39 s | 0.44 s | 4.64 s |
| 128 | 1.14 s | 1.00 s | 8.22 s |
| 256 | 3.57 s | 2.73 s | 15.1 s |
| 512 | 12.8 s | 8.64 s | 29.7 s |
| 1024 | 48.5 s | 30.7 s | 58.8 s |

Three things stand out:

- The verified top-down evaluator is already faster than libmltl from
  length 128 on, while also handling the end of the trace correctly.
- On random traces, early exits keep the top-down evaluator well below its
  worst case. Its time grows roughly 3–3.5× per doubling of the length here,
  compared with 2× per doubling for the bottom-up evaluator, which is
  exactly linear. Extrapolating, their curves cross at a length of about
  2,000–4,000.
- The bottom-up evaluator's constant factor is high. It allocates fresh
  tables for every formula and trace, and looks up every proposition at
  every relevant position in a hash set. Section 8 explains why its value
  lies elsewhere.

## 6. Bottom-up evaluation and R2U2

[R2U2](https://github.com/R2U2/r2u2) is a runtime monitor for MLTL built
for embedded flight hardware. Like bottom-up evaluation, it never evaluates a
subformula twice at the same time step, and our benchmarks
(`../benchmarks/README.md`) show it is also linear in the trace length. So
why have both? A common summary is "R2U2 uses bounded memory and bottom-up
evaluation does not". That is half right, and the half that is wrong is
instructive.

### Two different questions

The two algorithms are built for different jobs.

- **Bottom-up evaluation is offline.** It is given a whole trace and
  answers one question: does π satisfy φ, that is, does φ hold at
  position 0? It may read the trace in any order, as often as it likes.
- **R2U2 is online.** It reads the trace one state at a time, as the
  states arrive, and never looks back. It answers the question at *every*
  position: as soon as it can decide whether φ holds on the suffix
  starting at step i, it emits a verdict (i, true/false). It runs for as
  long as the stream lasts, possibly forever.

Memory has to be compared with this in mind.

### How R2U2 works

C2PO, R2U2's compiler, turns the formula into a small program with one
instruction per subformula (after rewriting, e.g. F[a,b] φ becomes
true U[a,b] φ). Each subformula owns a ring buffer, called a *shared
connection queue* (SCQ). The buffer holds verdicts (i, v), meaning "the
subformula has value v at step i". At each time step the monitor runs every
instruction once. An instruction reads new verdicts from its children's
queues, updates a few words of private state, and appends any verdicts it
can now decide to its own queue. Consecutive equal verdicts are merged into
one queue slot, so a run of "true" costs one slot, not one per step.

The temporal operators are *incremental*. To decide p U[0,1000] q at step
i, R2U2 does not store a window of 1001 values of p and q. It consumes the
pairs (p, q) in time order, step by step, and remembers only the last
verdict it emitted. A window of past values is never kept.

### Where R2U2 needs memory

Buffering is only needed when two operands of the same operator produce
verdicts at different speeds. Take (G[0,1000] p) ∧ q. The verdict of q at
step i is known as soon as step i arrives. The verdict of G[0,1000] p at
step i is known only at step i + 1000 (if p stays true). The ∧ needs both.
So q's verdicts must wait in its queue for up to 1000 steps.

C2PO computes this statically. For each subformula ψ it derives the
*best-* and *worst-case propagation delay*, bpd(ψ) and wpd(ψ): the fewest
and the most steps after step i before ψ's verdict for i is available. For a
future-time operator with interval [a, b], bpd adds a and wpd adds b. ψ's
queue then gets

  max(0, max over ψ's siblings of wpd − bpd(ψ)) + 1

slots. The sum over all subformulas is at most about |φ| · complen(φ), and
usually far less. It depends only on the formula, never on the trace
length. The monitor's whole memory is a fixed array whose size is set at
compile time (`R2U2_MAX_QUEUE_SLOTS`), with no heap allocation at all. This
is what "bounded memory" means for R2U2. It is exactly what flight software
needs: the worst case is known before launch.

### Where bottom-up evaluation needs memory

Bottom-up evaluation keeps, for each subformula ψ, a table over positions
0 … h_ψ − 1 (Section 4). The horizon h_ψ is at most |π|, but it is also at
most 1 + the sum of the upper bounds above ψ. So for a single verdict, its
memory is *also* bounded by the formula, O(|φ| · min(|π|, complen φ)), and
stops growing once the trace is longer than the formula's horizon. In that
sense the summary above is wrong.

The summary is right in three other senses:

1. **Every position, on a stream.** To get R2U2's output, φ's verdict at
   every step of an n-step trace, the bottom-up tables must cover all n
   positions: memory O(|φ| · n), growing without bound on an endless stream.
   R2U2 throws a verdict away as soon as its parent has used it. Bottom-up
   evaluation keeps the whole table, because it does not know which entries
   are still needed.
2. **The input itself.** Bottom-up evaluation takes the trace as an array,
   so at least the first min(|π|, complen φ) states must be in memory at
   once. R2U2 holds only the current state.
3. **Static versus dynamic.** Bottom-up evaluation allocates its tables on
   the heap for each call, with sizes that depend on the input. R2U2's
   footprint is a constant chosen before the program runs.

Even for a single verdict, R2U2 often needs much less than bottom-up
evaluation, because incremental operators need no windows. Here are queue
sizes reported by C2PO next to bottom-up table sizes, on a long trace:

| formula | R2U2 queue slots | bottom-up table entries |
|---|---|---|
| F[0,1000] p | 3 | about 1,000 |
| p U[0,1000] q | 4 | about 2,000 |
| (G[0,1000] p) ∧ q | 1,005 | about 1,000 |
| G[0,8] G[0,8] p (rewrites off) | 4 | about 30 |

Bottom-up evaluation also keeps a next-position array alongside each
temporal operand's table, which roughly doubles its figures. R2U2 needs as
much memory as bottom-up evaluation only when operands' delays are badly
mismatched, as in the third row.

### What R2U2 pays for this

- **Latency instead of random access.** A verdict for step i may have to
  wait until the stream reaches step i + wpd(φ); it comes sooner only when
  it can be decided early. For
  offline evaluation this costs nothing, since the whole trace is already
  there. It is the price of reading each state once.
- **No end of trace.** R2U2 assumes the stream goes on. If it ends before
  a verdict is decided, R2U2 emits nothing. The AFP semantics (Section 2)
  defines an answer on every finite trace, including windows that run past
  the end. Bottom-up evaluation computes it. Using R2U2 offline would need
  an end-of-trace "flush" that R2U2 does not have.
- **Time per step.** Each step runs every instruction, even when nothing
  new can be decided. Total time is linear in the trace length, as in
  bottom-up evaluation. In our measurements R2U2 was up to about 3× slower
  than `mltl_eval_bottom_up` (e.g. 321 µs vs 98 µs at n = 16,384, with late
  witnesses). Those runs stopped at the first verdict and did not count
  monitor set-up.
- **Not (yet) verified.** R2U2's Rust monitor has partial Verus
  annotations, but its queue code is outside the verifier. We also found
  input classes it gets wrong (some formulas with constant operands make it loop forever).
  Verifying R2U2 itself is a later goal of this project.

### Which to use

| | bottom-up (`mltl_eval_bottom_up`) | R2U2 |
|---|---|---|
| setting | offline: whole trace available | online: one state at a time |
| answers | φ at position 0 | φ at every position, as decided |
| memory, one verdict | O(\|φ\| · min(\|π\|, complen φ)), heap | Σ queue sizes, fixed at compile time |
| memory, verdict at every step | O(\|φ\| · \|π\|): grows with the trace | same fixed bound |
| time | linear in min(\|π\|, complen φ) | linear in \|π\|, every step |
| finite-trace semantics | exact (AFP), including past the end | no verdict if the stream ends early |
| batches across traces | yes (Section 8) | no: one stream per monitor |
| verified | yes, equal to `semantics_mltl` | partially annotated |

The choice follows from the job. For an onboard monitor with an endless
input and a fixed memory budget, R2U2's design is the right one. For
evaluating many formulas on many recorded traces, as in specification
mining, bottom-up evaluation fits better. It reads the trace freely, its
memory is already bounded by the formula's horizon, and its tables are the
structure that bit-parallel batching (Section 8) is built on.

The two ideas also combine. A bottom-up evaluator that needs verdicts at
every position can keep only a sliding window of each table, as large as
its parent's interval. That gives bounded memory on streams while keeping
the table structure. This is the sliding-window formulation of Section 8,
run over a stream instead of a stored trace.

## 7. What is proved

Both evaluators are verified in Verus against `semantics_mltl`, the Rust
transcription of the AFP definition (`mltl.rs`):

- `mltl_eval(f, t) == semantics_mltl(t, f)`, and it also equals
  `mltl_eval_spec`, the transcription of the Isabelle evaluator
  (`properties.rs`).
- `mltl_eval_bottom_up(f, t) == semantics_mltl(t, f)`.

The proofs rest on a few facts: suffixes past the end of the trace are all
the empty trace (`lemma_suffix_clamp`); each temporal operator at position
i equals a statement about the window of absolute positions
[i + a, min(i + b, |π|)] (`lemma_*_window`); and the next-position arrays
answer window queries exactly (`lemma_window`). Nothing in either evaluator
is assumed without proof. What remains trusted is the usual base: Verus and
its SMT solver, the Rust compiler, and vstd's specifications of `Vec` and
`HashSet`.

## 8. Where the speed will come from

The bottom-up formulation is the foundation for a much faster evaluator.

- **Many traces at once.** Search procedures evaluate one formula on many
  traces. Store bit t of a machine word for trace t: every table entry then
  covers 64 traces (or more, with vector registers), and every operation
  above becomes a handful of bitwise instructions. Early exits cannot be
  shared across traces in this layout; bottom-up evaluation never needed
  them.
- **Intervals as sliding windows.** Next-position arrays do not batch well,
  because every trace has its own "next" position. Instead, each interval
  operator can be seen as folding an associative operation over a sliding
  window. That works for OR (F) and AND (G), and also for Until, whose
  step combines as (P₁, Q₁)·(P₂, Q₂) = (P₁ ∧ P₂, Q₁ ∨ (P₁ ∧ Q₂)). Sliding
  folds take constant amortized time per position (van Herk / Gil–Werman).
  Bit-parallel tables therefore cost O(|φ| · |π|) word operations for 64
  traces at a time.
- **Shared subformulas.** Candidate formulas in a search share many
  subformulas, and their tables can be cached.

That evaluator will be proved equal to `mltl_eval_bottom_up`, and through it
to the semantics.
