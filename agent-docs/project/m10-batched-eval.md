# M10 batched evaluator — design notes (SHELVED 2026-10-03)

Owner shelved this on 2026-10-03 after a design discussion ("record all the
details, I'll come back to it"). Nothing here is implemented, measured, or
verified. Task IDs: T10.2 (bit-parallel batch), T10.3 (benchmarks). The
original analysis and proof plan are in `plan.md` §M10; this page holds the
fuller design and the discussion that led to shelving. Decision: D28.

Resume point: the agent offered to build an **unverified prototype** first
(64-trace bit-sliced F/G/U evaluator in `src/mltl-eval/benchmarks/`) to
replace the speed estimate below with measurements before investing in the
Verus proof. Owner has not answered; ask when resuming.

## 1. Sliding-window fold (van Herk 1992 / Gil & Werman 1993)

Goal: for every i, fold `x[i] ⊕ … ⊕ x[i+w−1]` for an associative ⊕ with no
inverse (OR, AND, max, the Until monoid), in O(1) amortized per position.
Running-sum style "add incoming, subtract outgoing" fails because ⊕ cannot
be undone.

Algorithm: cut the array into blocks of length w (fences at multiples of w).
- S[j] = x[j] ⊕ … ⊕ (last element of j's block) — right-to-left sweep per block.
- P[j] = (first element of j's block) ⊕ … ⊕ x[j] — left-to-right sweep per block.
- window(i) = S[i] ⊕ P[i+w−1]; if i is block-aligned, window(i) = S[i].
- Any width-w window crosses at most one fence, so this is exact. ~3 ⊕ per
  element, independent of w. Needs associativity only (no commutativity:
  S part is left of P part, order preserved).

Worked example (⊕ = OR, w = 3), verified by hand 2026-10-03:

| i | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| x | 0 | 0 | 1 | 0 | 0 | 0 | 1 | 0 | 0 |
| S | 1 | 1 | 1 | 0 | 0 | 0 | 1 | 0 | 0 |
| P | 0 | 0 | 1 | 0 | 0 | 0 | 1 | 1 | 1 |

window(1) = S1 ∨ P3 = 1; window(4) = S4 ∨ P6 = 1; window(3) = S3 = 0.

Same idea in the stream-processing literature: "two-stacks" sliding-window
aggregation (Tangwongsan et al.; SWAG survey). Citation from memory, not checked.

## 2. Mapping MLTL operators to folds

- F[a,b] φ at i = OR over φ positions [i+a, i+b], w = b−a+1, guarded.
- G[a,b] φ = AND over the same window, guarded (vacuous).
- φ U[a,b] ψ: element k = (P, Q) = (φ@k, ψ@k); monoid
  (P₁,Q₁)·(P₂,Q₂) = (P₁∧P₂, Q₁∨(P₁∧Q₂)), identity (true, false). Q of the
  window fold = "ψ at some j in window, φ at all earlier window positions" =
  the AFP Until body. ~3 bitwise ops per combine.
- R by duality: φ R ψ = ¬(¬φ U ¬ψ) (check against AFP `semantics_mltl` R
  clause and `lemma_*_window` when implementing; R's window for φ is
  [a, b−1]).
- **End of trace.** Current scalar code clamps window ends to
  min(i+b, len), where index len is the shared empty-suffix slot. For
  fixed-width folds, instead **pad** each child table out to position
  h_parent − 1 + b with the empty-suffix value (all positions ≥ len are the
  same empty suffix, `lemma_suffix_clamp`). Then every window has width
  exactly w. Proof obligation: the padded fold equals the clamped window
  statement in `lemma_*_window`.
- **Guards.** F/U need len − i > a, i.e. position i+a is alive. G/R are
  vacuously true otherwise. Batched: F = alive[i+a] & fold;
  G = ¬alive[i+a] | fold.

## 3. Bit-sliced batching

- Layout: word `p[k]`, bit t = "atom p true at position k of trace t".
  Every table entry is a word; every ⊕ is one bitwise op (U: ~3) for 64
  traces at once. With SIMD: 128 (NEON, M-series), 256/512 (AVX2/AVX-512).
- Next-position arrays (current scalar `mltl_eval_bottom_up`) do NOT batch:
  each trace has its own next position. Sliding folds have no per-trace
  state and are branch-free, so all lanes advance in lockstep.
- Different trace lengths: per-position `alive[k]` mask word (bit t = k <
  len_t). Entry = (alive & value) | (¬alive & empty_value_broadcast). Empty
  value is trace-independent (F/U false, G/R true, Booleans combine).
- Fitness for spec mining = popcount(result & positives) etc. (`plan.md`).
- Plan says: plain u64 loops, let LLVM vectorize. SIMD intrinsics are not
  verifiable. Proof via Verus `by (bit_vector)`; batch proved equal to the
  per-trace scalar evaluator, hence to `semantics_mltl`.

## 4. Expected speed — ASSUMED (estimate, not measured)

- Per 64 traces: ~3 · |φ| · m word ops (m = min(len, complen)). Example:
  |φ| = 10, m = 4096 → ~123k ops / 64 ≈ 1.9k ops per trace, well under 1 µs.
- Today: `mltl_eval_bottom_up` ≈ 71 µs/eval on the libmltl workload
  (n = 4096, benchmarks README 2026-10-03). Gap sources: 64 lanes, no
  `HashSet` lookups, no branches, dense tables. Estimated ≥ 100× before
  SIMD. Told to owner as "a target to benchmark, not a promise".

## 5. Caveats raised with owner

1. Variable trace lengths → alive masks (§3). Cheap, but essential: this is
   where libmltl and R2U2 diverge from AFP.
2. Input transposition into bit-sliced layout. Amortized away in spec mining
   (once per trace set, reused across thousands of candidates). Dominates
   one-off evaluation.
3. No early exits. On random traces top-down wins today (47 µs vs 158 µs at
   n = 16384). Batched should still win via lanes, but by the smallest margin there.
4. Memory bandwidth. Low arithmetic intensity, so big formula × long traces
   may become memory-bound. Mitigations: process positions in cache-sized
   chunks; keep horizons.
5. Only helps with many traces per formula. For one long trace: pack 64
   *positions* per word instead; F[0,w] by log₂ w shift-OR doubling steps,
   O(n/64 · log w). Different layout, same flavour.
6. Outside the kernel: hash-consing shared subformula tables across a
   candidate population (`plan.md`).

## 6. Streaming variant and the relation to R2U2

Owner asked (2026-10-03) whether keeping only a sliding window of each table
is "basically R2U2", since SCQs are circular buffers. Answer recorded:

- Same output class (verdict at every position) and asymptotics (memory
  independent of |π|, linear time). But they buffer different things:
  - Windowed bottom-up: each operand keeps a window of its own values, as
    wide as the parent's interval. Streaming van Herk needs a block to end
    before its S sweep → ~2w entries per operand, fixed latency ~w.
  - R2U2 SCQ: verdicts produced but not yet consumable because a sibling
    lags. Size = delay skew `max(0, max sibling wpd − bpd) + 1` (D23), not
    interval width. Operators are incremental (few words of state, no window).
  - C2PO numbers (D23) vs windowed estimate: F[0,1000] p → 3 vs ~1000;
    p U[0,1000] q → 4 vs ~2000; (G[0,1000] p) ∧ q → 1005 vs ~2000 (both
    need q's 1000-step delay buffer; windowed also needs p's G window).
- Windowed bottom-up becomes R2U2 by: (1) time-major evaluation (forced by
  streaming; creates delay buffers); (2) replacing windows by incremental
  forward state (streaming counterpart of the right-to-left next arrays);
  (3) early decisions + run-length compaction of verdicts.
- Why keep the windowed form: (2) and (3) are data-dependent, so per-trace
  queues advance at different rates, which kills bit-parallel batching.
  Windowed = "R2U2 minus (2)–(3)": more memory per trace, but data-oblivious
  → batchable and table-shaped for proofs.

## 7. Related work to check before claiming novelty

- Bitvector evaluation of temporal formulas over many traces in LTL
  learning, e.g. GPU LTL learning by Valizadeh, Fijalkow, Berger (CAV 2024).
  Cited from memory, UNVERIFIED. Possible novelty: verified, exact AFP
  finite-trace MLTL semantics, proved = `mltl_eval_bottom_up` =
  `semantics_mltl`.

## 8. Pending follow-ups

(none: the human doc was shortened 2026-10-03 and no longer discusses the
  streaming hybrid; §6 above is the reference.)
