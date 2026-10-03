# Module: mltl-eval (`src/mltl-eval`)

Executable, verified evaluation of MLTL formulas (D31). Depends on
`mltl-core` for the semantics and lemmas (cross-crate proofs work with
`cargo verus`). Human docs: `README.md` (trace formats), `EVAL_MLTL.md`
(algorithms), `benchmarks/README.md`.

## Files
- `src/trace.rs`: `Trace = [HashSet<usize>]`, `trace_view` (spec),
  `lemma_suffix_clamp`, `clamp_pos`.
- `src/top_down.rs`: `mltl_eval` (+ per-operator helpers). Ensures
  `== semantics_mltl` and `== mltl_eval_spec`.
- `src/bottom_up.rs`: `mltl_eval_bottom_up`: tables (`sat_ok`), horizons,
  next arrays (`next_ok`), window lemmas. Ensures `== semantics_mltl`.
- `src/lib.rs` re-exports the two evaluators and `Trace`. It must not
  re-export spec fns: plain builds erase them (E0432).
- `tests/eval_agree.rs`: AFP examples + random cross-check
  (`cargo test -p mltl-eval --release`).
- `benchmarks/`: suite (D24). Same directory depth as before, so the scripts'
  relative paths (`ROOT.parents[2]`, `../../../../external`) are unchanged.
- Crate: 39 VERIFIED (2026-10-03); workspace total 169.

## How optimisations are developed (D31)
Prototype unverified → benchmark → iterate until convinced → then prove.
Keep every iteration in the lessons log below (what changed, measured
effect, what didn't work, which invariant it relies on). If a proof later
forces a change, the log says which fix costs least performance.

## Lessons log (trace representation, T10.4; scope per D32)
Benchmark: heavy formula (~45 nodes, 8 atoms), 1M-step trace, Apple M-series,
2026-10-03. Prototype = `src/proto.rs` (plain Rust, generic over `AtomRead`).
1. Profile of verified bottom-up (`sample`): 73% hash lookups for atoms,
   17% table building, 10% next arrays. Ceiling from representation ≈ 3.7×
   by that profile; the real gain turned out larger (lookups also hurt
   caches/branching).
2. Same algorithm, plain Rust, hash sets: 239 ms vs verified 265 ms. Plain
   code is ~10% faster by itself; compare representations within the
   prototype, not against the verified code.
3. Bit row per atom (`BitTrace`), per-bit reads: 41 ms (5.8×). Conversion
   from hash sets: 19 ms per 1M-step trace, once.
4. One 64-bit mask per step (`StepMasks`, ≤ 64 atoms): 37.7 ms, same as rows
   (38.9 ms). Rows chosen: no atom limit, same speed.
5. Rows unpacked a word at a time into the atom's table (`push_row`): 34.6 ms
   (6.2× vs hash sets). Kept.
6. Quick suite (all workloads agree with the verified evaluators): gain
   5–6× on the heavy formulas, 2–4× when windows are scanned fully, 1.2–2.7×
   on random traces with few atoms. The remaining time is tables and next
   arrays (out of scope by D32).
Proof plan: one verified bottom-up, generic over a Verus `AtomRead` trait
(spec `view`), instantiated for hash-set traces and `BitTrace`, whose view
is defined from its bits. `from_sets(t, num_atoms)` proved to give
`view == trace_view(t)`.
