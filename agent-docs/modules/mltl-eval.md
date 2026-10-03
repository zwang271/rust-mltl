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

## Lessons log (bit-row bottom-up, T10.4)
(empty: work not started)
