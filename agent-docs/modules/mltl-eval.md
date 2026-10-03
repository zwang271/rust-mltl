# Module: mltl-eval (`src/mltl-eval`)

Executable, verified evaluation of MLTL formulas (D31). Depends on
`mltl-core` for the semantics and lemmas (cross-crate proofs work with
`cargo verus`). Human docs: `README.md` (trace formats), `EVAL_MLTL.md`
(algorithms), `benchmarks/README.md`.

## Files
- `src/trace.rs`: `Trace = [HashSet<usize>]`, `trace_view` (spec),
  `lemma_suffix_clamp`, `clamp_pos`.
- `src/atom_read.rs`: trait `AtomRead` (spec `view_trace`, `inv`; exec
  `len`, `push_row`), implemented for `[HashSet<usize>]`.
- `src/bit_trace.rs`: `BitTrace { len, rows: Vec<Vec<u64>> }`; meaning defined
  from bits (`holds_spec`, `atoms_upto`, `view_trace`); `inv` = row lengths
  are `words_for(len)` and atom count ≤ usize::MAX; `push_row` unpacks a word
  at a time; `from_sets(t, num_atoms)` proved `view_trace() == trace_view(t@)`
  (requires every atom < num_atoms; costs num_atoms × len hash lookups).
- `src/top_down.rs`: `mltl_eval` (+ per-operator helpers). Ensures
  `== semantics_mltl` and `== mltl_eval_spec`.
- `src/bottom_up.rs`: generic `mltl_eval_bottom_up_on<T: AtomRead + ?Sized>`
  with the two instances `mltl_eval_bottom_up` (sets) and
  `mltl_eval_bottom_up_bits`: tables (`sat_ok`), horizons, next arrays
  (`next_ok`), window lemmas. Ensures `== semantics_mltl(t.view_trace(), f)`.
- `src/lib.rs` re-exports the two evaluators and `Trace`. It must not
  re-export spec fns: plain builds erase them (E0432).
- `tests/eval_agree.rs`: AFP examples + random cross-check
  (`cargo test -p mltl-eval --release`).
- `benchmarks/`: suite (D24). `benchmarks/proto.rs` is the unverified
  prototype (generic over atom reads; hash, bit-row, step-mask traces),
  compiled into the driver only. Driver implementations: `topdown`,
  `bottomup`, `bottomup-bits`, `proto-hash`, `proto-bits`, `proto-masks`;
  choose with `run.py --impls a,b` (an option named after the word
  "evaluators" trips the worktree command guard).
- Crate: 66 VERIFIED (2026-10-03); workspace total 196.

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
7. Proof (2026-10-03): one bottom-up proof, generic over `AtomRead`. The
   existing proofs carried over with mechanical edits (the generic version
   verified first try); new proofs only for `push_row` and `from_sets` (bit
   lemmas via `by (bit_vector)`, index arithmetic via `nonlinear_arith`).
8. Verified bit-row: 65 ms vs verified sets 259 ms (4.0×), vs prototype 36 ms.
   The gap is not the representation: profile of the verified version is 47%
   tables, 38% next arrays, 14% atom reads; verified table/next code is
   ~2× slower than the prototype's (push loops, zero-fill + `set` in
   `build_next`; prototype uses `vec![n; n]` and iterator `extend`).
   `vec![x; n]` and `Vec::resize` have vstd specs, so this is fixable, but
   it is general code tuning, outside D32's scope; not done.
9. Conversion: verified `from_sets` 97 ms per 1M-step trace (8 atoms ×
   lookups) vs prototype 18 ms (iterates set elements); once per trace.
