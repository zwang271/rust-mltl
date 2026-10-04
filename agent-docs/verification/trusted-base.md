# Trusted base ledger

Every trusted item in `rust-mltl/` code MUST appear here (AGENTS.md §4):
`assume`, `admit`, axioms, `#[verifier::external_body]`, `#[verifier::external]`,
`uninterp` specs, trusted `vstd` extensions, unverified build/parse steps.

| ID | Location (file:item) | Kind | What is trusted | Why | Plan to discharge |
|---|---|---|---|---|---|

(empty — no `assume`/`admit`/`external*` in rust-mltl code, incl. `formula_progression` and `language_partitioning`, checked 2026-10-03)

Reliance on vstd's trusted std specifications (not our trust, but recorded
for visibility, D19): `mltl-eval` uses `Vec` and `std::collections::HashSet`
(`HashSet::contains` via `vstd::std_specs::hash` `assume_specification`,
plus `group_hash_axioms`: `usize` obeys the key model, default hasher is
valid). `#[verifier::spinoff_prover]` on two proofs in `properties.rs` is
a solver-scheduling attribute, not trust.

`mltl-parse` relies on vstd's `assume_specification` for `str::as_bytes`
(`parse_str` only). `#[verifier::spinoff_prover]` on `printer.rs :
exec_raw_tokens` (scheduling, not trust).

Unverified, non-library code: `src/mltl-eval/benchmarks/` (driver with an
ad-hoc libmltl-syntax parser, Python scripts, C++ libmltl driver) and
`src/mltl-eval/tests/eval_agree.rs` and `src/formula_progression/tests/progression.rs` (runtime tests; the latter has an unverified `complen` helper), `src/language_partitioning/tests/partition.rs` (runtime tests with unverified `show`/`wpd` helpers), and `src/formula_progression/benchmarks/` (drivers with ad-hoc parsers; the mimalloc allocator is linked only into the benchmark driver, never into the library).

## Upstream trust inherited by in-place targets
Track separately once R2U2/WEST are brought in. Known for `r2u2_core` as of
2026-10-02 (from upstream source, not yet audited): several
`#[verifier::external]` fns in `memory/scq.rs`, `internals/types.rs`,
`engines/booleanizer.rs` (floats; `&mut` deref of
`monitor.queue_arena.control_blocks`; writes to `monitor.value_buffer`).
Always trusted: Verus itself, Z3, rustc, `vstd`.
