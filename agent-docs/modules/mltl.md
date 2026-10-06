# Module: mltl (`src/mltl`), the front door

Plain Rust (no `[package.metadata.verus]`; wrappers need no proof of their own), created
2026-10-04 (D47). Text-level wrappers, each one call to a verified fn:
`Context` (wraps `mltl_parse::Atoms`; renamed from `Atoms` 2026-10-05, D54), `eval` (`BitTrace::from_sets` with bound = max trace atom + 1, then `mltl_eval_bottom_up_bits`; switched from the set evaluator 2026-10-05, owner, no new benchmark: 4.0× on the 1M-step heavy workload, conversion 97 ms once; `tests/eval.rs` checks agreement with the set evaluator), `progress` (`prog`),
`progress_afp`, `partition` / `partition_with` (`splits::with_width` /
`with_compositions` + `LP_mltl`), `nnf`, `bnf`; `Error` with cargo-style
`Display` for parse errors. `Debug` = newline + `Display` (2026-10-05), so `main` returning
`Err` prints `Error:` then the whole message, not `Error: error: …`. Re-exports the five crates as modules.

- `Context::parse_formula` returns `Parsed { text, formula }` (2026-10-05, D54):
  `Deref`/`AsRef`/`From` to `Formula`, `text()`, `into_formula()`;
  `display(&parsed)` shows the text as typed (no proof needed: the parser's
  `ensures` already says the formula is what the text denotes). Algorithm
  results are bare `Formula`s and print via the verified printer (`->`
  shows as `!a | b`). Only `Debug` derived: `Mltl` has no `Clone`/`Eq`.
  Gotcha: `f(&cx.formula(..)?)` inline does NOT compile (no deref coercion
  through `?`); bind with `let` first.
- `partition_with(f, splits, depth)` (2026-10-05): `splits: impl IntoIterator<Item:
  AsRef<[usize]>>`, so `[[2, 2], [1, 1]]` and `[vec![1, 3], vec![1]]` work.
  Mixed-length `&[&[1, 3], &[1]]` no longer compiles (no expected type to
  coerce the inner arrays); use `vec!`.
- Tests: doc examples in `src/lib.rs` (`cargo test -p mltl --release`).
- Outside-user example: `example/`, a tour of every front-door algorithm on `F[0,3] (p & q)` / `[{p}, {q}, {}, {p, q}]`; SAT step prints a skip if CaDiCaL is missing; reads `example/trace.csv` with `parse_csv` (path relative to the cwd; `main` returns `Box<dyn Error>`); owner chose 2026-10-05 not to show `unused`, `monitor` + `value_at` yet (separate project, empty `[workspace]` so it is not a member; `cd example && cargo run`). Not built by `cargo test --workspace`. Editors: `.vscode/settings.json` (gitignored, local) lists it in `verus-analyzer.linkedProjects`, else the analyzer reports "cannot find crate `mltl`".
- The algorithm crates use it as a **dev-dependency** for their doc
  examples (cycle is fine for doctests/integration tests; never add it as a
  normal dependency of those crates).
- Traces (2026-10-05, D52): `Context::parse_trace` (`[{a}, {}]`),
  `Context::parse_csv`; `Context::display(&f | &t)` → `Displayed` (`impl fmt::Display`,
  like `Path::display`; sealed trait `Show` for `Formula`, `[HashSet<usize>]`,
  `Vec<HashSet<usize>>`; replaced `print` / `print_trace` 2026-10-05, D54).
  Trace bound = max atom + 1, computed unverified, so every atom prints, `Context::unused(f, t)` →
  `Option<Warning>` (plain Rust; the claim "doesn't affect the result" is
  `mltl_core::properties::lemma_semantics_own_atoms`). `Context::trace` is `&mut self` and numbers new names; its only error is
  `Error::Numbering` (a clashing `pN`). Name-list input is
  `IntoIterator<Item = IntoIterator<Item = AsRef<str>>>`; `[vec!["a"],
  vec![]]` is the idiom (arrays of different lengths don't unify).
- `prog`'s output keeps `Not … Not` dual shapes (`!(!F… | F… !…)`);
  printing `nnf(r)` reads better. Not a bug.
- WEST / SAT / R2U2 (2026-10-05, D51, D53): `Context::west` (header
  `# names` + `trace_to_text` lines; columns `0..WEST_num_vars`, so unused
  `pN` columns appear), `sat` → `Sat::{Sat(trace), Unsat, Unknown}`
  (checks `cadical --version` first → `Error::SolverMissing`; `solve`'s
  `None` → `TooLarge`), `monitor` (= `monitor_trace`), `Monitor`
  (new/step/verdicts/value_at), `value_at` (plain Rust reading of R2U2's
  `value_at` spec), `Verdict` = `r2u2::exec::ExVerdict`. Every wrapper
  first runs `r2u2::exec_engine::intervals_welldef_ex` (`BadInterval` for
  hand-built formulas). Tests: `tests/sat.rs` (SAT skipped without
  CaDiCaL). west / mltl-sat / r2u2 now use `mltl` as a dev-dependency for
  their doc examples (mltl-sat's is `no_run`: needs CaDiCaL).
- Not wrapped: top-down and bit-row evaluators, faithful `WEST_reg`.
  Keep the table in `lib.rs` and the README in sync.
