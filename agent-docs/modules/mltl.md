# Module: mltl (`src/mltl`), the front door

Plain Rust (no `[package.metadata.verus]`; wrappers need no proof of their own), created
2026-10-04 (D47). Text-level wrappers, each one call to a verified fn:
`Atoms` (wraps `mltl_parse::Atoms`), `eval` (bottom-up), `progress` (`prog`),
`progress_afp`, `partition` / `partition_with` (`splits::with_width` /
`with_compositions` + `LP_mltl`), `nnf`, `bnf`; `Error` with cargo-style
`Display` for parse errors. Re-exports the five crates as modules.

- Tests: doc examples in `src/lib.rs` (`cargo test -p mltl --release`).
- The algorithm crates use it as a **dev-dependency** for their doc
  examples (cycle is fine for doctests/integration tests; never add it as a
  normal dependency of those crates).
- Trace input is `IntoIterator<Item = IntoIterator<Item = AsRef<str>>>`;
  `[vec!["a"], vec![]]` is the idiom (arrays of different lengths don't
  unify). A text syntax for traces does not exist yet (owner's call).
- `prog`'s output keeps `Not … Not` dual shapes (`!(!F… | F… !…)`);
  printing `nnf(r)` reads better. Not a bug.
- Not yet wrapped: bit-row evaluator, WEST, SAT (add when those land; keep
  the table in `lib.rs` and the README in sync).
