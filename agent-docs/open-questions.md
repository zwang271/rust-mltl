# Open questions

Ask the owner when a question blocks work; move answered items to
`decisions.md` (and delete here).

- **Q5 — Who wrote the existing Verus annotations in `r2u2_core`, and what do
  they prove?** Build on them or start fresh?
  Partial answer (2026-10-02, from `git log` + grep): author Alexis Aurandt
  (aaurandt, commits Jun–Oct 2025). ~30 requires/ensures in `engines/mltl.rs`
  and `engines/booleanizer.rs`, all local per-operator properties
  (`previous.time`/`next_time` updates, `not` flips truth, `min`/`max`,
  `saturating_sub` spec). No `spec fn` semantics, no invariants, no link to MLTL
  semantics. 27 `#[verifier::external*]` attrs. Plan: build on them (T8.2).
  Still open: does the upstream recipe verify today?
- **Q8 — Is C2PO (compiler) in scope**, e.g. its rewrite rules
  (`Rewrite_Rules_and_Proofs.thy`)?
- **Q10 — Fork URLs** (D9). Owner to create forks of `R2U2/r2u2` and (if a
  fork rather than a branch is wanted for an owner-owned repo)
  `zwang271/WEST`, and give URLs. Blocks T6.1, T8.1-onward.
  Deferred by the owner (2026-10-02).
- **Q13 — Integration for the GA project**: Python (PyO3 bindings, like
  libmltl's pybind) or Rust? (The syntax part is settled in D10.)
