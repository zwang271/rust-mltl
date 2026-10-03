# Open questions

Ask the owner when a question blocks work; move answered items to
`decisions.md` (and delete here).

- **Q1 — How to verify R2U2/WEST "in place" while confined to `rust-mltl/`?**
  Options: (a) add the upstream repos as git submodules under `rust-mltl/`
  (e.g. on a verification branch/fork), (b) vendor a pinned copy, (c) path
  dependency on `ROOT/r2u2`. Matters for upstreaming proofs to R2U2/R2U2 and
  for keeping in sync with upstream changes.
- **Q2 — WEST repo URL** (public, owned by Zili Wang). Not on this machine.
- **Q3 — SAT solver formalization location** (verified, unpublished).
- **Q4 — Verus version.** Upstream `r2u2_core` pins `vstd
  0.0.0-2025-08-12-1837` and rust 1.85.1. Use the same, or the latest and
  update r2u2's pin? Verus is not installed on this machine yet (2026-10-02).
- **Q5 — Who wrote the existing Verus annotations in `r2u2_core`, and what do
  they prove?** Build on them or start fresh?
  Partial answer (2026-10-02, from `git log` + grep): author Alexis Aurandt
  (aaurandt, commits Jun–Oct 2025). ~30 requires/ensures in `engines/mltl.rs`
  and `engines/booleanizer.rs`, all local per-operator properties
  (`previous.time`/`next_time` updates, `not` flips truth, `min`/`max`,
  `saturating_sub` spec). No `spec fn` semantics, no invariants, no link to MLTL
  semantics. 27 `#[verifier::external*]` attrs. Plan: build on them (T8.2).
  Still open: does the upstream recipe verify today?
- **Q6 — Parser scope.** Which concrete syntax(es): AFP-style
  `F[0,3](p & q)`, C2PO input language, WEST's input syntax, R2U2 binary spec
  format? R2U2 consumes C2PO binaries, so "eliminating untrusted parsing" for
  R2U2 may mean verifying `process_binary.rs` against a spec of the binary
  format rather than a text parser.
- **Q7 — R2U2 reference semantics.** The local Isabelle R2U2 work is
  in progress with many `sorry`s and documented bugs (`ROOT/*_BUG.md`). Is the
  target theorem "r2u2_core output = MLTL semantics" (which known bugs may
  falsify) or "r2u2_core refines the Isabelle R2U2 model"?
- **Q8 — Is C2PO (compiler) in scope**, e.g. its rewrite rules
  (`Rewrite_Rules_and_Proofs.thy`)?
- **Q9 — `ROOT/sabre/`** relevance to this project.
