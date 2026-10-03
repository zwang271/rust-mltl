# Roadmap (PROPOSED)

Status 2026-10-02: Phase 0 done (docs scaffolding). Task-level breakdown:
`plan.md` (milestones there supersede this page's ordering where they differ; order per D12). Order is a suggestion; the
owner sets priorities.

- **Phase 0 — scaffolding.** AGENTS.md, README.md, agent-docs/. DONE 2026-10-02.
- **Phase 1 — toolchain.** Install Verus; pick a version (consider matching
  upstream `r2u2_core`'s `vstd 0.0.0-2025-08-12-1837` vs. latest). Cargo
  workspace + one trivial verified crate; document the verify command in
  `../verification/verus-notes.md`.
- **Phase 2 — mltl-core.** Port `MLTL_Encoding` + the parts of
  `MLTL_Properties` the algorithms depend on. Build
  `../correspondence/mission-time-ltl.md`.
- **Phase 3 — parser.** Verified parser/printer for MLTL concrete syntax
  (needs a grammar decision; see open questions).
- **Phase 4 — algorithms.** Formula progression, language partition, WEST
  (in place), SAT solver. Each: correspondence page, spec, exec, proof of the
  main theorem(s).
- **Phase 5 — R2U2 in place.** Survey upstream Verus annotations; decide the
  in-place setup; spec the SCQ/observer/engine invariants following
  `ROOT/isabelle/R2U2_*`; connect to core semantics.
