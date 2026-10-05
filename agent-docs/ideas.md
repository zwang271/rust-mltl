# Ideas and possible directions

Updated at each housekeeping pass. Each idea: what, why it might matter,
rough cost. The owner decides; nothing here is planned until it moves to
`project/plan.md`.

## From the first pass (2026-10-03)

1. **Use the verified evaluator as a bug-finding oracle for other MLTL tools.**
   Simply running libmltl and R2U2 against it found three real bugs in a
   day: libmltl's wrong short-trace semantics, R2U2's reset bug, and R2U2's
   infinite loop on constant operands. A systematic campaign (random formulas
   and traces, all tools, minimised counterexamples) is cheap, and every hit
   is evidence for the paper story ("the verified tool finds bugs in the
   tools people use"). Natural targets: libmltl, R2U2 (Rust and C), WEST, and
   the exported Isabelle code. Cost: small; the benchmark harness already has
   most of it.
2. **Report or fix the R2U2 bugs upstream.** Both have one-line or few-line
   fixes and minimal reproductions. This also de-risks the R2U2 milestone:
   the reset bug is in the exact code we plan to verify. Owner's call
   (outward-facing).
3. **A theorem for when tools agree.** State and prove: on traces at least
   `complen(φ)` long, the "stop at trace end" semantics (libmltl's) equals
   AFP semantics. The `atomics_agree_semantics` lemma is most of the way
   there. It turns "libmltl is buggy" into a precise, citable boundary of
   where it is safe to use. Cost: small.
4. **Cheap speed-ups before the batched evaluator.** Bottom-up spends its
   time on hash-set lookups and fresh allocations. A bitset view of the
   trace plus reused table buffers would likely make it 2–5× faster with
   modest proof changes. That benefits the owner's search project now, while
   the batched design stays shelved. Cost: small to medium.
5. **The parser as the integration point for the search project.** The
   parser milestone is next anyway. If it also accepts libmltl's syntax, and
   Python bindings come with it, the verified evaluator becomes a drop-in
   replacement for libmltl in the owner's GA code (Python bindings: D41, deferred).
   Cost: medium.
6. **Watch: Verus solver brittleness.** Proofs have needed splitting and
   `spinoff_prover` as files grew. Keep proof files moderate in size, and
   prefer many small lemmas over big case analyses, before this becomes a
   tax on every milestone.

## Owner interest (2026-10-04)

- **Formalize C2PO, the R2U2 compiler** (`ROOT/r2u2/compiler`, Python).
  Only after R2U2 (D48). Candidate pieces: its rewrite rules (`passes.py`
  `optimize_rewrite_rules`; hand proofs of 15 general rules in the
  FMICS'23 proofs PDF; none mechanized. Note: despite its name,
  `ROOT/isabelle/Rewrite_Rules_and_Proofs.thy` is an R2U2 engine-step
  equivalence and holds no formula rewrites), common
  subexpression sharing, queue sizing (`compute_scq_sizes`, where the
  shared nested-until bug lives), and the binary format `r2u2_core`
  decodes. Natural shape: a verified Rust compiler from `Mltl` to the
  stage-1 instruction layout, then to C2PO's binary. Cost: UNKNOWN, survey
  first; likely large.
