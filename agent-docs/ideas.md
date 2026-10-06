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

## Owner interest (2026-10-05)

- **Flesh out WEST's API** (owner: "at some point"; not planned yet).
  Wanted: (1) sample random traces from a WEST regex (uniform over the
  concrete traces it matches, or at least each `s` filled at random), so
  random *satisfying* traces of a formula; (2) sample random
  *non-satisfying* traces (e.g. from WEST of `!f`, or rejection sampling);
  (3) an exec "does this trace match this regex / any line" check. State
  2026-10-05: none exist as exec code. `west_match` / `match_regex` /
  `match_timestep` are **spec only** (`src/west/src/algorithms.rs`), with
  proof lemmas in `matching.rs`; exec API (`src/west/src/api.rs`) is just
  `num_vars_checked`, `fast_reg_checked`, `decode_trace`, `trace_to_text`.
  A verified exec matcher against `west_match` looks cheap and would make
  "matches a line ⟺ satisfies f" checkable at runtime (front door:
  `Context::west_matches`?). Sampling needs randomness outside the
  verified core (trusted RNG; the claim would be "every sample matches /
  satisfies", provable; uniformity not). Cost: matcher small; sampling
  small-to-medium.

## Library extensions: owner's verdicts (2026-10-05)

Brainstorm of extensions toward a reusable, unified library; the owner
rated each. Priorities are the owner's words. Nothing here is planned yet.

**Wanted**
- **Equivalence / implication / validity via SAT** ("great idea"):
  `equivalent(f, g)`, `implies(f, g)`, `valid(f)` = `sat` of `f & !g` etc.
  Small.
- **Verified simplifier as its own pass** ("absolutely"): expose
  progression's proved simplification as `simplify(f)` with its
  same-meaning proof; later the landing place for C2PO rewrite rules.
  Small-medium.
- **Formula measurements in the front door** ("nice QoL"): horizon
  (`wpd`/`complen`), size, depth, atoms; verified `clone_mltl` / `eq_mltl`
  as `Clone` / `PartialEq` (then `Parsed` can derive them). Small.
- **Truth value at every step** ("seems useful"): `eval_all(f, trace)`,
  the bottom-up tables already hold it. Docs MUST explain that "at step i"
  means the formula on the suffix starting at i, i.e. `semantics(suffix
  from i, f)`: the same notion R2U2's soundness theorem checks verdicts
  against (owner confirmed 2026-10-05: suffix, not prefix). Small.
- **Complete a partial trace** ("fantastic"): is there a continuation of
  prefix `pi` satisfying `f`, and give one. This is `sat(progress(f, pi))`
  (progress' guarantee covers non-empty continuations; handle the empty
  one with `eval`). Same premise as Li & Rozier, "MLTL Benchmark
  Generation via Formula Progression", RV 2018,
  doi:10.1007/978-3-030-03769-7_25 (cited by the AFP progression entry,
  `AFP/thys/Mission_Time_LTL_Formula_Progression/document/root.bib`, key
  LR18), and the FPROGG tool (Rosentrater & Rozier 2025, "to appear",
  same bib, key RR25); survey row 15 (`project/algorithm-survey.md`).
  Paper not read yet. Small, built from two verified pieces.
- **One trace type everywhere** (medium priority): the `AtomRead`
  interface the evaluator uses, extended to progression, R2U2, SAT
  witnesses. Medium.
- **Publishing / how outsiders depend on us** (medium priority): can the
  crates go on crates.io with the pinned pre-release `vstd`? If not, git
  dependency, or a published front door hiding the verification
  dependency. Investigate.

- **Vacuity checks** ("yes definitely"): does a subformula matter? Replace
  it by `true` / `false` and test equivalence with the original. Builds on
  the SAT equivalence check above. Small once that exists.
- **Close the verified evaluator's speed gap** ("we should do this soon"):
  verified bit-row bottom-up is ~2× slower than the unverified prototype
  (65 vs 36 ms on the 1M-step heavy workload); profile blames table and
  next-array building (push loops, zero-fill + `set` in `build_next`),
  not the representation. `vec![x; n]` and `Vec::resize` have vstd specs.
  Details: `modules/mltl-eval.md` lessons 8-9. Small-medium; speeds up
  every `mltl::eval`.

**Later or separate research**
- **Partitioning: disjointness beyond depth 1 / all-ones splits; port
  `Codegen.thy` printing.** Owner: a separate theoretical direction, not a
  usability item.
- **Explanations = unsat cores** (owner's framing): given `phi` and a
  violating trace `pi`, encode `pi` as a conjunction of `G[x,x]` atom
  literals and run an unsat-core algorithm to find the trace assignments
  responsible. Separate research direction. Related: survey row 4
  (tableau SAT with unsat cores).
- **Richer spec files (several formulas, definitions, source spans):** a
  step toward verifying C2PO; big, later.
- **Command-line tool:** needed eventually so non-Rust stacks can use the
  library; deferred.
- **Stable JSON in/out:** "cross this bridge when we get there".
- **Lemma guide:** only as part of a larger documentation effort; low.

- **Bounded / shortest SAT** (find a trace of exactly length n, or the
  shortest): owner wants careful design first. Risk: someone asking for a
  shorter trace runs into end-of-trace semantics they didn't intend
  (steps past the end count as empty), so results could mislead. Design
  must make trace-length requirements impossible to misread.
- **Random formula / trace generators for property testing** (`proptest`,
  `quickcheck`): owner can't judge usefulness yet; revisit in detail when
  work on random formula / trace generation starts (with T9.1 and WEST
  sampling).
- **Monitor on embedded targets** (no standard library, fixed memory;
  overlaps R2U2 stage 2): a whole new direction, low priority.

**Declined**
- Step-by-step `Progressor` (users can build it).
- Printers for other tools' syntaxes (owner: this library will subsume
  them).
- New-crate template.
- Counting satisfying traces ("not really that useful").

## Algorithm survey (2026-10-04)

Literature + local-repo survey of MLTL algorithms not yet mechanized
(class 1) and related-logic algorithms with no MLTL version (class 2):
`project/algorithm-survey.md`. Owner is choosing which to keep.
