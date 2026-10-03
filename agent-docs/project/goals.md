# Project goals

Owner: Zili Wang. Recorded 2026-10-02 from the owner's kickoff instructions.
Paths: `ROOT`, `AFP` placeholders are defined in `sources.md`.

## The problem
The MLTL ecosystem (MLTL semantics, WEST, formula progression, language
partitioning, R2U2, an MLTL SAT solver) is formalized in Isabelle/HOL. Getting
runnable code has meant:
1. Isabelle code export → SML/Haskell (slow, awkward to integrate).
2. A hand-written, **unverified** parser to turn concrete formulas into the AST
   the extracted code expects (e.g. `ROOT/experiments/run_r2u2_sml.py` uses
   Python `lark` to build SML ASTs).
3. For R2U2, the Isabelle development is a *model* of the algorithm; tying it
   to the real C/Rust monitor is done by conformance testing (see
   `ROOT/experiments/verify_r2u2.py`) — no proof covers the shipped code.

## Goals
1. **Faithful encoding** of the formalized MLTL ecosystem in Rust/Verus, giving
   fast, verified, executable code. Specs must track Isabelle definitions
   closely enough that a reader can match them line by line (see
   `../correspondence/`).
2. **Modular, reusable library** so future MLTL algorithms are developed and
   verified against a shared core (syntax, semantics, traces, intervals,
   standard lemmas like NNF / semantic equivalence / complen).
3. **Verify R2U2 in place**: proofs over the actual `r2u2_core` Rust source,
   replacing "Isabelle model + SML + conformance tests".
4. **Verify WEST in place**: the owner's existing public Rust WEST
   implementation (https://github.com/zwang271/WEST; D9).
5. **Port + verify** formula progression and language partitioning in Rust
   (no existing Rust implementation assumed).
6. **Eliminate the untrusted parsing step**: a verified parser (and ideally a
   printer with round-trip proof) from concrete MLTL syntax to the verified AST.
   For R2U2, this likely also concerns the C2PO-compiled binary spec format
   that `r2u2_core` decodes (see open questions).

Also in scope: the MLTL SAT solver (verified in Isabelle, unpublished; source
location UNKNOWN — see `../open-questions.md`).

## Owner interest: a very fast verified evaluator (recorded 2026-10-02)
The owner has a side project learning MLTL formulas from positive/negative
trace sets with genetic algorithms / search, which needs a *very fast*
formula-on-trace evaluator (many formulas × many traces). A
performance-optimized, verified evaluator is a desired by-product. See
`plan.md` M10 for the planned approach.

## Guiding principles
- The Isabelle proofs are the reference. We are re-proving in Verus, not
  trusting Isabelle results via axioms — unless a decision in
  `../decisions.md` explicitly allows an axiom, recorded in
  `../verification/trusted-base.md`.
- Minimize the trusted base; make every trusted item visible.
- Prefer verifying existing code in place (R2U2, WEST) over rewriting. Where
  in-place code must change to be verifiable, keep changes minimal and
  behavior-preserving, and record them.
- Executable code should be efficient (machine integers, `Vec`, no needless
  cloning); spec code may use `nat`, `Seq`, `Set`, ghost state.

## Non-goals (for now)
- Re-verifying C2PO (the R2U2 compiler) end-to-end — UNKNOWN whether in scope.
- The C R2U2 monitor (`ROOT/r2u2/monitors/c`).
