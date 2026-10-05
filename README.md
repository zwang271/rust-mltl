# rust-mltl

Verified, executable Rust for Mission-time Linear Temporal Logic (MLTL),
built with [Verus](https://github.com/verus-lang/verus).

## Why

Our MLTL algorithms are proved correct in Isabelle/HOL, but running them has
meant extracting SML/Haskell code, writing an unverified parser to feed it,
and conformance-testing against the real tools. This project instead puts the
proofs directly on fast Rust code — including, later, the real R2U2
monitor — so the code that runs is the code that is verified.

## What's covered

| Component | Isabelle source | Crate | State |
|---|---|---|---|
| MLTL syntax & semantics (shared core) | AFP `Mission_Time_LTL` | [`src/mltl-core`](src/mltl-core/README.md) | done |
| Verified evaluators | (new) | [`src/mltl-eval`](src/mltl-eval/README.md) | done |
| Verified parser and printer for MLTL formulas | (new) | [`src/mltl-parse`](src/mltl-parse/README.md) | done |
| Formula progression | AFP `Mission_Time_LTL_Formula_Progression` | [`src/formula_progression`](src/formula_progression/README.md) | done |
| Language partitioning | AFP `Mission_Time_LTL_Language_Partition` | [`src/language_partitioning`](src/language_partitioning/README.md) | done |
| WEST (MLTL → regular expressions) | AFP `Mission_Time_LTL_to_Regular_Expression` | [`src/west`](src/west/README.md) | done: faithful port, plus a fast version proved equivalent |
| MLTL SAT solver | verified, unpublished | [`src/mltl-sat`](src/mltl-sat/README.md), [`src/propositional`](src/propositional/README.md) | verified translation; CaDiCaL answers checked (LRAT for UNSAT) |
| R2U2 runtime monitor | `MLTL_R2U2-` repo, `isabelle/` (in progress) | [`src/r2u2`](src/r2u2/README.md) | done for R2U2's algorithm: verdicts proved correct and on time, with bounded queues; found a case where `r2u2_core` is wrong. The real `r2u2_core` source is not verified yet |

[`src/mltl`](src/mltl/README.md) is the one crate to import for text-level
use (formulas and traces as text in, results as text out); it covers
evaluation, progression and partitioning so far.

## Layout

- [`src/`](src/) — Rust code and Verus proofs. Each module folder has a short
  `README.md` explaining what it does and which Isabelle theory it follows.
- [`agent-docs/`](agent-docs/) — working notes maintained by AI coding agents. Not intended
  for human reading.
- [`AGENTS.md`](AGENTS.md) — rules for AI agents working in this folder.

## Status

Everything above is proved in Verus, and nothing is assumed without proof
(for R2U2: our implementation of its algorithm, not `r2u2_core` itself).
Not verified, but not trusted either: CaDiCaL and its glue (verified code
checks every answer) and the text wrappers in [`src/mltl`](src/mltl/).
To check the proofs: [`scripts/verify.sh`](scripts/verify.sh).
