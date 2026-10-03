# rust-mltl

Verified, executable Rust for Mission-time Linear Temporal Logic (MLTL),
built with [Verus](https://github.com/verus-lang/verus).

## Why

Our MLTL algorithms are proved correct in Isabelle/HOL, but running them has
meant extracting SML/Haskell code, writing an unverified parser to feed it,
and conformance-testing against the real tools. This project instead puts the
proofs directly on fast Rust code — including the real R2U2 and WEST
implementations — so the code that runs is the code that is verified.

## What's covered (planned)

| Component | Isabelle source |
|---|---|
| MLTL syntax & semantics (shared core) | AFP `Mission_Time_LTL` |
| WEST (MLTL → regular expressions) | AFP `Mission_Time_LTL_to_Regular_Expression` |
| Formula progression | AFP `Mission_Time_LTL_Formula_Progression` |
| Language partitioning | AFP `Mission_Time_LTL_Language_Partition` |
| R2U2 runtime monitor | `MLTL_R2U2-` repo, `isabelle/` (in progress) |
| MLTL SAT solver | verified, unpublished |
| Verified parser for MLTL formulas | new |

## Layout

- `src/` — Rust code and Verus proofs. Each module folder has a short
  `README.md` explaining what it does and which Isabelle theory it follows.
- `agent-docs/` — working notes maintained by AI coding agents. Not intended
  for human reading.
- `AGENTS.md` — rules for AI agents working in this folder.

## Status

Early setup; no code yet.
