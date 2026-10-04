# Sources inventory

Everything listed here is **read-only** for agents. Paths use these
placeholders; other pages use them too and must not hard-code machine paths.
Where they point on the current machine: `../local-paths.md` (git-ignored,
one per machine; create it if missing).

| Placeholder | What it is |
|---|---|
| `REPO` | this repo (rust-mltl) |
| `ROOT` | `MLTL_R2U2-` repo (local Isabelle R2U2 work, `r2u2` submodule, experiments) |
| `AFP` | Archive of Formal Proofs release 2026-09-11 (https://www.isa-afp.org) |
| `REU` | `isabelle-group` repo of the Iowa State REU 2026 (MLTL→SAT translation work) |

Last surveyed 2026-10-02.

## AFP (published Isabelle) — `AFP/thys/`

### `Mission_Time_LTL` (shared core)
- `MLTL_Encoding.thy` (84 lines): `datatype 'a mltl` = `True_mltl | False_mltl |
  Prop_mltl 'a | Not_mltl | And_mltl | Or_mltl | Future_mltl nat nat φ |
  Global_mltl nat nat φ | Until_mltl φ nat nat ψ | Release_mltl φ nat nat ψ`;
  `Implies_mltl`, `Iff_mltl` are definitions (derived).
  `semantics_mltl :: 'a set list ⇒ 'a mltl ⇒ bool` (finite traces as lists of
  sets of atoms; `Prop` requires `π ≠ []`; F/U require `length π > a`;
  G/R are vacuous when `length π ≤ a`; R uses `b-1` with nat subtraction).
- `MLTL_Properties.thy` (1068 lines): `intervals_welldef`, `semantic_equiv`,
  `depth_mltl`, `subformulas`, `convert_nnf`, `complen_mltl`,
  `make_empty_trace`, plus many lemmas.

### `Mission_Time_LTL_to_Regular_Expression` (WEST)
- `WEST_Algorithms.thy` (744): `WEST_bit`, `state`/`trace`/`state_regex`/
  `trace_regex`/`WEST_regex` types, `match_timestep`, `match_regex`, `match`,
  `regex_equiv`, `WEST_and*`, `WEST_simp*`, `count_diff`, …, `WEST_num_vars`
  (l.699), `WEST_reg` (l.712, top-level algorithm).
- `WEST_Proofs.thy` (6024): correctness of `WEST_reg`.
- `Regex_Equivalence.thy` (1202): enumeration-based equivalence checking.

### `Mission_Time_LTL_Formula_Progression`
- `MLTL_Formula_Progression.thy` (2285): `weight_operators`,
  `formula_progression_len1`, `formula_progression`; theorems
  `formula_progression_decomposition`, `satisfiability_preservation`,
  `formula_progression_correctness(_alt)`.

### `Mission_Time_LTL_Language_Partition`
- `MLTL_Language_Partition_Algorithm.thy` (241): its *own* extended datatype
  `mltl_ext` (with interval annotations; `to_mltl` forgets them),
  `semantics_mltl_ext`, `convert_nnf_ext`, compositions
  (`is_composition*`, `interval_times`), list builders (`And_mltl_list`, …),
  `Mighty_Release_mltl_ext`, `Global_mltl_decomp`, `LP_mltl_aux`, `LP_mltl`.
- `MLTL_Language_Partition_Proof.thy` (6671): `LP_mltl_language_union(_explicit)`,
  `LP_mltl_language_disjoint(_k)`.
- `MLTL_Language_Partition_Codegen.thy` (34): string printing for export.

## Local Isabelle (unpublished, in progress) — `ROOT/isabelle/`
Session `MLTL_Parsing_Trees` (`ROOT/isabelle/ROOT`, `quick_and_dirty`), builds on
`Mission_Time_LTL_Formula_Progression` and `List-Index`. Theories in session order
(sorry counts = `grep -c sorry`, approximate, 2026-10-02):

| Theory | Lines | sorry | Notes |
|---|---|---|---|
| `Misc_List` | | 0 | |
| `MLTL_Properties_Extended` | | 0 | |
| `R2U2_Verdicts` | 1000 | 1 | ROOT claims sorry-free; grep hit may be a comment |
| `R2U2_Observer` | 68 | 0 | |
| `R2U2_SCQ` | 5162 | 8 | shared connection queues |
| `R2U2_Operators` | 1398 | 1 | LOAD/NOT/AND/UNTIL preservation |
| `R2U2_Parse_Tree` | 727 | 0 | |
| `R2U2_Function` | 2317 | 76 | |
| `MLTL_Update_and_R2U2_Engine_Step` | 3293 | 86 | |
| `Rewrite_Rules_and_Proofs` | 2033 | 85 | |
| `R2U2_Bugs` | 463 | 0 | documented R2U2 bugs |
| `Formula_Progression_Extended` | 1612 | 0 | simplifier + `prog`; ported (D33) |

Deprecated monolithic backups (excluded from session): `R2U2_Engine`,
`R2U2_Algorithm`, `R2U2_Proofs`. Also `R2U2_Function_Codex.thy` (Codex-assisted
variant merged into main, 2026-09). Guide: `ROOT/isabelle/explain_r2u2.md`
(distills R2U2 C/Rust into what the formalization must capture). Proof-completion
log: `ROOT/CHANGELOG.md`. Known bug write-ups at `ROOT/*_BUG.md`
(`C_RUST_DIRECT_TEMPORAL_BUG`, `SCQ_BUG`, `SHARED_NESTED_UNTIL_SOUNDNESS_BUG`,
`VALID_PARENT_CHILD_BUG`, `ISABELLE_NESTED_UNTIL_CURSOR_BUG`) — read these before
specifying R2U2; they describe places where the real monitor and the intended
semantics diverge.

## R2U2 implementation — `ROOT/r2u2` (git submodule of `github.com/R2U2/r2u2`)
- Rust monitor: `ROOT/r2u2/monitors/rust/r2u2_core` (crate `r2u2_core` v4.1.0,
  `#![no_std]`, toolchain pinned `1.85.1`, ~3.3k lines). Modules: `engines/`
  (`mltl.rs` 1222 lines, `booleanizer.rs` 762), `memory/` (`scq.rs`,
  `monitor.rs`), `instructions/`, `internals/` (`bounds.rs`, `process_binary.rs`,
  `types.rs`). Also `r2u2_cli`, `r2u2_cortex_m_example`.
- **Pre-existing Verus work upstream**: `r2u2_core` already depends on
  `vstd = "0.0.0-2025-08-12-1837"` and wraps `scq.rs`, `types.rs`,
  `booleanizer.rs`, `mltl.rs` in `verus! {}`. ~30 `requires`/`ensures` exist,
  and several fns are `#[verifier::external]` (reasons given: floats, `&mut`
  deref of `monitor.queue_arena.control_blocks`, writes to
  `monitor.value_buffer`). Instructions: `r2u2/monitors/rust/docs/dev/verification.md`.
  Extent/strength of these specs: UNKNOWN — survey before building on them.
- C monitor: `ROOT/r2u2/monitors/c` (not in scope).
- Compiler C2PO: `ROOT/r2u2/compiler` (Python); produces the binary spec that
  `r2u2_core` decodes in `internals/process_binary.rs`.

## Other local material
- `ROOT/experiments/`: `r2u2.sml` (Isabelle export), `run_r2u2_sml.py`
  (untrusted Python/lark parser → SML AST — the thing goal 6 removes),
  `run_r2u2.py`, `verify_r2u2.py` (conformance testing).
- `ROOT/formula_progression_api/`: a deployed API (FastAPI + lark parser,
  Cloud Run) around exported formula progression code. `codegen/`:
  `formula_progression.hs` (Isabelle export of `prog`, unary `Nat`, sets as
  lists) and `run_prog.hs` (reads `Mltl Nat` and the trace with derived
  `Read`, prints `prog` of every prefix). One process per request. Used
  read-only by `src/formula_progression/benchmarks` (built into its
  `build/`; needs GHC).
- `ROOT/sabre/`: SABRe (`github.com/cgjohannsen/sabre`, `c7b059eb`), an MLTL
  runtime monitor that generates C code evaluating formulas with bitwise
  operations over machine words of time steps. Prior art that our
  evaluators must not reproduce (D32).

## REU 2026 Isabelle work — `REU/isabelle/` (unpublished; surveyed 2026-10-02, commit `14fdbbe`)
- `MLTL_Properties_Extended.thy` (2479 lines): extra equivalences, CE lemmas,
  BNF, unrolling/shift lemmas, `mltl_eval` + `mltl_eval_correct`,
  `MLTL_SAT`, atoms/`atomics_agree_semantics`, plus R2U2-specific parse tree
  and r2u2-form. Ported (minus R2U2 parts) into `mltl-core/src/properties.rs`
  (D17). Distinct from (newer than) `ROOT/isabelle/MLTL_Properties_Extended.thy`.
- **MLTL SAT solver** (owner-confirmed, D18): `MLTL_SAT_Solver.thy`,
  `MLTL_To_SAT.thy`, `Fast_MLTL_To_SAT*.thy`, `MLTL_CNF_Encoder.thy`,
  `Tseytin_CNF_Lists.thy`, `Prop_To_SAT_Solver.thy`,
  `SAT_Solver_Locale_Executable.thy`, … Not yet surveyed (T7.1).

## libmltl (owner's current evaluator; performance baseline for M10)
- https://github.com/lmarzen/libmltl, surveyed at commit `19d8cfc`
  (2026-10-02). Since 2026-10-03 a git submodule at `REPO/external/libmltl`
  (D24), pinned to `19d8cfc`; read-only. C++ with pybind11
  Python bindings, LGPL-2.1. `src/ast.cc` (509 lines): AST of
  `shared_ptr<ASTNode>` with virtual `evaluate_subt(trace, begin, end)`.
- Trace format: `vector<string>`, one '0'/'1' char per atom per step;
  atoms `p<N>`; extra operators `^` (xor), `->`, `<->`/`=`; constants
  `t/tt/true`, `f/ff/false`.
- Algorithm: top-down recursive with short-circuit, one trace at a time —
  same complexity class as `mltl_eval`, O(|φ|·W^d) per trace.
- **BUG (external tool, D22): wrong semantics on short traces** — temporal loops stop at the
  trace end (`idx_end = min(begin+ub+1, end)`) instead of evaluating the
  child on the empty suffix. Checked 2026-10-02 (compiled `src/*.cc`, trace
  `["1"]` = `[{p0}]`): `F[0,2] !p0` → 0 (AFP: True, our `example_future_not`),
  `G[0,2] p0` → 1 (AFP: False, `example_global`), `!(F[0,2] p0)` → 0 (agrees).
  Expected (UNPROVEN): the two agree whenever `len π ≥ complen φ`.
- `tests/perf_compare/benchmark.cc`: 2048 random traces, 4 vars, lengths
  4…1024, formulas from `MLTL_interpreter/formulas.txt` with bounds
  rewritten to `[0, len/2]`. Reproduced (identical inputs) as the `libmltl`
  workload of `src/mltl-eval/benchmarks` (D24).

## R2U2 benchmark copy — `REPO/external/r2u2` (submodule, D24)
- https://github.com/R2U2/r2u2 branch `develop`, pinned at `5573897`
  (surveyed 2026-10-03). Read-only. Rust monitor API used: `get_monitor`,
  `update_binary_file`, `load_bool_signal`, `monitor_step`,
  `get_output_buffer`, `get_overflow_error`; outputs `r2u2_output { spec_num,
  verdict: { time, truth } }` (a verdict covers all times ≤ `time`).
- C2PO (`compiler/c2po.py`, pure-stdlib Python ≥ 3.9): `--spec f.mltl
  --output f.bin`; MLTL format with atoms `a<N>` mapped to signal N. ~0.4 s
  per invocation. Rejects constant formulas ("found constant formula ... not
  supported").
- **BUG found (R2U2, 2026-10-03):** `Monitor::reset`
  (`monitors/rust/r2u2_core/src/memory/monitor.rs`) sets
  `bz_program_count.max_program_count = 0` twice and never resets
  `mltl_program_count.max_program_count`, so `update_binary_file` on a reused
  monitor appends to the MLTL instruction table until it overflows
  (index-out-of-bounds panic in `process_binary.rs`). Benchmark driver works
  around it. Candidate upstream fix (owner's call). Also present in `ROOT/r2u2`
  (`f4ae1358`), the copy M8 will verify.
- **BUG found (R2U2, 2026-10-03): infinite loop on constant operands.** In
  `engines/mltl.rs : check_operand_data`, `MLTL_OP_TYPE_DIRECT` (constant)
  operands return a verdict on every engine re-loop (atomics only on
  `FirstLoop`); `push_result` then marks progress, so `r2u2_engine_step`'s
  `while start_time == monitor.time_stamp` re-loop never ends. Triggered by
  any C2PO output with a constant TL operand, e.g. `(!a0|true)` →
  `or n1 True`, `F[0,2]true`, `(false|false)`. Reproduced with the benchmark
  driver (per-formula 2 s timeouts). Benchmarks exclude such formulas
  (detected from C2PO's printed assembly) as unsupported.
- How R2U2 sizes memory (checked 2026-10-03): SCQ size per node
  (`compiler/c2po/scq.py`) = `max(0, max sibling wpd − bpd) + 1`
  (+ `--scq-constant`), with bpd/wpd accumulated over temporal ancestors in
  `cpt.py` (lb/ub). Operators are incremental (`engines/mltl.rs`, e.g.
  `until_operator` keeps only `previous`/`edge`/`next_time`), and `scq_write`
  compacts equal consecutive verdicts. C2PO `--debug` totals:
  `F[0,1000] a0` → 3 (rewritten to `true U`), `a0 U[0,1000] a1` → 4,
  `(G[0,1000] a0) & a1` → 1005 (the a1 queue waits for the G), nested
  `G[0,8] G[0,8] a0` → 4 without rewrites (C2PO merges nested G's).
- Memory bounds (`internals/bounds.rs`): `R2U2_MAX_QUEUE_SLOTS` (default
  2048), `R2U2_MAX_TL_INSTRUCTIONS` (256), etc., overridable by env vars at
  compile time.

## Not available locally
- **WEST Rust implementation** — https://github.com/zwang271/WEST (owner's
  public repo; D9). To be brought in as a fork submodule under `vendor/`.
