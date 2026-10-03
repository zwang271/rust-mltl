# Sources inventory

Everything listed here is **read-only** for agents. Paths use these
placeholders; other pages use them too and must not hard-code machine paths.

| Placeholder | What it is | Owner's machine (2026-10-02) |
|---|---|---|
| `REPO` | this repo (rust-mltl) | `/Users/wangzili/Documents/rust-mltl` |
| `ROOT` | `MLTL_R2U2-` repo (local Isabelle R2U2 work, `r2u2` submodule, experiments) | `/Users/wangzili/Documents/MLTL_R2U2-` |
| `AFP` | Archive of Formal Proofs release 2026-09-11 (https://www.isa-afp.org) | `~/afp-2026-09-11` |

On another machine, update the last column (or add a row per machine).
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
  `formula_progression_len`, `formula_progression`; theorems
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
| `Formula_Progression_Extended` | 1612 | 0 | |

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
- `ROOT/formula_progression_api/`: a deployed API around exported formula
  progression code (has `codegen/`).
- `ROOT/sabre/`: submodule `github.com/cgjohannsen/sabre` (unrelated? UNKNOWN).

## Not on this machine
- **WEST Rust implementation** — public repo owned by Zili Wang. URL UNKNOWN; ask
  before cloning.
- **MLTL SAT solver** Isabelle formalization — verified, unpublished. Location UNKNOWN.
