# Module: west (`src/west`)

WEST (MLTL → regular expressions), D43: the AFP entry ported afresh, plus
a fast packed version proved *equivalent*. Isabelle mapping:
`../correspondence/west.md`. Status 2026-10-04: VERIFIED, `scripts/verify.sh
-p west` → 297 verified, 0 errors (Verus 0.2026.09.27.3cf1832), nothing
trusted.

## Files (`src/west/src/`)
| File | What |
|---|---|
| `algorithms.rs` | Spec of `WEST_Algorithms.thy` (`<name>_spec`), incl. `WEST_simp_helper` termination. |
| `matching.rs` | `*_regex_of_vars`, `@`/AND/shift/pad matching lemmas. |
| `simp.rs` | `check_simp ⟹` ≤ 1 differing entry; merge and `WEST_simp` keep the matched traces. |
| `temporal.rs` | G/F/U/R matching over `shifted π L i`; named predicates `all_shifted`, `some_shifted`, `until_shifted`, `release_(helper_)shifted`. |
| `correct.rs` | `WEST_reg_aux_correct`, `WEST_correct(_v2)`, `WEST_correct_pad`; `future/global/until/release_sem` (shared with fast). |
| `exec.rs` | Faithful exec, `rview(r) == <name>_spec(..)`; `WEST_reg`, `simp_pad_WEST_reg` with the theorem in `ensures`; `bound_sum`, exec `complen`. |
| `bits.rs` | `bit_vector` lemmas (AND/OR/XOR bits, 32-pair word check, ≤ 1 bit set, shift carry, set pair). |
| `packed.rs` | Packed trace = words, 2 bits per entry (`tr`, `twf`, position arithmetic). |
| `packed_ops.rs` | Word AND = `WEST_and_trace`, OR = `WEST_simp_trace`, diff test ⟹ `check_simp`, shift = `shift`, pad = `pad`, one-state builders. |
| `fast.rs` | `Packed` (`Vec<Vec<u64>>`), `pwf`, `pview`; constructors, `p_shift`, `p_pad`, `p_and_cross` (= `WEST_and_spec` exactly), `p_simp` (fixpoint, match-preserving), `p_or`, `p_and`. |
| `fast_reg.rs` | `p_global/future/until/release`, `p_reg`, `fast_reg` (theorem in `ensures`), `intervals_welldef_exec`. |
| `api.rs` | `fast_reg_checked` (`None` iff sizes overflow), `decode_trace`, `trace_to_text` (WEST text `s1,0s`, spec `trace_text`). |

## Design of the fast version
- Same recursion as `WEST_reg_aux` on the NNF; each regex list has one
  length `len ≤ complen φ`; AND/OR pad both sides with `S` to the longer
  length. Top level pads to `complen φ`, then simplifies once more.
- Packed: entry `(t,v)` is pair `p = n·t+v`, bits `2p` ("may be false")
  and `2p+1` ("may be true"): 11 `S`, 10 `One`, 01 `Zero`; unused bits 1.
  Shift = bit shift with carry; null check = `(z | z>>1) & 0x55…55 == 0x55…55`;
  merge test = per-word diff mask `((x^y) | (x^y)>>1) & 0x55…55` has ≤ 1 bit
  overall; merge = OR.
- Simplification merges any mergeable pair (in place, swap-remove) and
  repeats until a pass merges nothing; it does not restart after each merge
  (AFP and upstream do). Output differs from Isabelle's list; equivalence
  only (D43). **This is the main reason for the speed gap** (ablation below).
- Guarantee shape: `∀π. len π ≥ complen φ ⟹ (match π out ⟷ π ⊨ φ)`, built
  per operator: e.g. `p_until` gives `until_shifted` for `π ≥ b + max(len φ-1, len ψ)`,
  then `until_sem` turns it into semantics with the induction hypothesis.
- Size precondition: `fits(n, bound_sum φ + 1)` (`2·n·len + 64 ≤ usize::MAX`
  for every length used; `complen` of every subformula ≤ `bound_sum + 1`).
  `fast_reg_checked` decides it.
- Storage `Vec<Vec<u64>>` (one Vec per trace): measured 2026-10-04 ~4%
  slower than flat storage in the prototype (hard d=3: 26.7 vs 25.7 ms);
  chosen because proofs need no `i·w` index arithmetic.
- Verified `fast` ≈ unverified prototype (`benchmarks/proto.rs`): hard d=3
  0.023 vs 0.023 s, d=4 0.214 vs 0.221 s (2026-10-04). No proof tax.

## Why fast beats upstream (ablation, 2026-10-04)
Measured, not argued: `benchmarks/ablation/` has copies of `proto.rs`
changing one design choice each to upstream's; driver impls
`proto_restart`, `proto_quad`, `proto_toplen`; all checked exhaustively in
`tests/proto.rs`. Hard sets, 30 formulas × 15 files, 10 s limit:
- `restart` (rescan from the first pair after every merge, as AFP and both
  upstream versions): finishes 383/450 vs 397; on the 383 both finish 1.40 s
  → 30.3 s total (×22), ×1.46 geometric mean, worst ×692 (hard n=5 #5,
  5 ms → 3.4 s). Cost is n² per merge, so cubic in list size.
- `quad` (U/R rebuild `G[a,k]` each step, as upstream): 396/450, ×1.3 total,
  ×1.07 geo-mean. Small, only on heavy formulas.
- `toplen` (full-formula length from the leaves, as upstream): ×1.0.
- Output size is not the reason: fast and upstream C++ give the same count
  on 300/349 common formulas. Restart vs ours: fewer regexes on 14, more on
  16, same on 353 — neither order is better in general.
- Correction of an earlier claim (made to the owner from a 20-formula
  sample, before this run): `quad` was said to have no effect and ours was
  said to reach smaller fixpoints; the full run shows ×1.3 and a tie.
- Upstream C++'s `simplify` also restarts by recursion with the vector
  passed by value (a full copy per merge) and `erase` (shifting).

## Testing and comparison
- `cargo test -p west --release`: Isabelle `value` examples; exhaustive
  trace checks vs `mltl_eval` for faithful, fast and prototype (random
  formulas, `n·(complen+1) ≤ 14`).
- `src/west/differential/run.py` (needs GHC and `WEST_EXPORT` = output of
  `isabelle build -d $AFP/thys -b Mission_Time_LTL_to_Regular_Expression`
  then `isabelle export -d $AFP/thys -O <dir> -x "*:**" Mission_Time_LTL_to_Regular_Expression`;
  ~30 s). 2026-10-04: 1200 random formulas, `WEST_reg` and
  `simp_pad_WEST_reg` output identical to Isabelle's export.
- `src/west/benchmarks/run.py` (env `WEST_UPSTREAM` = clone of upstream WEST;
  `--hard` uses upstream's `gen_formulas_hard.py`, seed 2026);
  `summarize.py` compares on formulas all implementations finished.
  Upstream C++ is built with `-O2` (its Makefile has no `-O`); formulas
  needing > 512 bits are skipped for C++ (its bitset size).
- Harness pitfall (fixed 2026-10-04): reading the driver's pipe through a
  buffered file object made `select` miss lines already read, producing
  false timeouts and skipped formulas. Read the raw fd.

## Open / possible next
- Faster simplification: each pass is still all pairs (n²); hashing on
  "regex with one entry wildcarded" would find merges in ~n·len. Matters
  only where lists reach thousands (the remaining timeouts). Subsumption
  (dropping a regex implied by another) is not done by AFP or us.
- Website/CLI entry (D44): `fast_reg_checked` + `trace_to_text` are the
  intended surface. Parser front end: `mltl-parse` `parse_numbered`.
- `Regex_Equivalence.thy` not ported.
