# Correspondence: AFP `Mission_Time_LTL` ↔ `src/mltl-core`

Isabelle source: `AFP/thys/Mission_Time_LTL/` (`MLTL_Encoding.thy`,
`MLTL_Properties.thy`). Rust: `src/mltl-core/src/mltl.rs` (this page's file
column is relative to `src/mltl-core/src/`). Status column per INDEX.md.
VERIFIED rows: `scripts/verify.sh`, Verus 0.2026.09.27.3cf1832, 2026-10-02.

## MLTL_Encoding.thy

| Isabelle (theory : name) | Rust (file : item) | Kind | Status | Divergence / bridging notes |
|---|---|---|---|---|
| `datatype 'a mltl` | `mltl.rs : Mltl<A>` | exec type | VERIFIED (compiles under Verus) | Constructors `True_mltl…Release_mltl` → `Mltl::True…Mltl::Release`, same order and argument order. Bounds `nat` → `usize` (D15): formulas with bounds > `usize::MAX` are not representable. Specs read bounds as `nat`. |
| `atoms_mltl` (datatype set fn) | `mltl.rs : atoms_mltl` | spec | VERIFIED (well-founded) | Returns finite `Set<A>` (formulas are finite, so no loss). |
| `Implies_mltl` | `mltl.rs : implies_mltl` | spec | VERIFIED | Definition, not a constructor, as in Isabelle. |
| `Iff_mltl` | `mltl.rs : iff_mltl` | spec | VERIFIED | |
| binding examples (`value` lines) | — | — | SKIPPED | About concrete-syntax precedence; belong to the parser (M3, T3.1). |
| `semantics_mltl` (`π ⊨_m φ`) | `mltl.rs : semantics_mltl` | spec | VERIFIED (well-founded) | **Divergence:** trace `'a set list` → `Seq<Set<A>>`, finite states only (D16; owner: infinite states are a shortcoming of the Isabelle encoding). `drop` → `mltl.rs : drop` (total, `[]` past end). Release's `b-1` → `nat_sub(b, 1)` (truncating, as Isabelle `nat` minus). Quantifier bounds written `a <= i && i <= b` exactly as Isabelle. No explicit triggers (Verus gotcha, see verus-notes). |
| example lemma 1 (`Not (F[0,2] Prop 0)`) | `mltl.rs : example_not_future` | proof | VERIFIED | Isabelle states `... = False`; Rust states `!semantics_mltl(...)`. |
| example lemma 2 (`F[0,2] (Not Prop 0)`) | `mltl.rs : example_future_not` | proof | VERIFIED | |
| example lemma 3 (`G[0,2] Prop 0`) | `mltl.rs : example_global` | proof | VERIFIED | |
| (List library) `drop`, `length (drop i xs)`, `drop_drop` | `mltl.rs : drop, lemma_drop_len, lemma_drop_drop, lemma_drop_past_end, lemma_drop_zero` | spec/proof | VERIFIED | Isabelle gets these from `List`; Verus `Seq::skip` is partial, hence our wrappers. `nat_sub` mirrors `nat` minus. |
| — | `mltl.rs : sanity_until, sanity_release_zero_bound` | proof | VERIFIED | Not in Isabelle. Exercise Until and Release incl. the `b = 0` truncation case. Negative test (flipping a claim) fails as expected, 2026-10-02. |

## MLTL_Properties.thy

PLANNED (T2.4–T2.6): `intervals_welldef`, `semantic_equiv`, `depth_mltl`,
`subformulas`, `convert_nnf`, `complen_mltl`, `make_empty_trace`, plus the
lemma inventory from T2.5.
