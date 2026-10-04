# Module: mltl-parse (`src/mltl-parse`)

Verified parser, printer and atom numbering (goal 6). Spec for humans:
`src/mltl-parse/GRAMMAR.md` (owner-reviewed; keep it and `grammar.rs` in
lockstep, D10). VERIFIED 2026-10-03: 139 items, 0 errors, nothing assumed;
`cargo test -p mltl-parse --release` 4 tests pass.

## Files
- `lexer.rs`: `Token<N>` (N = `Vec<u8>` exec / `Seq<u8>` spec), spec
  `lex_from`/`lex_spec` (longest match, whitespace skipped, numbers > usize::MAX
  rejected, keywords incl. `t tt f ff`), exec `lex` == spec.
- `grammar.rs`: one relation per GRAMMAR.md rule, `rule(ts, lo, hi, f)` over
  token spans, in strict-BNF recursive form (left recursion = left
  grouping); desugarings `implies_mltl`, `iff_mltl`, `xor_mltl` with
  `*_parts` inverses; `stop_*` sets; `denotes(s, f)`.
- `parser.rs`: `p_<rule>` exec fns, each `ensures` sound + complete
  (complete under `stop_<rule>(ts, k)`); `parse_tokens`.
- `printer.rs`: `tokens_at`/`raw_tokens` (minimal parentheses by level),
  `render` (space rules: `glue`), `lemma_round_trip`, exec `print`.
- `numbering.rs`: `pnum` (`n == "p" ++ digits(v)`), table spec
  (`table_ok`, `lookup` via `has_entry`/`entry_index`), `assign`, `number`,
  `number_injective`, `pn_kept`, `lemma_numbering_semantics`
  (`traces_agree` ⇒ same truth value).
- `afp_binding.rs`: the 4 AFP binding examples, at token level.
- `lib.rs`: `parse`, `parse_str`, `parse_numbered`.

## Proof patterns that worked
- **Completeness of chain levels** (`&`, `^`, `|`): the grammar is left
  recursive, the parser loops left to right. Bridge: `spine_<level>(j, acc,
  k, f)` ("f's derivation passes through j with value acc"),
  `lemma_<level>_spine` (derivation ⇒ first piece + spine),
  `lemma_<level>_spine_step` (peel the next piece). The three levels are
  generated from one template (the generator lived in /tmp; the code shapes
  are identical, so edit all three together).
- **Existentials in recursive spec fns need `#![trigger ts[m]]`.** Without it
  Verus picks the recursive call as trigger and neither `choose` nor
  proving the existential connects to the definition. Same for every
  `choose` in proofs (`#![trigger tv[m]]`).
- Instantiate callee completeness at positions written exactly as the
  callee's argument (`(i + 1) as int`), and rule out sibling disjuncts with
  `assert(!atom(..))` (mutually recursive definitions don't unfold through
  each other at fuel 1).
- Name a `choose` as its own spec fn (`entry_index`) so different proofs
  refer to the same term.
- Concrete examples: unfold printer fns with `reveal_with_fuel(.., 8)`;
  `by (compute)` on the text printer hit "maximum recursion depth".

## Known limits / open
- Longest match is final (owner, 2026-10-03): libmltl's unspaced `p0U[0,2]`
  / `trueR[0,2]` lex as names `p0U` / `trueR`, so such text needs a space
  before `U`/`R`. (Measured: 512 of libmltl's 1662 benchmark formulas; all
  parse once spaced.) The libmltl benchmark is used only by mltl-eval; the
  parser's test of it was removed.
- `parse_numbered`'s `None` is not fully characterised: besides "not a
  formula" and "pN too large", it may mean the numbers ran out (not provable
  impossible).
- Error messages carry no position yet (parser returns `Option`).
