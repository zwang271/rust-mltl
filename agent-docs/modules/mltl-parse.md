# Module: mltl-parse (`src/mltl-parse`)

Verified parser, printer and atom numbering (goal 6). Spec for humans:
`src/mltl-parse/GRAMMAR.md` (owner-reviewed; keep it and `grammar.rs` in
lockstep, D10). VERIFIED 2026-10-04: 156 items, 0 errors, nothing assumed;
`cargo test -p mltl-parse --release`: all pass (incl. `tests/atoms.rs`).

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
- `atoms.rs` (2026-10-04, D47): `Atoms`, a shared name table. Private
  fields + closed specs `names()`, `num()`, `wf()`; open `injective()`,
  `grows_to()`. `number`/`parse` extend the table (reusing `assign`; numbers
  of old names kept), `atom` (name → number, `None` if not in the table),
  `trace` (`ensures traces_agree(named_trace(steps), …, names(), num())`, so
  `lemma_numbering_semantics` applies), `name` (number → name: the table's
  name if valid, else `pN`; `map_atoms(name(g), num()) == g`), `print`.
  `pN` vs. names: invariant "pN < lo ≤ every name's number", so a `pN` with
  N ≥ lo after the first name is rejected (`ErrorKind::NumberTaken`); with
  no names yet, `lo` is raised instead. Names in the table are checked with
  `exec_valid_name` at print time rather than proved valid (no lemma
  "parsed names are `valid_name`" exists; would be a nice small proof).
  Runtime tests: `tests/atoms.rs`. Uses vstd's finite `Set` + `Seq::to_set`
  (`Set::new` now returns `Option<Set>` in this vstd).
- `afp_binding.rs`: the 4 AFP binding examples, at token level.
- `lib.rs`: `parse`, `parse_str`, `parse_numbered`, all returning
  `Result<_, ParseError>` (D42).
- Errors come from the verified code itself (owner, 2026-10-03: no second
  parser). `lex(s, &mut spans, &mut bad)` also returns token spans
  (`spans_ok`) or the bad piece; every `p_*` takes `fail: &mut Fail` and
  ensures `r is None ==> fail_ok(*final(fail), len)`. Only fresh failure
  sites write `fail` (`p_interval`, `p_atom`, `parse_tokens` leftovers); all
  others pass it through, which is right because the parser never
  backtracks past a failure. The soundness/completeness proofs were
  untouched by this.
- `error.rs`: `ParseError { kind, at: Span, related: Option<Span> }`,
  `from_fail` (token index → byte span), `ensures error_ok` (in bounds).
- `report.rs`: plain Rust outside `verus!` (not verified): message wording
  and rustc-style layout. Re-runs the verified `lex` to see tokens around
  the failure (glued `p0U[`, `U`/`R` and `->` chains via paren-depth scans,
  unmatched `)`), and checks suggested fixes with `parse` before showing
  them. Golden tests + 200k random texts in `tests/errors.rs`.
  `examples/check.rs`: CLI.

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
- Error positions are tested, not proved (owner chose this level,
  2026-10-03). Possible later proof: the error token is the first one after
  which the token prefix has no completion to a formula (viable-prefix
  property); would need a spec of "prefix of some formula" and an ensures
  on `fail` in each `p_*`.
- Wording is expected to change as the owner uses it (D42).
