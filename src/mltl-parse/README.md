# mltl-parse

Turns MLTL text into a formula and a formula back into text:

```
parse:  "G[0,10] (request -> F[0,5] grant) & !fault"
          ⟶  And(Global(0, 10, Or(Not(request), Future(0, 5, grant))), Not(fault))
print:  And(Global(0, 10, Or(Not(request), Future(0, 5, grant))), Not(fault))
          ⟶  "G[0,10] (!request | F[0,5] grant) & !fault"
```

Formulas are the `Mltl` type of [mltl-core](../mltl-core/README.md), with
atoms given by their names. `->` is not part of that type, so it is stored as
the `!a | b` it stands for, and printed that way.

## What "verified" means here

[`GRAMMAR.md`](GRAMMAR.md) is the ground truth: it says which texts are
formulas and which formula each one means. The chain from it to the running
code has two links:

1. **GRAMMAR.md → Verus definitions (checked by reading).** The grammar is
   copied rule by rule into Verus definitions (next section). Nothing
   machine-checks this copy. To re-check the ground truth, compare the two
   side by side.
2. **Verus definitions → code (checked by Verus).** `parse` and `print` are
   proved to agree with those definitions, for every possible input.

So if you trust link 1, you can trust the parser without reading its code.

## Link 1: the grammar as Verus definitions

| GRAMMAR.md | Verus definition |
|---|---|
| §2 tokens | the token type [`Token`](src/lexer.rs#L12); [`lex_from`](src/lexer.rs#L155) splits text into tokens (longest match, spaces skipped, keywords in [`keyword`](src/lexer.rs#L120), symbols in [`symbol`](src/lexer.rs#L133), numbers above `usize::MAX` rejected) |
| §3 `atom` … `implication` | one definition per rule: [`atom`](src/grammar.rs#L85), [`unary`](src/grammar.rs#L97), [`until_release`](src/grammar.rs#L111), [`conjunction`](src/grammar.rs#L126), [`exclusive_or`](src/grammar.rs#L137), [`disjunction`](src/grammar.rs#L148), [`implication`](src/grammar.rs#L159), [`formula`](src/grammar.rs#L172) |
| §3 `interval`, with `a ≤ b` | [`interval`](src/grammar.rs#L73) |
| §4 `->`, `<->`, `^` | [`implies_mltl`](../mltl-core/src/mltl.rs#L44), [`iff_mltl`](../mltl-core/src/mltl.rs#L49) (both the AFP's), [`xor_mltl`](src/grammar.rs#L22) |
| "the whole text is one formula" | [`denotes`](src/grammar.rs#L180) |

Each rule definition answers one question: "do tokens `lo` to `hi` form this
rule, and do they mean formula `f`?" For example, the rule

```
conjunction  =  until_release { "&" until_release }
```

is copied as: tokens `lo..hi` form a conjunction meaning `f` if

- they form an `until_release` meaning `f`, **or**
- `f` is `And(g, h)` and there is an `&` at some position `m`, with
  `lo..m` a conjunction meaning `g` and `m+1..hi` an `until_release`
  meaning `h`.

This is the same rule, written recursively. Reading the repeated
`{ "&" until_release }` part from the left is what makes `a & b & c` mean
`And(And(a, b), c)`. The other rules follow the same pattern.

`denotes(text, f)` puts it together: `text` splits into tokens, and all of
them together form a `formula` meaning `f`. This is the definition everything
below is proved against.

## Link 2: what is proved

**[`parse`](src/lib.rs#L32)** takes text and returns a formula or `None`.
Its [guarantee](src/lib.rs#L33) has two parts:

- **Sound:** if it returns `f`, then `denotes(text, f)`.
- **Complete:** if `denotes(text, f)` for some `f`, it returns exactly that
  `f`.

Consequences:

- `None` means the grammar has no reading for the text. It never rejects a
  valid formula.
- No text has two readings: `parse` returns at most one formula, and
  completeness says it returns every reading.

**[`print`](src/printer.rs#L895)** returns the formula as text, with
parentheses only where the grammar's levels need them. Its
[guarantee](src/printer.rs#L898) covers formulas where every interval has
`a ≤ b` and every atom is a valid name (for example, not `F` or `p q`). For
those, the text denotes the formula, so by `parse`'s completeness, parsing it
gives back the same formula. Formulas outside those two conditions have no
text in the grammar.

The exact layout (spacing, which parentheses) is a definition,
[`print_text`](src/printer.rs#L335). You don't need to trust it, because the
round trip is what's proved.

**For all code in the crate,** Verus also proves termination, no crashes and
no arithmetic overflow. Nothing is assumed: there is no `assume` and no
unverified function.

## What is not proved

- That GRAMMAR.md says what we intend, and that link 1 copies it faithfully.
  This is the part to review by hand.
- Error messages: `parse` returns `None` with no position.
- As usual, Verus itself and the Rust compiler are trusted.

Supporting evidence (not proofs of the guarantees above):
- [`src/afp_binding.rs`](src/afp_binding.rs) proves that the AFP's binding
  examples group the same way in this grammar (e.g. `p & q | r` means
  `Or(And(p, q), r)`).
- [`tests/parse_examples.rs`](tests/parse_examples.rs) runs GRAMMAR.md's
  examples and 20,000 random print/parse round trips.

## Optional: numbering atoms

Evaluators work on numbered atoms (`Mltl<usize>`).
[`parse_numbered`](src/lib.rs#L63) parses, then numbers the atoms as in
GRAMMAR.md §6: `pN` is atom N, and other names get the next free numbers.

For example, `request & p2 | grant & request` gives `p2` ↦ 2, `request` ↦ 3,
`grant` ↦ 4. Different names never share a number. So, on a trace where
atom 3 holds exactly when `request` does (and so on), the numbered formula
and the named one have the same truth value
([`lemma_numbering_semantics`](src/numbering.rs#L119)).

Agent context: [agent-docs/modules/mltl-parse.md](../../agent-docs/modules/mltl-parse.md),
[agent-docs/decisions.md](../../agent-docs/decisions.md) (parser syntax).
