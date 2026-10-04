# MLTL concrete syntax

This document is the specification of the verified parser. The parser is
proved to agree with it exactly: it accepts precisely the texts this
grammar allows and returns precisely the formula this document assigns to
them. The proofs cannot catch a mistake in this document itself, so it is
written to be checked by eye.

Status: reviewed with the owner (2026-10-03). The parser, printer and
numbering step are proved against this document; see [`README.md`](README.md).

## 1. One example

```
text:     G[0,10] (request -> F[0,5] grant) & !fault
formula:  And( Global(0, 10, Or(Not(request), Future(0, 5, grant))),
               Not(fault) )
```

Reading it left to right:

- `G[0,10]` applies to the parenthesised part only.
- Inside the parentheses, `->` is the loosest operator, so its two sides are
  `request` and `F[0,5] grant`.
- `->` is not a primitive of MLTL. It is spelled out as `!request | …`,
  exactly as the AFP defines it.
- `&` binds more loosely than the prefix operators `G[…]` and `!`, so it
  joins `G[0,10] (…)` with `!fault`.

## 2. Tokens

The text is first split into tokens. Spaces, tabs and line breaks
separate tokens and are otherwise ignored.

| Token | Written as | Notes |
|---|---|---|
| name | a letter or `_`, then letters, digits, `_` | ASCII only; case-sensitive (`Req` ≠ `req`) |
| number | one or more digits `0`–`9` | decimal |
| keywords | `F` `G` `U` `R` `true` `false` `t` `tt` `f` `ff` | can never be names; `t` and `tt` mean `true`, `f` and `ff` mean `false` (libmltl's spellings) |
| symbols | `(` `)` `[` `]` `,` `!` `&` `\|` `^` `->` `<->` | |

- **Longest match.** A name or keyword runs as far as letters, digits and
  `_` continue. So `Fuel` is one name, `F[` is the keyword `F` followed by
  `[`, `tt0` is a name, and `pUq` is one name: write `p U[0,1] q`.
- **Anything else is an error.** That includes `~`, `=`, `-` on its own,
  `<` on its own, and every non-ASCII character.

## 3. Grammar

### The levels

Operators bind with different strength. The tighter an operator binds, the
smaller the piece of text it takes as its operand. Tightest first:

| Level | Operators | Chains like `a op b op c` |
|---|---|---|
| 1 | `true`, `false`, names, `( … )` | — |
| 2 | prefix `!`, `F[a,b]`, `G[a,b]` | `!!p`, `F[0,1] G[0,2] p` allowed |
| 3 | `U[a,b]`, `R[a,b]` | **not allowed**: parenthesise |
| 4 | `&` | allowed, grouped from the left |
| 5 | `^` (exclusive or) | allowed, grouped from the left |
| 6 | `\|` | allowed, grouped from the left |
| 7 | `->`, `<->` | **not allowed**, and the two can't be mixed without parentheses |

### The rules

The rules below say exactly what the table says, precisely enough to prove
things about. Rule N is level N of the table: each rule builds on the one
above it.

```
atom          =  "true" | "t" | "tt" | "false" | "f" | "ff" | name | "(" formula ")"
unary         =  atom | "!" unary | "F" interval unary | "G" interval unary
until_release =  unary [ ( "U" | "R" ) interval unary ]
conjunction   =  until_release { "&" until_release }
exclusive_or  =  conjunction { "^" conjunction }
disjunction   =  exclusive_or { "|" exclusive_or }
implication   =  disjunction [ ( "->" | "<->" ) disjunction ]

formula       =  implication
interval      =  "[" number "," number "]"
```

This is the standard way to write operator precedence into a grammar: one
rule per level, each built from the next tighter level. Chapter 6 of Robert
Nystrom's *Crafting Interpreters*
(<https://craftinginterpreters.com/parsing-expressions.html>) explains it
well. The parser has one function per rule.

### How to read a rule

Each line reads "an X is …". The notation:

| Notation | Means | Example |
|---|---|---|
| `"&"` | that exact token | `"&"` matches `&` |
| `a b` | `a` followed by `b` | `"!" unary` is `!` followed by a unary |
| `a \| b` | `a` or `b` | `"->" \| "<->"`: either arrow |
| `[ x ]` | `x` at most once (optional) | an implication has at most one arrow |
| `{ x }` | `x` any number of times, including zero | a disjunction can have many `\|` |

So `conjunction = until_release { "&" until_release }` reads: "a
conjunction is one or more until/release pieces joined by `&`". Each piece
can be as simple as a name: a name is an atom, an atom is a unary, and a
unary is an until/release without the optional `U`/`R` part.

Because each rule only uses the rule above it, whatever stands between two
`|`s is a complete exclusive-or, so any `&` inside it is grouped before the
`|`. That is how the table's levels become exact.

### Worked example: `p & q | r`

Read the rules from the bottom up, asking at each step where a rule can cut
the text:

1. `formula` is an `implication`. There is no arrow, so the whole text is
   one `disjunction`.
2. A `disjunction` is exclusive-ors joined by `|`. Cutting at the `|` gives
   `p & q` and `r`.
3. An `exclusive_or` is conjunctions joined by `^`. There is no `^`, so
   `p & q` is one `conjunction`, and so is `r`.
4. A `conjunction` is until/release pieces joined by `&`. Cutting `p & q`
   at the `&` gives `p` and `q`.
5. `p`, `q` and `r` are each a name.

Result: `Or(And(p, q), r)`. The `&` ended up inside because the
`disjunction` rule cut at `|` first. For `p | q & r` the same steps cut at
`|` first again, giving `Or(p, And(q, r))`.

### Worked example: why `p U[0,2] q U[0,3] r` is rejected

`until_release = unary [ ( "U" | "R" ) interval unary ]` allows **at most
one** `U`. The unary on either side cannot itself contain a bare `U`,
because a unary is an atom, or `!`/`F`/`G` in front of a unary. So no rule
can take a second `U`, and the parser reports an error.
`(p U[0,2] q) U[0,3] r` is accepted: the parentheses make the left part a
single atom.

### Side conditions

The parser checks these on top of the rules, and rejects with an error:

- **Intervals are well-formed.** In `[a,b]`, `a ≤ b`.
- **Numbers fit.** Every number is at most 18446744073709551615 (the
  largest machine integer, `usize::MAX` on 64-bit). A larger bound is an
  error, never wrapped around.
- **The whole text is used.** Nothing may follow a complete formula.

**Agreement with the AFP.** Isabelle's MLTL notation uses the same levels
1–4 and 6, and accepts fewer texts (it refuses `&` chains, for instance).
Every text both accept is grouped the same way by both. The AFP's own
"binding examples" in `MLTL_Encoding.thy` will be proved as lemmas about
this grammar.

## 4. What each form means

The parser produces core MLTL formulas only: `True`, `False`, `Prop`,
`Not`, `And`, `Or`, `Future`, `Global`, `Until`, `Release`. Parentheses
create no node.

| Text | Formula |
|---|---|
| `true`, `t`, `tt` | `True` |
| `false`, `f`, `ff` | `False` |
| `x` (a name) | `Prop(x)` |
| `!a` | `Not(a)` |
| `a & b`, `a \| b` | `And(a, b)`, `Or(a, b)` |
| `F[i,j] a`, `G[i,j] a` | `Future(i, j, a)`, `Global(i, j, a)` |
| `a U[i,j] b`, `a R[i,j] b` | `Until(a, i, j, b)`, `Release(a, i, j, b)` |
| `a -> b` | `Or(Not(a), b)`, which is the AFP's `Implies_mltl` |
| `a <-> b` | `And(Or(Not(a), b), Or(Not(b), a))`, which is the AFP's `Iff_mltl` |
| `a ^ b` | `Or(And(a, Not(b)), And(Not(a), b))`: one or the other, not both |

## 5. Examples

Accepted:

| Text | Formula |
|---|---|
| `p & q \| r` | `Or(And(p, q), r)` |
| `p \| q & r` | `Or(p, And(q, r))` |
| `p & q & r` | `And(And(p, q), r)` |
| `p ^ q & r` | `Xor(p, And(q, r))`, spelled out as in §4 |
| `!p & q` | `And(Not(p), q)` |
| `!(p & q)` | `Not(And(p, q))` |
| `F[0,3] p & q` | `And(Future(0,3,p), q)` |
| `F[0,3] (p & q)` | `Future(0,3, And(p, q))` |
| `F[0,2] !p` | `Future(0,2, Not(p))` |
| `p U[0,2] q & r` | `And(Until(p,0,2,q), r)` |
| `!p U[1,4] G[0,2] q` | `Until(Not(p), 1,4, Global(0,2,q))` |
| `F[0,1] p U[0,2] q` | `Until(Future(0,1,p), 0,2, q)` |
| `p -> q` | `Or(Not(p), q)` |
| `(p -> q) -> r` | `Or(Not(Or(Not(p), q)), r)` |
| `G[0,2] t` | `Global(0,2, True)` |
| `p0 & p12`, `Fuel_low` | names (see §6 for how names become atom numbers) |

Rejected:

| Text | Why |
|---|---|
| `p &` | `&` needs a right operand |
| `p U[0,2] q U[0,3] r` | `U` chain: write `(p U[0,2] q) U[0,3] r` or `p U[0,2] (q U[0,3] r)` |
| `p -> q -> r` | `->` chain |
| `p -> q <-> r` | `->` and `<->` mixed without parentheses |
| `G[3,1] p` | interval start after its end |
| `F[0,99999999999999999999] p` | bound too large |
| `F p`, `F[0,3]` | missing interval / missing operand |
| `F & q` | `F` is a keyword, not a name. (`t & q`, by contrast, is accepted: it means `True & q`.) |
| `(p` | missing `)` |
| `~p`, `p = q` | unknown symbols (libmltl's `~` and `=`) |

## 6. From names to atom numbers

The fast evaluators number atoms 0, 1, 2, …. After parsing, a separate,
verified step replaces names by numbers and returns the table it used:

- A name of the form `p` followed by a number without leading zeros (`p0`,
  `p7`, `p12`) always means atom N. This is the libmltl and WEST convention,
  so their formula and trace files work unchanged.
- Any other name (`request`, `p_alt`, `p07`) gets the next unused number, in
  order of first appearance, starting after the largest `pN` in the input.

Example: in `request & p2 | grant & request`, `p2` is atom 2, `request` is
atom 3 and `grant` is atom 4.

A formula can't be numbered if some `pN` has N ≥ 18446744073709551615 (no
number would be left after it).

The proof guarantees that different names get different numbers and that
the same name always gets the same number. So the numbered formula on the
numbered trace has the same truth value as the named formula on the named
trace.

## 7. What is proved against this document

- **Soundness.** If the parser returns a formula for a text, this document
  assigns that formula to that text.
- **Completeness.** If this document assigns a formula to a text, the parser
  returns it. Equivalently, every error is a real error.
- **Unambiguity.** No text has two readings under this grammar.
- **Round trip.** A printer turns any formula back into text, using as few
  parentheses as these levels allow, and parsing that text gives back the
  same formula.
- **Safety.** The parser always terminates, never crashes, and never
  overflows.

Unambiguity is not a separate lemma. It follows from soundness and
completeness: the parser returns at most one formula, and completeness says
it returns every reading.

Not covered by the proofs: whether this document says what we intend (hence
this review), and the wording of error messages.

The proofs use the grammar in its equivalent recursive form, for example
"a conjunction is an until/release, or a conjunction followed by `&` and an
until/release". This reads `a & b & c` as `(a & b) & c`, exactly as the
`{ }` form above does.
