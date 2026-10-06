# MLTL concrete syntax

The specification of the verified parser: it is proved to accept exactly
the texts allowed here and to return exactly the formula (or trace) this
document assigns to them. The proofs can't catch a mistake in this document
itself, so it is written to be checked by eye.

Status: formulas reviewed with the owner (2026-10-03); traces (§6) agreed
2026-10-05. Both are proved against this document; see [`README.md`](README.md).

```
text:     G[0,10] (request -> F[0,5] grant) & !fault
formula:  And( Global(0, 10, Or(Not(request), Future(0, 5, grant))),
               Not(fault) )
```

## 1. Tokens

Spaces, tabs and line breaks separate tokens and are otherwise ignored.

| Token | Written as | Notes |
|---|---|---|
| name | a letter or `_`, then letters, digits, `_` | ASCII only; case-sensitive |
| number | digits `0`–`9` | decimal, at most 18446744073709551615 (`usize::MAX`) |
| keywords | `F` `G` `U` `R` `true` `false` `t` `tt` `f` `ff` | never names; `t`, `tt` mean `true`, `f`, `ff` mean `false` (libmltl's spellings) |
| symbols | `(` `)` `[` `]` `{` `}` `,` `!` `&` `\|` `^` `->` `<->` | `{` `}` only in traces |

- **Longest match.** A name or keyword runs as far as letters, digits and
  `_` continue: `Fuel` is one name, `F[` is `F` then `[`, and `pUq` is one
  name (write `p U[0,1] q`).
- **Anything else is an error**, including `~`, `=`, a lone `-` or `<`, and
  non-ASCII characters.

## 2. Formulas

Tightest binding first:

| Level | Operators | Chains like `a op b op c` |
|---|---|---|
| 1 | `true`, `false`, names, `( … )` | — |
| 2 | prefix `!`, `F[a,b]`, `G[a,b]` | `!!p`, `F[0,1] G[0,2] p` allowed |
| 3 | `U[a,b]`, `R[a,b]` | **not allowed**: parenthesise |
| 4 | `&` | grouped from the left |
| 5 | `^` (exclusive or) | grouped from the left |
| 6 | `\|` | grouped from the left |
| 7 | `->`, `<->` | **not allowed**, and not mixed without parentheses |

The same, as rules (one per level; `[ x ]` = optional, `{ x }` = any number
of times, `"&"` = that token):

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

This is the standard way to write operator precedence into a grammar;
chapter 6 of Robert Nystrom's *Crafting Interpreters*
(<https://craftinginterpreters.com/parsing-expressions.html>) explains it
well. The parser has one function per rule.

So `p & q | r` is `Or(And(p, q), r)`: `disjunction` cuts at `|` first. And
`p U[0,2] q U[0,3] r` is rejected: `until_release` takes at most one `U`,
and a `unary` can't contain a bare `U`.

Also rejected: an interval `[a,b]` with `a > b`, and anything left over
after a complete formula.

The grouping agrees with Isabelle's MLTL notation (AFP) on every text both
accept; the AFP's binding examples are proved as lemmas.

## 3. What each form means

Only core MLTL formulas come out; parentheses create no node.

| Text | Formula |
|---|---|
| `true`, `t`, `tt` / `false`, `f`, `ff` | `True` / `False` |
| `x` (a name) | `Prop(x)` |
| `!a`, `a & b`, `a \| b` | `Not(a)`, `And(a, b)`, `Or(a, b)` |
| `F[i,j] a`, `G[i,j] a` | `Future(i, j, a)`, `Global(i, j, a)` |
| `a U[i,j] b`, `a R[i,j] b` | `Until(a, i, j, b)`, `Release(a, i, j, b)` |
| `a -> b` | `Or(Not(a), b)` (AFP `Implies_mltl`) |
| `a <-> b` | `And(Or(Not(a), b), Or(Not(b), a))` (AFP `Iff_mltl`) |
| `a ^ b` | `Or(And(a, Not(b)), And(Not(a), b))` |

## 4. Examples

| Text | Formula |
|---|---|
| `p \| q & r` | `Or(p, And(q, r))` |
| `p & q & r` | `And(And(p, q), r)` |
| `!p & q` | `And(Not(p), q)` |
| `F[0,3] p & q` | `And(Future(0,3,p), q)` |
| `p U[0,2] q & r` | `And(Until(p,0,2,q), r)` |
| `F[0,1] p U[0,2] q` | `Until(Future(0,1,p), 0,2, q)` |
| `(p -> q) -> r` | `Or(Not(Or(Not(p), q)), r)` |
| `G[0,2] t` | `Global(0,2, True)` |

| Rejected | Why |
|---|---|
| `p &` | `&` needs a right operand |
| `p U[0,2] q U[0,3] r` | `U` chain |
| `p -> q -> r`, `p -> q <-> r` | arrow chain |
| `G[3,1] p` | interval start after its end |
| `F[0,99999999999999999999] p` | bound too large |
| `F p`, `F[0,3]`, `(p` | missing interval, operand, `)` |
| `F & q` | `F` is a keyword (but `t & q` means `True & q`) |
| `~p`, `p = q` | unknown symbols (libmltl's `~`, `=`) |

## 5. Atom numbers

The evaluators number atoms 0, 1, 2, …. A verified step replaces names by
numbers, with one table shared by all formulas and traces of a problem:

- `p` followed by a number without leading zeros (`p0`, `p12`) is atom N,
  as in libmltl and WEST.
- Any other name (`request`, `p_alt`, `p07`) gets the next unused number
  when first seen, after the largest `pN` seen so far. Example: in
  `request & p2 | grant`, `p2` is 2, `request` 3, `grant` 4.
- Once a name has a number, a later `pN` must have N below it (an error
  otherwise: parse the formula with the largest `pN` first).

Different names always get different numbers, and a name keeps its number,
so numbered formulas on numbered traces have the same truth values as the
named ones.

## 6. Traces

A trace says which atoms are true at each step; every other atom is false.

### Sets: the main syntax

```
text:   [{request}, {grant, ok}, {}]
trace:  step 0: request;  step 1: grant and ok;  step 2: nothing true
```

```
trace  =  "[" [ step { "," step } ] "]"
step   =  "{" [ name { "," name } ] "}"
```

- Names as in §1; `p3` is atom 3 (§5).
- `[]` is the trace with no steps; `{}` is a step where nothing is true.
- A name may appear twice in a step (`{a, a}` is `{a}`).
- Rejected: trailing or missing commas (`[{a},]`, `{a b}`), missing
  brackets (`{a}, {b}`), anything but names in a step (`{!a}`, `{1}`).

### CSV: for trace files

R2U2's format: a header naming the columns, then one row per step, `1` true
and `0` false. This is `[{request}, {grant}, {}]`:

```
# request,grant
1,0
0,1
0,0
```

- The header is required: `#`, then one or more distinct names, separated
  by commas. A header with no rows is the trace with no steps.
- Every row has exactly one `0` or `1` per header name, separated by commas.
- Spaces and tabs are allowed around every item; lines end with `\n` or
  `\r\n`; blank lines are ignored.

### Names no formula uses

A trace may name atoms a formula doesn't use, so one trace can serve many
formulas. Such names are numbered as in §5. Checking a formula on such a
trace gives a warning, not an error:

```
warning: atoms `x`, `y` are not used in the formula and don't affect the result
```

A formula's truth value depends only on its own atoms (proved), so the
warning only helps catch typos.

### Printing

Traces print in the sets syntax, names in order of their numbers:
`[{request}, {grant, ok}, {}]`.

## 7. What is proved against this document

- **Sound and complete:** the parser returns a result exactly when this
  document gives the text one, and returns that result. So every error is a
  real error, and no text has two readings.
- **Round trip:** the printer writes formulas with as few parentheses as
  the levels allow, and traces in the sets syntax; reading the text back
  gives the same formula or trace.
- **Safety:** parsing always terminates, never crashes or overflows, and
  error positions lie inside the text.

Not covered: whether this document says what we intend (hence the review),
and the wording of error messages.
