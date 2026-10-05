# west

WEST for MLTL, proved correct in Verus: given a formula, list *all* the
traces that satisfy it, as a few regular expressions. Port of the AFP entry
[`Mission_Time_LTL_to_Regular_Expression`](https://www.isa-afp.org/entries/Mission_Time_LTL_to_Regular_Expression.html).

Example: `F[0,2] p1` ("p1 holds at some step 0, 1 or 2") gives

```
s1,ss,ss    ss,s1,ss    ss,ss,s1
```

Each regex has one character per atom (`p0 p1`) per step: `1` true, `0`
false, `s` either. A trace of at least 3 steps satisfies the formula
exactly when it fits one of the three.

## Start here

**[`fast_reg_checked`](src/api.rs#L40)** is the function to use. It
returns `None` only when the formula is too large for machine words. Its
`ensures` clause is the guarantee: every regex has `complen φ` steps, and
for intervals with `a ≤ b`, a trace at least
[`complen_mltl`](../mltl-core/src/properties.rs#L758)`(φ)` steps long satisfies `φ`
([`semantics_mltl`](../mltl-core/src/mltl.rs#L164)) exactly when it
matches one of the regexes ([`west_match`](src/algorithms.rs#L106)).
[`trace_to_text`](src/api.rs#L221) prints a regex in the format above.

## Two versions

- **Faithful:** [`WEST_reg`](src/exec.rs#L1331) and
  [`simp_pad_WEST_reg`](src/exec.rs#L1359) compute exactly what Isabelle's
  definitions compute ([`WEST_reg_spec`](src/algorithms.rs#L605)). This is
  checked against Isabelle's own exported code in
  [`differential/`](differential/).
- **Fast:** [`fast_reg`](src/fast_reg.rs#L757) packs each regex into
  64-bit words and simplifies in a different order. Its regexes are not
  Isabelle's list, but they describe the same traces. That is the theorem
  in its `ensures`. Benchmarks: [`benchmarks/`](benchmarks/).

## Key theorems

[`WEST_correct`](src/correct.rs#L469) and
[`WEST_correct_pad`](src/correct.rs#L547), as in Isabelle. Nothing is
trusted. Proofs: [`scripts/verify.sh`](../../scripts/verify.sh). Runtime
checks: `cargo test -p west --release`.

Agent context: [agent-docs/modules/west.md](../../agent-docs/modules/west.md),
[agent-docs/correspondence/west.md](../../agent-docs/correspondence/west.md).
