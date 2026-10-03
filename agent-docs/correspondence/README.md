# Isabelle ↔ Rust correspondence

One page per component (`mission-time-ltl.md`, `west.md`,
`formula-progression.md`, `language-partition.md`, `sat.md`, `r2u2.md`,
`parser.md`), created when work on that component starts.

Each page has a table, one row per Isabelle definition/theorem we port:

| Isabelle (theory : name) | Rust (file : item) | Kind (spec/exec/proof) | Status | Divergence / bridging notes |
|---|---|---|---|---|

Rules:
- Use exact Isabelle names so agents can grep both sides.
- Any intentional difference (types, bounded ints, argument order, extra
  preconditions, strengthened/weakened statements) goes in the last column
  with justification.
- Theorems we choose not to port: list them with "SKIPPED" and why.
