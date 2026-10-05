# WEST differential test

Checks that the faithful port ([`WEST_reg`](../src/exec.rs#L1331),
[`simp_pad_WEST_reg`](../src/exec.rs#L1359)) prints exactly what
Isabelle's own exported Haskell code prints, on random formulas. The proofs
already say the port equals the Isabelle definitions; this test catches a
definition copied wrongly from Isabelle, which the proofs cannot.

- [`gen.py`](gen.py) writes random formulas (prefix notation).
- [`driver.hs`](driver.hs) runs Isabelle's export; [`driver.rs`](driver.rs)
  runs the Rust port; [`run.py`](run.py) builds both and compares.

Needs GHC and Isabelle's export of the AFP entry in a directory named by
`WEST_EXPORT` (how to make it:
[agent-docs/modules/west.md](../../../agent-docs/modules/west.md)). Then
`python3 run.py [count] [seed]`.

Last run (2026-10-04): 1,200 formulas, identical output.
