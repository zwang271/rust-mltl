# Spike: does R2U2's progress reporting delay UNTIL verdicts? (2026-10-04)

Unverified throwaway code (not built by the workspace).
- `sim.py`: Python model of `src/r2u2` (history queues, compaction,
  Isabelle operators). Variant `faithful`: UNTIL's "wait" (skip ahead, no
  write) reports no progress, as Isabelle and Rust do. Variant `ideal`: it
  reports progress. Checks soundness against AFP semantics after each run.
- `search2.py`, `search3.py`, `targeted.py`: random / constructed searches
  for a violation of "node covers ≥ n + 1 − wpd after step n".
- `compare.py`: runs sim (both variants) and the real Rust `r2u2_core`
  (C2PO `--impl rust --no-rewrite --no-cse --scq-constant 64`, driver in
  `rust_driver_main.rs` printing outputs per step) on random formulas.
  Needs `/tmp/r2real/driver` built (`cargo +1.85.1 build --release`) and
  `/tmp/r2real/t.map` (`s0:0`, `s1:1`).

Results (2026-10-04):
- No `wpd` deadline miss in either variant (~600k random cases, depths
  2–4, bounds ≤ 6, traces ≤ 40, plus targeted chunk scenarios).
- `ideal` never slower than `faithful`; `faithful` lags `ideal` in ~1500
  node-steps per 40k runs, by up to 12 steps of coverage.
- Real Rust timing == `faithful` sim in 43/43 root-differing cases; Rust
  verdicts all sound (with enlarged queues).
- `probe.py`/`probe2.py`/`probe3.py`: invariant search for the faithful
  variant. `P + b ≥ min(cov_l, cov_r)` fails (26 / 1.7M UNTIL node-steps);
  `next_time ≥ min(cov_l, cov_r, (n+1) − wpd(operands))` holds (0 / 3.4M).
  The latter became `promptness.rs : untils_ready` + `lemma_last_pass`.
- `ringsim.py`: ring buffers with Isabelle compaction and read pointers;
  compares the root output with the unbounded model for child size
  `wpd(operands) + extra` (2026-10-04, 20k runs: +1/+2/+3 all match;
  all-1-slot: 11751 differ; Isabelle sizing: 86 differ).
- `ringsearch.py`, `ringtarget.py`, `ptrlag.py`, `ptrcond.py`, `ringhook.py`
  (2026-10-04): pointer staleness reaches `wpd + 2` (first pass of a step
  only, and then only the newest entry is needed); with `wpd + 1` slots the
  pointer slot is overwritten in ~7% of reads but never wrongly; `+2`:
  never overwritten. `max(1, wpd)`: 1093/20000 runs wrong.
- `sizes.py` / `sizes2.py` (2026-10-04, 20k runs): total slots and wrong
  runs for the candidate sizing rules. C2PO/Isabelle (sibling-based)
  80 wrong (value errors) at 1.00×; uniform `wpd(operands)+1` 0 wrong at 1.56×; per-child
  `max(wpd(operands) − bpd(c), 0)+1` (what we proved, D50) 0 wrong at
  1.24×. `need.py`/`need2.py` measure the per-node need directly: NOT
  children always 1; C2PO undersizes a slow child beside a fast sibling.
  `sizes2.py` needs `/tmp/r2sim/ringhook.py` and `search3.py` (copy this
  directory there).
