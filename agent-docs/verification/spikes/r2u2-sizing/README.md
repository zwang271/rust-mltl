# Spike: how big must each R2U2 queue be? (2026-10-05)

Unverified throwaway code (own `[workspace]`, not built by the repo).
Question from the owner: where C2PO's queue sizes are right, how far off are
ours; where they are wrong, why is the extra needed, and is all of it
needed; is there a better rule.

## Method
- `src/main.rs`: Rust copy of the model in `src/r2u2` (history engine +
  Isabelle ring). Checked: `xcheck.py` (same root outputs as
  `../r2u2-promptness/sim.py`/`ringhook.py`, unbounded and with C2PO sizes,
  3000/3000), `check` mode (rule below exact: measured sizes always enough,
  one less always breaks a read, 4424/4424).
- **Exact per-queue need from one unbounded run.** Reader pointer at
  logical entry `j`, child has `len` compacted entries, needed entry `k`
  (first with time ≥ τ). A ring of `N` slots reads right for every
  `N` iff `k` is absent or `k = len − 1`; otherwise iff `N ≥ len − j`
  (smaller `N`: the pointer slot holds an entry later than `k`). Follows
  from `ring_abs` + `ring_scan`. So `need(c) = max over reads`, no need to
  try sizes. Queues are independent while all reads are right.
- Per formula: 30 random traces (5 generators) + hill climbing per edge.
  `run` (stats per edge), `stress RULE` (search for need > RULE),
  `explain` (log a worst trace), `c2cex` (trace where C2PO sizes give a
  wrong *value*).
- `real.py`: compiles with real C2PO (`--no-rewrite --no-cse`, default
  sizes) and runs real `r2u2_core` (driver from `src/r2u2/benchmarks`).
- Notation for child `c` of binary node, sibling `s`: `x = max(wpd l,
  wpd r) − bpd(c)` (ours = `x + 1`), `y = max(wpd(s) − bpd(c), 0)` (C2PO =
  `y + 1`). They differ only when `c` is the **slower** child
  (`wpd(c) > wpd(s)`).
- Commands: `grid.sh` (2 shared atoms), `grid_distinct.sh` (one atom per
  leaf = every trace the shape allows), `stress.sh`, `stress_deep.sh`;
  `analyze.py`. Outputs in `out/` (gitignored, ~200 MB).

## Results
- **The model = real r2u2_core.** On 40/40 formulas where the model with
  C2PO sizes gives a wrong value, real `r2u2_core` is wrong on the same
  trace and its output equals the model's exactly.
- C2PO sizes are too small (some read wrong) in 13–95% of formulas
  (depth 3–5, bounds 4–40; more with bigger intervals, deeper formulas,
  distinct atoms); a wrong root *value* in 8–81%.
- **Every C2PO shortfall is at a slower child** (faster/equal child: ours =
  C2PO, never too small). 98% have C2PO size 1 (`bpd(c) ≥ wpd(s)`).
  Shortfall 1–3 slots in 93%, max 19 seen (54k short queues).
- C2PO-correct formulas: ours is 1.18–1.37× C2PO total (per cell).
- **Why the extra is needed** (`explain`, smallest case
  `p0 U[0,3] (p1 U[7,10] p2)`: C2PO 1, ours 4, need 3): the slow child
  waits, then catches up with one long entry; the reader walks through it
  about one step per pass (the fast sibling's entries are one step long)
  and gets only ~2 passes per time step (pass 0 + at least one repeat; an
  UNTIL skip reports no progress, so the step often ends there), while the
  child, now caught up, writes one new entry per step. So the backlog is
  about half the jump plus the sibling term. `IDEAL=1` (skip reports
  progress) halves the violations but does not remove them (bursts of
  several entries in one step, mostly under `&`).
- **Not all of the extra is needed. Candidate "half":**
  `size = y + ⌈(x − y)/2⌉ + 1` (= C2PO + half of our extra, rounded up).
  Never beaten: 884k edges in the grids, `stress half` 10.8k formulas ×
  4000 iterations, `stress_deep.sh` 2000 formulas × 40000 iterations: 0.
  Reached exactly on thousands of edges (tight in shape). Rounding down
  (`half_floor`) is beaten (69 formulas, by 1 slot, e.g. the formula above).
  Totals: half ≈ 1.19× C2PO, ours ≈ 1.38× (all formulas).
- The measured need totals (0.3–0.7× C2PO) are **search-limited**: 15× more
  search raised faster-child needs from 47% to 69% of C2PO's size. Do not
  read them as slack.

## Status
"half" is VERIFIED (2026-10-05, D55, `src/r2u2/src/half.rs`). Before the
proof, `psi` mode with `CHECKINV=1` checked the exact invariant (`psi ≤ x +
y + [ent = 0]` before every pass, and for the next step after the last pass)
on 7.5 billion pass checks: 0 failures.
