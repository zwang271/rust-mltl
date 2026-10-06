# Human-doc backlog

Human-facing docs (anything outside `agent-docs/` except `AGENTS.md`) that an
agent believes are stale or wrong. Agents may not fix these without a human
request (AGENTS.md §3.2). List: file, what's wrong, proposed text, date found.
Remove an entry once a human has had it applied.

(empty — all entries applied 2026-10-04 at the owner's request: README.md,
AGENTS.md goal 4, PLAN.md, line anchors, front-door pointers, `Atoms`.
The SAT crate's anchors in `src/mltl-sat/README.md` move while that crate
is edited; rerun `scripts/readme_links.py --fix`.)

- `src/r2u2/README.md`, "How it is proved", ring bullet (found 2026-10-05):
  the queue sizes changed (D55). Now: 1 slot for the child of a `!` and for
  the root; for a child `c` of `&`/`U` with sibling `s`, `⌈(x + y)/2⌉ + 1`
  with `x = wpd(operands) − bpd(c)` and `y = wpd(s) − bpd(c)` (both cut at
  0), i.e. C2PO's size plus half of the old extra, rounded up. The line
  "whether any slot can be saved is open" is answered: rounding down is wrong
  (`agent-docs/verification/spikes/r2u2-sizing/`). Proposed text: "...with
  [`child_slots`] slots per queue — 1 for the child of a `!` and for the
  root; for the other children, C2PO's size plus half of the extra the
  slower child needs (rounded up; [`half.rs`](src/half.rs)). Rounding down
  is not enough." The `child_slots` anchor moved (rerun
  `scripts/readme_links.py --fix`).
