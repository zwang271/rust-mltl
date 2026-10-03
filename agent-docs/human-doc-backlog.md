# Human-doc backlog

Human-facing docs (anything outside `agent-docs/` except `AGENTS.md`) that an
agent believes are stale or wrong. Agents may not fix these without a human
request (AGENTS.md §3.2). List: file, what's wrong, proposed text, date found.
Remove an entry once a human has had it applied.

- `README.md` "Status: Early setup; no code yet." — will go stale as soon as
  Phase 1 lands. (2026-10-02)
- `src/mltl-eval/EVAL_MLTL.md` §6 last paragraph ("The two ideas also combine…") calls the streaming sliding window a hybrid without saying it is close to R2U2 or how it differs (buffers operand windows of width w vs R2U2's sibling-delay buffers; data-oblivious, so batchable). Proposed text: see `project/m10-batched-eval.md` §6. (2026-10-03)
- `src/mltl-eval/EVAL_MLTL.md` §5 measurements come from the first, ad-hoc comparison (libmltl's `benchmark.cc`, non-identical traces). Proposed: replace with a pointer to `benchmarks/` and its plots (identical inputs, growth exponents). Also mention short-trace disagreement observed there. (2026-10-03)
