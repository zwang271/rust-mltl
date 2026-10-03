# Verus notes

Practical knowledge about running Verus here. Add gotchas as you hit them
(what failed, error text, fix).

## Toolchain (2026-10-02)
- Verus not installed. Version choice open (Q4 in `../open-questions.md`).
- Upstream `r2u2_core`: `vstd = "0.0.0-2025-08-12-1837"`, `rust-toolchain.toml`
  channel `1.85.1`. Upstream verify recipe
  (`ROOT/r2u2/monitors/rust/docs/dev/verification.md`): `cargo build -v`, copy
  the `-L` paths except vstd, then
  `verus --crate-type=lib src/lib.rs --compile -L <paths>`.
- Consider `cargo verus` (newer Verus releases) for workspace integration —
  check availability when installing.

## Verify command for this repo
TBD — fill in once Phase 1 sets up the workspace.

## Gotchas
(none recorded yet)
