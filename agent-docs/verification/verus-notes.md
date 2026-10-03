# Verus notes

Practical knowledge about running Verus here. Add gotchas as you hit them
(what failed, error text, fix).

## Toolchain (installed 2026-10-02, T1.1)
- Verus `0.2026.09.27.3cf1832` (latest non-prerelease on 2026-10-02; a newer
  rolling prerelease `0.2026.10.02.f319e4d` existed and was skipped). Policy: D9.
- Source: GitHub release asset `verus-0.2026.09.27.3cf1832-arm64-macos.zip`.
- Install layout on owner's machine: `~/.verus/<version>/verus-arm64-macos/`;
  `~/.verus/current` symlink → active version; `~/.cargo/bin/verus` and
  `~/.cargo/bin/cargo-verus` symlink into `~/.verus/current/`. To upgrade:
  unzip new version, repoint `current`, install its rust toolchain.
- Requires rust toolchain `1.98.1-aarch64-apple-darwin` (installed via
  `rustup install`; Verus selects it itself via `RUSTUP_TOOLCHAIN`). `verus`
  prints the exact `rustup install` command if missing.
- Bundled Z3 4.16.0.
- `cargo verus` subcommands: `new`, `toolchain`, `verify`, `focus`, `build`,
  `check`. Plan to use `cargo verus verify` for the workspace (T1.2).
- Smoke test: a 2-item file (spec fn + proof fn) → `verus /tmp/verus_smoke.rs`
  → `verification results:: 2 verified, 0 errors`.
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
