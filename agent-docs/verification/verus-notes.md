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

## Verify command for this repo (T1.2, 2026-10-02)
- `scripts/verify.sh` → `cargo verus verify --workspace` (exit non-zero on any
  failure). Extra args go to `cargo verus verify`, e.g.
  `scripts/verify.sh -p mltl-core`.
- Workspace: root `Cargo.toml`, members `src/<crate>`. Each crate sets
  `[package.metadata.verus] verify = true` and `[lints] workspace = true`.
- `vstd` comes from crates.io, pinned in `[workspace.dependencies]` to
  `=0.0.0-2026-09-20-0158` — the version `cargo verus new` emits for Verus
  0.2026.09.27. When upgrading Verus, run `cargo verus new --lib /tmp/x` and
  copy its vstd pin.
- First run verifies vstd itself (2059 items, ~20 s); later runs reuse cargo's
  cache. Re-verification is content-based: editing a file re-verifies,
  `touch` alone does not. Checked 2026-10-02 (introducing a false assert →
  errors; reverting → passes).
- Plain `cargo build` also works (ghost code erased).

## Gotchas (all observed with Verus 0.2026.09.27.3cf1832)
- **`Set` is finite, `ISet` is possibly infinite.** In this vstd, `Set<A>` is
  finite-only and `Set::new(pred)` returns `Option<Set<A>>`. Isabelle's
  `'a set` may be infinite → use `ISet<A>` for trace states (D13).
  `ISet::new`, `ISet::empty().insert(x)`; lemmas:
  `broadcast use vstd::iset::group_iset_lemmas;`. No `iset!` macro found.
- **Don't put `#[trigger]` on a recursive call inside a recursive spec fn's
  quantifier.** E.g. `exists|i: nat| i <= b && #[trigger] sem(pi.skip(i), *g)`
  makes the body unprovable from outside (the recursive call is encoded with
  fuel, so the user-facing term never matches). Minimal repro: spike
  `spikes/recursive-trigger-repro.rs` (v2/v4 fail, v1/v3 pass). Fix: omit the trigger and let
  Verus choose; it picks `drop(pi, i)`. Then **in proofs, also trigger on
  `drop(pi, k)`**, e.g. `forall|k| ... ==> !semantics(#[trigger] drop(pi, k), g)`
  — triggering on `semantics(...)` in proof quantifiers fails the same way.
- **Default fuel is 1.** Concrete examples nesting operators need
  `reveal_with_fuel(semantics, n)` (n = nesting depth).
- **`Seq::skip(i)` requires `i <= len`.** Isabelle `drop` is total, so the
  spike defines `drop(pi, i) = if i <= len { skip(i) } else { empty }` plus
  `lemma_drop_drop` (drop composes) and `lemma_drop_past_end`.
- **Loops with `break`** need a loop `ensures` clause for facts established
  on the break path (invariants alone only cover iterations that continue).
- `i = i + 1` on `usize` near a `b` bound may overflow; restructure loops to
  break at `i == hi` rather than iterate to `hi + 1`.
- Loop invariants must restate every fact used after/inside the loop (e.g.
  `rem > a`, `*f == Formula::Future(a, b, *g)` for the termination check of a
  recursive call inside the loop).

## Spikes
- `spikes/m1-semantics-spike.rs` (T1.4, 2026-10-02, VERIFIED: 14 verified,
  0 errors; not part of the build). Contains: generic `Formula<A>` enum with
  `Box` children and `usize` bounds; full `semantics` spec over
  `Seq<ISet<A>>` (all 10 cases); total `drop`; the three `MLTL_Encoding.thy`
  example lemmas; `Vec<Vec<bool>>` trace with view to `Seq<ISet<nat>>`;
  `view_f: Formula<usize> -> Formula<nat>`; exec `eval` proved equal to
  `semantics` for True/False/Prop/Not/And/Or/Future (loop over `[a, min(b, rem)]`).
  Starting point for T2.2–T2.7.
