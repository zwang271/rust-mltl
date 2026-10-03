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

## IDE support (2026-10-02)
- Plain rust-analyzer "doesn't work" on Verus code: outside Verus, `verus!`
  erases spec/proof fns and specs, so RA sees almost nothing (checked
  `rust-analyzer analysis-stats .`: 11 bodies for 256-line `mltl.rs`). RA
  itself loads the workspace fine (no diagnostics, correct cwd).
- Fix: VS Code extension `verus-lang.verus-analyzer` (Verus' RA fork), with
  rust-analyzer disabled for this workspace. Installed v0.3.269 via `code
  --install-extension` 2026-10-02; disabling RA per-workspace is manual (UI).
- verus-analyzer labels its diagnostics "rust-analyzer" (it's a fork), so
  errors that look like RA's come from it. False positive seen 2026-10-03:
  "cannot index into a value of type `Seq<bool>`" (E0608) on spec-mode
  `s[i]`; Verus verifies the code. Silenced in local, gitignored
  `.vscode/settings.json`: `"verus-analyzer.diagnostics.disabled": ["E0608"]`.

## Gotchas (all observed with Verus 0.2026.09.27.3cf1832)
- **`Set` is finite, `ISet` is possibly infinite.** In this vstd, `Set<A>` is
  finite-only and `Set::new(pred)` returns `Option<Set<A>>`. Isabelle's
  `'a set` may be infinite, but we use finite `Set<A>` for trace states by
  owner decision (D16, supersedes D16). `ISet` notes kept for reference:
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

- **Predicates over constructors need the constructor term.** With
  `requires forall|q| #[trigger] p(Mltl::Prop(q))`, proving `p(f)` in a
  `Mltl::Prop(_)` match arm fails: the arm doesn't create the term
  `Mltl::Prop(q)`, so the trigger never fires. Bind the field and assert
  `p(Mltl::Prop(q))` (or `p(Mltl::And(Box::new(*f1), Box::new(*f2)))`).
  Or-patterns across constructors (`And(..) | Or(..) => ...`) can't do this —
  split them into one arm per constructor (seen in `nnf_induct`, 2026-10-02).
- **rlimit after adding unrelated definitions.** `release_until_dual2` passed,
  then hit "Resource limit (rlimit) exceeded" once more definitions existed in
  the file. Fix that worked: move the fuel-3 unfolding into a small helper
  lemma (`not_until_not_unfold`) so the main proof runs at fuel 1. Also:
  `assert(goal) by { ... }` per case. Don't raise rlimit as a first resort.
- **`decreases ... via f`** for non-structural measures: syntax
  `decreases depth_mltl(f), via convert_nnf_decreases::<A>` (needs the
  turbofish for generic fns, else E0282), plus `#[via_fn] proof fn
  convert_nnf_decreases<A>(f: Mltl<A>) { ... }` with the same params; inside,
  `reveal_with_fuel` the measure and assert the per-call inequalities.
- **Closures as predicates**: `let p = |k: nat| semantics_mltl(drop(pi, k), psi);`
  works as `spec_fn(nat) -> bool`; facts `forall k. p(k)` must be
  instantiated with `assert(p(k))` before Z3 sees the body.
- `assert(false); arbitrary()` is fine for unreachable arms of proof fns
  returning a value (not trusted: `assert(false)` is proved).

- **Cross-query solver interference.** In the full run, proofs that passed
  before (`release_until_dual2`, `convert_nnf_preserves_semantics`) hit rlimit
  after more functions were added to the module, yet passed in isolation.
  Fix: `#[verifier::spinoff_prover]` on the heavy function (fresh Z3 instance;
  soundness unaffected, not a trust item). Splitting a big proof into small
  case lemmas (e.g. `mltl_eval_correct_*`) is the other fix.
- **Verifying one function**: `cargo verus focus -- --verify-only-module properties --verify-function NAME`
  (`cargo verus verify` refuses partial selectors; `--verify-module` +
  `--verify-function` is rejected). Repeated `focus` runs with different
  selectors may be served from cache — change file contents to force a re-run.
- **Mutual recursion fuel**: for `mltl_eval`/`mltl_eval_unchecked`, unfolding
  the checked fn into the unchecked one needs `reveal_with_fuel(mltl_eval, 2)`
  and `reveal_with_fuel(mltl_eval_unchecked, 2)`. Lexicographic decreases:
  `decreases depth_mltl(f), width(f), 1nat` / `..., 0nat`, each with its own
  `via` fn.
- **Two-sided triggers** for relating two traces: when facts relate
  `drop(pi, i)` and `drop(pi2, i)`, give both triggers
  (`forall|i| #![trigger drop(pi, i)] #![trigger drop(pi2, i)] ...`), else
  only one direction of an ∃/∀ unfolding instantiates (`atomics_agree_semantics`).

- **Termination of a recursive call inside a loop needs the accessor term.**
  With `requires/invariant *f == M::F(a, *g)` and a call `ev(g, ..)` inside a
  `loop`/`while`, Verus reported "could not prove termination" — the
  height-ordering fact only fires on accessor terms. Fix: `proof {
  assert(f->F_1 == *g); }` before the call (minimal repro 2026-10-03:
  20-line file, fails without, passes with). In `eval.rs`:
  `assert(f->Future_2 == *g)`, `assert(f->Until_0 == *g && f->Until_3 == *h)`.
- **`f is Variant` is spec-only**: "cannot test variant in exec mode" — use
  `match f { Mltl::And(_, _) => true, _ => false }` in exec code.
- **`HashSet<usize>` in exec**: `broadcast use vstd::std_specs::hash::group_hash_axioms;`
  then `t[i].contains(&q)` ensures `== t@[i]@.contains(q)` (needs
  `obeys_key_model::<usize>()` and `builds_valid_hashers`, both provided by
  the group). Trace view: `t.map_values(|s: HashSet<usize>| s@)`.
- Plain `cargo test`/`cargo run --release` compile the verified code with
  ghost code erased; used for `tests/eval_agree.rs` and the benchmark driver
  (`src/mltl-core/benchmarks/driver.rs`, declared as `[[example]]` with a
  custom `path` in `src/mltl-core/Cargo.toml`). Plain builds emit
  unused-variable/import warnings for ghost-only bindings — expected.

## Spikes
- `spikes/m1-semantics-spike.rs` (T1.4, 2026-10-02, VERIFIED: 14 verified,
  0 errors; not part of the build). Contains: generic `Formula<A>` enum with
  `Box` children and `usize` bounds; full `semantics` spec over
  `Seq<ISet<A>>` (all 10 cases); total `drop`; the three `MLTL_Encoding.thy`
  example lemmas; `Vec<Vec<bool>>` trace with view to `Seq<ISet<nat>>`;
  `view_f: Formula<usize> -> Formula<nat>`; exec `eval` proved equal to
  `semantics` for True/False/Prop/Not/And/Or/Future (loop over `[a, min(b, rem)]`).
  Starting point for T2.2–T2.7.
