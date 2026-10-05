# Verus notes

Practical knowledge about running Verus here. Add gotchas as you hit them
(what failed, error text, fix).

## Toolchain (installed 2026-10-02, T1.1)
- Verus `0.2026.09.27.3cf1832` (latest non-prerelease on 2026-10-02; a newer
  rolling prerelease `0.2026.10.02.f319e4d` existed and was skipped). Policy: D9.
- Source: the GitHub release asset for your platform
  (`verus-0.2026.09.27.3cf1832-<platform>.zip`). This machine's install
  layout: `../local-paths.md`.
- Requires Rust toolchain `1.98.1` for your platform (install with `rustup
  install`; Verus selects it itself via `RUSTUP_TOOLCHAIN`). `verus` prints
  the exact `rustup install` command if it is missing.
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
  20-line file, fails without, passes with). In `mltl-eval`:
  `assert(f->Future_2 == *g)`, `assert(f->Until_0 == *g && f->Until_3 == *h)`.
- **`f is Variant` is spec-only**: "cannot test variant in exec mode" — use
  `match f { Mltl::And(_, _) => true, _ => false }` in exec code.
- **`HashSet<usize>` in exec**: `broadcast use vstd::std_specs::hash::group_hash_axioms;`
  then `t[i].contains(&q)` ensures `== t@[i]@.contains(q)` (needs
  `obeys_key_model::<usize>()` and `builds_valid_hashers`, both provided by
  the group). Trace view: `t.map_values(|s: HashSet<usize>| s@)`.
- Plain `cargo test`/`cargo run --release` compile the verified code with
  ghost code erased; used for `tests/eval_agree.rs` and the benchmark driver
  (`src/mltl-eval/benchmarks/driver.rs`, declared as `[[example]]` with a
  custom `path` in `src/mltl-core/Cargo.toml`). Plain builds emit
  unused-variable/import warnings for ghost-only bindings — expected.

- **`&mut` parameters in postconditions** must be written `final(w)@`
  (and `old(w)@` for the entry value); plain `w@` is rejected ("disambiguate
  by wrapping it in either `old` or `final`").
- **Ghost closures don't unfold reliably.** `let ghost goal = |i| ...;` then
  `goal(x)` in assertions failed even with hints; writing the lambda inline
  (`Seq::new(n, |m: int| ...)`) worked.
- **Traits with spec methods work for generic proofs**: `trait AtomRead {
  spec fn view_trace(&self) -> ..; fn push_row(..) ensures ..; }`, generic
  `fn f<T: AtomRead + ?Sized>(t: &T)`, and `impl AtomRead for [HashSet<usize>]`
  all verify; proofs over the abstract `view_trace()` carried over unchanged.
- **Bit reasoning**: `assert(... ) by (bit_vector) requires k < 64u64;` proves
  facts like "setting bit k leaves other bits unchanged"; pair with
  `by (nonlinear_arith)` for `i / 64`, `i % 64` index facts.
- **Plain builds erase spec items**: a `pub use` of a spec fn from `lib.rs`
  breaks `cargo build` (E0432); re-export exec items only.

- **Fuel runs out one level down.** Unfolding `semantics_mltl(pi, Or(phi,
  psi))` at fuel 1 leaves `semantics_mltl(pi, phi)` with no fuel, so even
  `phi == False` facts don't fire: `False ∨ ψ ≡ ψ` failed until
  `reveal_with_fuel(semantics_mltl, 2)` inside the `assert forall` (seen in
  `formula_progression/src/simp.rs`, 2026-10-03). Same for nested results like
  `Or(x, And(y, Until(..)))`: give fuel = nesting depth.
- **Quantified ensures + big case split → rlimit.** A lemma ensuring
  `forall rho. …` over ten cases timed out; the same lemma with `rho` as a
  parameter verified instantly, wrapped by a 3-line `assert forall … by {
  lemma_at(.., rho) }` (`complen_one_len1_value_at`).
- **Exec pattern matching through boxes works**: `match &**g { … }` and
  `match (&**x, &**y) { (Mltl::Not(phi), Mltl::Not(psi)) => … }` verify, and
  structural `decreases f` accepts recursive calls on such nested bindings.
- **Loop until a flag clears**: `decreases size(cur) + if changed { 1nat }
  else { 0nat }` handles the last iteration where nothing shrinks
  (`simp_mltl`).
- **Moving out of a `Box` works** (Verus 0.2026.09.27): `match *g {..}`,
  `let x = *g;`, and re-filling with `*g = f(*g)` to reuse the allocation all
  verify; spec side reads `*f->Not_0` (the field is a `Box`).
- **A moved parameter loses its facts inside a loop**: with `let ghost f0 =
  f; let mut cur = f; while .. { .. return h; }`, `ensures r == spec(f, ..)`
  failed at the early `return` until the invariant restated `f0 == f`
  (`formula_progression_alt_owned`).
- **Importing proof fns by name breaks plain `cargo build`** (they are
  erased): `use crate::m::{some_lemma}` → E0432 outside Verus. Guard it with
  `#[cfg(verus_only)]` (glob imports are fine unguarded).
- **`return` inside a `while`** is fine; the function's `ensures` is checked
  at the return (`formula_progression_alt`).

- **No implicit `nat` → `int` coercion in calls** (`hi + n` is `int`):
  cast `(hi + n) as nat` at the argument (language partitioning).
- **Identical closures are equal terms**: a spec fn's `Seq::new(m, |j| f(j))`
  and the same lambda written in a lemma or loop invariant compare equal
  without `=~=` (`LP_mltl_aux_spec(..) == lp_future_list(..)`).
- **Mutual recursion lemma + helper at the same `k`**: main `decreases k,
  0nat`, helper `decreases k, 1nat` (helper calls main at `k`, main calls
  helper at `k-1`). Reversed, Verus reports "could not prove termination".
- **Exec values built inline lose their views**: in `Global(single_vec(x),
  .., Box::new(Not(Vec::new(), ..)))` the view of the nested nodes failed;
  bind each part (`let nv = Vec::new(); let body = Not(nv, ..)`), assert
  `nv@ =~= Seq::empty()`, and give the view fn fuel 3.
- **A conjunctive `assert forall` gets one trigger**: `assert forall|j| ..
  implies #[trigger] sat(xs[j]) == .. && disjoint(xs[j])` did not satisfy a
  later `requires forall|j| disjoint(#[trigger] xs[j])`; use
  `#![trigger xs[j]]`.
- **rlimit on assembly lemmas**: when a lemma combines several lifted facts
  with existentials, move each piece into a small lemma and pass a `spec_fn`
  (`head_concat_sat`, `single_head_disjoint`); `spinoff_prover` alone did
  not help.

- **Re-running Verus needs a content change** (seen 2026-10-04): `cargo
  verus verify -p X` after only `touch` reuses the cached result and prints
  just "Finished". Append and remove a comment line in `lib.rs` to force a
  real run.
- **Private fields + public specs**: a `pub` fn's `requires`/`ensures` may not
  name private fields ("field expression for an opaque datatype"). Use
  `pub closed spec fn` accessors, or `pub open(crate) spec fn` when other
  modules of the crate must see the body (`mltl-sat` `Encoding::inv`).
- **`-x` on an `i32` in spec code is `int`**: `seq![-x, y]` is `Seq<int>`;
  bind `let nx: i32 = -x;` in exec and use `nx` (`mltl-sat/src/encode.rs`).
- `slice::reverse` has no vstd spec; iterate by index instead.

- **Arithmetic in triggers doesn't fire on constants** (WEST, 2026-10-04):
  `forall|p| p < 32 ==> #[trigger] bit(z, 2 * p) || ..` never instantiated
  for `assert(bit(z, 0) || bit(z, 1))`. Name the body
  (`pair_ok(z, p)`) and trigger on that; then `assert(pair_ok(z, 0))` works.
- **`nonlinear_arith` sees only its `requires`**: facts like `s == 2*n*k`
  from `let` bindings must be passed in `requires`, and spec fns (e.g.
  `fits`) must be written out, or the query fails.
- **Exec `e - 1` vs bit-vector `sub(e, 1u64)`**: equal when `e != 0`, but
  needs `assert(x == e & sub(e, 1u64)) by (bit_vector) requires e != 0u64,
  x == e & ((e - 1) as u64)`.
- **Facts before a loop are gone inside it**: a `proof { lemma(..) }` before
  a `while` did not help an early `return` inside the loop; call the lemma
  at the return (WEST `WEST_and_state`).
- **A shadowed, moved parameter in `ensures`**: `fn f(l: T) ensures ..l..
  { let mut l = l; loop {..} }` failed at the return; rename the parameter
  (`input`) and keep `ghost l0 == view(input)` plus `target == spec(l0)` in
  the invariant.
- **Quantified-ensures lemmas over arithmetic index terms**: a lemma
  ensuring `forall a, b. P[off(a) + (b - a - 1)] == (a, b)` was
  unusable/unprovable; the same lemma with `a, b` as parameters worked.

## Spikes
- `spikes/m1-semantics-spike.rs` (T1.4, 2026-10-02, VERIFIED: 14 verified,
  0 errors; not part of the build). Contains: generic `Formula<A>` enum with
  `Box` children and `usize` bounds; full `semantics` spec over
  `Seq<ISet<A>>` (all 10 cases); total `drop`; the three `MLTL_Encoding.thy`
  example lemmas; `Vec<Vec<bool>>` trace with view to `Seq<ISet<nat>>`;
  `view_f: Formula<usize> -> Formula<nat>`; exec `eval` proved equal to
  `semantics` for True/False/Prop/Not/And/Or/Future (loop over `[a, min(b, rem)]`).
  Starting point for T2.2–T2.7.
- (2026-10-03, parser) Postconditions on `&mut` args must say `final(x)` (or
  `old(x)`); `decreases_to!` is unavailable here; spec-only items imported by
  name break plain `cargo build` (use glob imports). Parser-specific proof
  patterns: `modules/mltl-parse.md`.

- **rlimit in tree simulations (2026-10-04, `r2u2/src/ring_sim.rs`).** One
  lemma simulating a pass over all node kinds hit rlimit. Fix: one lemma
  per node kind with the children's results as `requires` (`sim_ok`), a
  tiny dispatcher, explicit equality chains for the node's update tuple
  (`assert(mltl_update_r(t, ..) == (Node(nd, Box::new(c2)), ..))`), and
  `#[verifier::spinoff_prover]`. Two of them (`lemma_sim_and`,
  `lemma_sim_until`) still need `#[verifier::rlimit(100)]` (scheduling, not
  trust).
- **Tightening a uniform bound to a per-item one (2026-10-04,
  `r2u2/src/ring_sim.rs`).** Going from "all children of a node get `w + 1`
  slots" to "child `c` gets `w_c + 1`" cost almost no proof rework because
  the pointer lemmas already took `w` and the coverage bound as parameters:
  the edit was to replace the two hard-wired expressions (`w` for the slack,
  `n + 1` for the child's coverage bound) with parameters (`w`, `cap`) and
  add one arithmetic lemma relating them (`lemma_cap_slack`). Lesson: when a
  size or deadline appears in an invariant, pass it in rather than computing
  it inside — the invariant then tightens by changing call sites only.
  `nat_sub` arithmetic (`nat_sub(nat_sub(k,b), nat_sub(w,b)+1) ≤
  nat_sub(k,w+1)`) went through with an empty proof body.
- `nat % int` does not type-check: write `x as int % (n as int)`.
- Named imports of spec fns (`use m::f;`) break the plain `cargo build`
  (spec fns are erased); use glob imports.

