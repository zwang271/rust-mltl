# Architecture (PROPOSED — nothing built yet)

Status: PLANNED, 2026-10-02. Revise freely; record real decisions in
`../decisions.md`.

## Shape
A Cargo workspace inside `rust-mltl/` whose crates live under `src/`:

```
rust-mltl/
  Cargo.toml            # workspace
  src/
    mltl-core/          # shared foundation (goal 2)
      syntax            # Formula<A> enum mirroring Isabelle `'a mltl`; spec + exec
      semantics         # spec fn semantics(trace: Seq<Set<A>>, f) mirroring semantics_mltl
      props             # intervals_welldef, convert_nnf, complen, depth, subformulas + lemmas
      trace             # exec trace repr ↔ Seq<Set<A>> view
    mltl-parse/         # verified parser/printer (goal 6)
    west/               # WEST (goal 4) — or a wrapper around the in-place WEST repo
    progression/        # formula progression (goal 5)
    lang-partition/     # language partitioning (goal 5); mltl_ext lives here or in core
    sat/                # MLTL SAT solver
    r2u2/               # R2U2 in-place verification (goal 3) — see open question Q1
```

## Cross-cutting design points (to settle as we go)
- **Atoms.** Isabelle is polymorphic in `'a`; WEST and R2U2 fix `nat`. Core
  should be generic over the atom type where Verus allows, with `nat`/`u32`
  instantiations.
- **nat vs machine ints.** Spec uses `nat`; exec uses `u32`/`u64`/`usize`
  with overflow preconditions. Interval bounds' arithmetic (`b-1`, `a+b`) needs
  careful bridging — Isabelle `nat` subtraction truncates.
- **Traces.** Spec trace = `Seq<Set<A>>` (matches `'a set list`). Exec trace for
  `nat` atoms = bit-vectors / `Vec<Vec<bool>>`; prove a `view`.
- **Recursion over formulas.** Verus needs `decreases` on `Box`ed enums; check
  current Verus support for `Box<Formula>` in spec/exec and `height` measures.
- **Shared lemmas** (NNF preserves semantics, semantic_equiv is an equivalence,
  etc.) belong in core so all algorithms reuse them.
- **In-place targets** (R2U2, WEST) prove their own specs and then a bridge
  lemma to `mltl-core` semantics.
