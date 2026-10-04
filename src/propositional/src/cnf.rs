//! Literals, clauses and CNF.
//!
//! Mirrors AFP `Propositional_Proof_Systems`: `CNF.thy` (`literal`),
//! `CNF_Sema.thy` (`lit_semantics`, `clause_semantics`, `cnf_semantics`) and
//! `CNF_Formulas.thy` (`form_of_lit`, `disj_of_clause`, `form_of_cnf`).
//! Isabelle's clauses are sets (`'a literal set`) for the semantics and
//! lists for `cnf_lists`/`form_of_cnf`; here both are lists (`Seq`), which is
//! the shape the REU MLTL encoder uses (`'a literal list list`).
use vstd::prelude::*;
use crate::formula::*;

verus! {

/// `datatype 'a literal = Pos 'a | Neg 'a`
pub enum Literal<A> {
    Pos(A),
    Neg(A),
}

/// `atoms_of_lit`
pub open spec fn atoms_of_lit<A>(l: Literal<A>) -> A {
    match l {
        Literal::Pos(k) | Literal::Neg(k) => k,
    }
}

/// `lit_semantics 𝒜 (k⁺) = 𝒜 k`, `lit_semantics 𝒜 (k⁻) = ¬𝒜 k`
pub open spec fn lit_semantics<A>(v: spec_fn(A) -> bool, l: Literal<A>) -> bool {
    match l {
        Literal::Pos(k) => v(k),
        Literal::Neg(k) => !v(k),
    }
}

/// `clause_semantics 𝒜 C ≡ ∃L ∈ C. lit_semantics 𝒜 L`
pub open spec fn clause_semantics<A>(v: spec_fn(A) -> bool, c: Seq<Literal<A>>) -> bool {
    exists|j: int| 0 <= j < c.len() && lit_semantics(v, #[trigger] c[j])
}

/// `cnf_semantics 𝒜 S ≡ ∀C ∈ S. clause_semantics 𝒜 C`
pub open spec fn cnf_semantics<A>(v: spec_fn(A) -> bool, f: Seq<Seq<Literal<A>>>) -> bool {
    forall|i: int| 0 <= i < f.len() ==> clause_semantics(v, #[trigger] f[i])
}

/// `∃𝒜. cnf_semantics 𝒜 F`
pub open spec fn cnf_satisfiable<A>(f: Seq<Seq<Literal<A>>>) -> bool {
    exists|v: spec_fn(A) -> bool| #[trigger] cnf_semantics(v, f)
}

/// `form_of_lit (Pos k) = Atom k`, `form_of_lit (Neg k) = ¬(Atom k)`
pub open spec fn form_of_lit<A>(l: Literal<A>) -> Formula<A> {
    match l {
        Literal::Pos(k) => Formula::Atom(k),
        Literal::Neg(k) => Formula::Not(Box::new(Formula::Atom(k))),
    }
}

/// `disj_of_clause c ≡ ⋁[form_of_lit l. l ← c]`
pub open spec fn disj_of_clause<A>(c: Seq<Literal<A>>) -> Formula<A> {
    big_or(c.map_values(|l: Literal<A>| form_of_lit(l)))
}

/// `form_of_cnf F ≡ ⋀[disj_of_clause c. c ← F]`
pub open spec fn form_of_cnf<A>(f: Seq<Seq<Literal<A>>>) -> Formula<A> {
    big_and(f.map_values(|c: Seq<Literal<A>>| disj_of_clause(c)))
}

pub proof fn form_of_lit_semantics<A>(v: spec_fn(A) -> bool, l: Literal<A>)
    ensures
        formula_semantics(v, form_of_lit(l)) == lit_semantics(v, l),
{
    reveal_with_fuel(formula_semantics, 3);
}

pub proof fn disj_of_clause_semantics<A>(v: spec_fn(A) -> bool, c: Seq<Literal<A>>)
    ensures
        formula_semantics(v, disj_of_clause(c)) == clause_semantics(v, c),
{
    let m = c.map_values(|l: Literal<A>| form_of_lit(l));
    big_or_semantics(v, m);
    if formula_semantics(v, disj_of_clause(c)) {
        let j = choose|j: int| 0 <= j < m.len() && formula_semantics(v, #[trigger] m[j]);
        form_of_lit_semantics(v, c[j]);
    }
    if clause_semantics(v, c) {
        let j = choose|j: int| 0 <= j < c.len() && lit_semantics(v, #[trigger] c[j]);
        form_of_lit_semantics(v, c[j]);
        assert(formula_semantics(v, m[j]));
    }
}

/// The semantics of `form_of_cnf` is `cnf_semantics` (Isabelle proves this
/// via `cnf_form_semantics`, for the set-based semantics).
pub proof fn form_of_cnf_semantics<A>(v: spec_fn(A) -> bool, f: Seq<Seq<Literal<A>>>)
    ensures
        formula_semantics(v, form_of_cnf(f)) == cnf_semantics(v, f),
{
    let m = f.map_values(|c: Seq<Literal<A>>| disj_of_clause(c));
    big_and_semantics(v, m);
    if formula_semantics(v, form_of_cnf(f)) {
        assert forall|i: int| 0 <= i < f.len() implies clause_semantics(v, #[trigger] f[i]) by {
            disj_of_clause_semantics(v, f[i]);
            assert(formula_semantics(v, m[i]));
        }
    }
    if cnf_semantics(v, f) {
        assert forall|i: int| 0 <= i < m.len() implies formula_semantics(v, #[trigger] m[i]) by {
            disj_of_clause_semantics(v, f[i]);
        }
    }
}

} // verus!
