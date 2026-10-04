//! CNF over DIMACS literals (`i32`: `x` is variable `x` positive, `-x`
//! negative, `0` is not a literal) and a verified model check.
//!
//! This is the executable CNF that is handed to an external SAT solver and
//! that the LRAT checker (`lrat.rs`) checks proofs against. `lit_view` maps
//! it to `Literal<nat>` of `cnf.rs`.
use vstd::prelude::*;
use crate::cnf::*;

verus! {

/// Variable of a DIMACS literal (`|l|`).
pub open spec fn var_of(l: i32) -> int {
    if l < 0 { -(l as int) } else { l as int }
}

/// A literal whose variable is below `nv` (and that can be negated).
pub open spec fn lit_ok(l: i32, nv: int) -> bool {
    l != 0 && l != i32::MIN && var_of(l) < nv
}

pub open spec fn clause_ok(c: Seq<i32>, nv: int) -> bool {
    forall|j: int| 0 <= j < c.len() ==> lit_ok(#[trigger] c[j], nv)
}

pub open spec fn dimacs_lit_sem(v: spec_fn(nat) -> bool, l: i32) -> bool {
    if l > 0 { v(l as nat) } else { !v(var_of(l) as nat) }
}

pub open spec fn dimacs_clause_sem(v: spec_fn(nat) -> bool, c: Seq<i32>) -> bool {
    exists|j: int| 0 <= j < c.len() && dimacs_lit_sem(v, #[trigger] c[j])
}

pub open spec fn dimacs_models(v: spec_fn(nat) -> bool, f: Seq<Seq<i32>>) -> bool {
    forall|i: int| 0 <= i < f.len() ==> dimacs_clause_sem(v, #[trigger] f[i])
}

pub open spec fn dimacs_satisfiable(f: Seq<Seq<i32>>) -> bool {
    exists|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f)
}

/// `F ⊫ C`: every model of `F` satisfies `C`.
pub open spec fn dimacs_entails(f: Seq<Seq<i32>>, c: Seq<i32>) -> bool {
    forall|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f) ==> dimacs_clause_sem(v, c)
}

/// The clauses of an executable CNF as sequences.
pub open spec fn cnf_seqs(f: Seq<Vec<i32>>) -> Seq<Seq<i32>> {
    Seq::new(f.len(), |i: int| f[i]@)
}

/// DIMACS literal as a `Literal<nat>`.
pub open spec fn lit_view(l: i32) -> Literal<nat> {
    if l > 0 { Literal::Pos(l as nat) } else { Literal::Neg(var_of(l) as nat) }
}

pub open spec fn clause_view(c: Seq<i32>) -> Seq<Literal<nat>> {
    Seq::new(c.len(), |j: int| lit_view(c[j]))
}

pub open spec fn cnf_view(f: Seq<Seq<i32>>) -> Seq<Seq<Literal<nat>>> {
    Seq::new(f.len(), |i: int| clause_view(f[i]))
}

/// The DIMACS semantics is `cnf_semantics` of the view.
pub proof fn dimacs_models_view(v: spec_fn(nat) -> bool, f: Seq<Seq<i32>>)
    ensures
        dimacs_models(v, f) == cnf_semantics(v, cnf_view(f)),
{
    assert forall|i: int| 0 <= i < f.len() implies dimacs_clause_sem(v, #[trigger] f[i])
        == clause_semantics(v, cnf_view(f)[i]) by {
        let c = f[i];
        if dimacs_clause_sem(v, c) {
            let j = choose|j: int| 0 <= j < c.len() && dimacs_lit_sem(v, #[trigger] c[j]);
            assert(lit_semantics(v, clause_view(c)[j]));
        }
        if clause_semantics(v, clause_view(c)) {
            let j = choose|j: int| 0 <= j < c.len() && lit_semantics(v, #[trigger] clause_view(c)[j]);
            assert(dimacs_lit_sem(v, c[j]));
        }
    }
    if cnf_semantics(v, cnf_view(f)) {
        assert forall|i: int| 0 <= i < f.len() implies dimacs_clause_sem(v, #[trigger] f[i]) by {
            assert(clause_semantics(v, cnf_view(f)[i]));
        }
    }
    if dimacs_models(v, f) {
        assert forall|i: int| 0 <= i < cnf_view(f).len() implies clause_semantics(v, #[trigger] cnf_view(f)[i]) by {
            assert(dimacs_clause_sem(v, f[i]));
        }
    }
}

pub proof fn dimacs_satisfiable_view(f: Seq<Seq<i32>>)
    ensures
        dimacs_satisfiable(f) == cnf_satisfiable(cnf_view(f)),
{
    if dimacs_satisfiable(f) {
        let v = choose|v: spec_fn(nat) -> bool| #[trigger] dimacs_models(v, f);
        dimacs_models_view(v, f);
    }
    if cnf_satisfiable(cnf_view(f)) {
        let v = choose|v: spec_fn(nat) -> bool| #[trigger] cnf_semantics(v, cnf_view(f));
        dimacs_models_view(v, f);
    }
}

/// The valuation given by a model vector (index = variable; out of range is
/// false).
pub open spec fn model_valuation(m: Seq<bool>) -> spec_fn(nat) -> bool {
    |x: nat| x < m.len() && m[x as int]
}

/// Verified model check: `true` means the model satisfies every clause.
pub fn check_model(f: &Vec<Vec<i32>>, model: &Vec<bool>) -> (r: bool)
    ensures
        r ==> dimacs_models(model_valuation(model@), cnf_seqs(f@)),
        r ==> dimacs_satisfiable(cnf_seqs(f@)),
{
    let mut i: usize = 0;
    while i < f.len()
        invariant
            i <= f.len(),
            forall|k: int| 0 <= k < i ==> dimacs_clause_sem(model_valuation(model@), #[trigger] cnf_seqs(f@)[k]),
        decreases f.len() - i,
    {
        let c = &f[i];
        let mut j: usize = 0;
        let mut found = false;
        while j < c.len() && !found
            invariant
                j <= c.len(),
                found ==> dimacs_clause_sem(model_valuation(model@), c@),
            decreases c.len() - j,
        {
            let l = c[j];
            if l != 0 && l != i32::MIN {
                let x: usize = if l > 0 { l as usize } else { (-l) as usize };
                if x < model.len() && model[x] == (l > 0) {
                    assert(x as int == var_of(l));
                    assert(model_valuation(model@)(x as nat) == (x < model@.len() && model@[x as int]));
                    if l > 0 {
                        assert(l as nat == x as nat);
                    }
                    assert(dimacs_lit_sem(model_valuation(model@), c@[j as int]));
                    found = true;
                }
            }
            j += 1;
        }
        if !found {
            return false;
        }
        assert(cnf_seqs(f@)[i as int] == c@);
        i += 1;
    }
    assert(dimacs_models(model_valuation(model@), cnf_seqs(f@)));
    true
}

} // verus!
