//! Deciding MLTL satisfiability with an untrusted SAT solver.
//!
//! `Encoding::decide` takes whatever the solver said and returns an answer
//! that is checked here: a trace is returned only if the verified evaluator
//! confirms it satisfies the formula, and "unsatisfiable" only if the
//! verified LRAT checker accepts the solver's proof against the encoding's
//! own CNF. Anything else is `Unknown`.
use vstd::prelude::*;
use std::collections::HashSet;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use mltl_eval::trace::*;
use mltl_eval::top_down::mltl_eval;
use propositional::dimacs::*;
use propositional::lrat::{check_lrat, LratStep};
use crate::table::*;
use crate::encode::*;
use crate::fast::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// What the SAT solver claims (unverified input).
pub enum SolverOutput {
    /// A model, indexed by variable (`model[0]` unused).
    Sat(Vec<bool>),
    /// A refutation of the CNF.
    Unsat(Vec<LratStep>),
    Unknown,
}

/// A checked answer.
pub enum Answer {
    /// A satisfying trace of length `complen φ`.
    Sat(Vec<HashSet<usize>>),
    /// No trace of length `complen φ` satisfies `φ`.
    Unsat,
    /// The solver's claim could not be checked.
    Unknown,
}

impl Encoding {
    /// The trace a model induces: `val_to_trace` of the read-back valuation.
    pub open(crate) spec fn decoded_w(&self, w: spec_fn(nat) -> bool) -> Seq<Set<usize>> {
        val_to_trace(restrict(w, self.table.sub@, self.n as nat), self.n as nat, table_props(self.table.nodes@))
    }

    pub open(crate) spec fn decoded(&self, model: Seq<bool>) -> Seq<Set<usize>> {
        self.decoded_w(model_valuation(model))
    }

    /// Trace whose state at `t` holds atom `p` iff the model sets `(p, t)`.
    fn decode(&self, model: &Vec<bool>) -> (r: Vec<HashSet<usize>>)
        requires
            self.inv(),
        ensures
            r@.len() == self.n,
            trace_view(r@) == self.decoded(model@),
    {
        let n = self.n;
        let ghost w = model_valuation(model@);
        let ghost sub = self.table.sub@;
        let ghost nodes = self.table.nodes@;
        let ghost v = restrict(w, sub, n as nat);
        let ghost ap = table_props(nodes);
        let ghost target = self.decoded(model@);
        let mut trace: Vec<HashSet<usize>> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                self.inv(),
                n == self.n,
                k <= n,
                trace@.len() == k,
                w == model_valuation(model@),
                sub == self.table.sub@,
                nodes == self.table.nodes@,
                v == restrict(w, sub, n as nat),
                ap == table_props(nodes),
                target == self.decoded(model@),
                forall|t: int| 0 <= t < k ==> #[trigger] trace@[t]@ == target[t],
            decreases n - k,
        {
            let mut state: HashSet<usize> = HashSet::new();
            let mut id: usize = 0;
            while id < self.table.nodes.len()
                invariant
                    self.inv(),
                    n == self.n,
                    k < n,
                    id <= nodes.len(),
                    w == model_valuation(model@),
                    sub == self.table.sub@,
                    nodes == self.table.nodes@,
                    forall|p: usize| #[trigger] state@.contains(p) == exists|j: nat|
                        j < id && nodes[j as int] == Node::Prop(p) && w(bvar(n as nat, j, k as nat) as nat),
                decreases nodes.len() - id,
            {
                let ghost s0 = state@;
                match &self.table.nodes[id] {
                    Node::Prop(p) => {
                        let x = bv_pub(&self.table, n, id, k);
                        if (x as usize) < model.len() && model[x as usize] {
                            state.insert(*p);
                        }
                    },
                    _ => {},
                }
                proof {
                    assert forall|q: usize| #[trigger] state@.contains(q) == exists|j: nat|
                        j < id + 1 && nodes[j as int] == Node::Prop(q) && w(bvar(n as nat, j, k as nat) as nat) by {
                        if exists|j: nat| j < id + 1 && nodes[j as int] == Node::Prop(q) && w(bvar(n as nat, j, k as nat) as nat) {
                            let j = choose|j: nat| j < id + 1 && nodes[j as int] == Node::Prop(q) && w(bvar(n as nat, j, k as nat) as nat);
                            if j < id {
                                assert(s0.contains(q));
                            }
                        }
                        if s0.contains(q) {
                            let j = choose|j: nat| j < id && nodes[j as int] == Node::Prop(q) && w(bvar(n as nat, j, k as nat) as nat);
                        }
                    }
                }
                id += 1;
            }
            proof {
                let tk = target[k as int];
                assert(tk == ap.filter(|p: usize| v((Mltl::Prop(p), k as nat))));
                assert forall|p: usize| state@.contains(p) == tk.contains(p) by {
                    table_props_contains(nodes, p);
                    if state@.contains(p) {
                        let j = choose|j: nat| j < nodes.len() && nodes[j as int] == Node::Prop(p) && w(bvar(n as nat, j, k as nat) as nat);
                        sub_prop_iff(nodes, sub, j as int, p);
                        let pr: Var<usize> = (Mltl::Prop(p), k as nat);
                        assert(j < sub.len() && sub[j as int] == pr.0 && pr.1 < n);
                        assert(w(bvar(n as nat, j, pr.1) as nat));
                        assert(restrict(w, sub, n as nat)(pr));
                    }
                    if tk.contains(p) {
                        assert(restrict(w, sub, n as nat)((Mltl::Prop(p), k as nat)));
                        let j = choose|j: nat| j < sub.len() && sub[j as int] == Mltl::<usize>::Prop(p) && (k as nat) < n && #[trigger] w(bvar(n as nat, j, k as nat) as nat);
                        sub_prop_iff(nodes, sub, j as int, p);
                    }
                }
                assert(state@ =~= tk);
            }
            trace.push(state);
            k += 1;
        }
        proof {
            assert(trace_view(trace@) =~= target);
        }
        trace
    }

    /// A model of the CNF decodes to a trace satisfying the formula
    /// (`assign_agrees_trace` at the root).
    proof fn model_decodes(&self, model: Seq<bool>)
        requires
            self.inv(),
            dimacs_models(model_valuation(model), cnf_seqs(self.cnf@)),
        ensures
            semantics_mltl(self.decoded(model), self.phi),
    {
        self.model_decodes_w(model_valuation(model));
    }

    proof fn model_decodes_w(&self, w: spec_fn(nat) -> bool)
        requires
            self.inv(),
            dimacs_models(w, cnf_seqs(self.cnf@)),
        ensures
            semantics_mltl(self.decoded_w(w), self.phi),
            self.decoded_w(w).len() == self.n,
    {
        let g = convert_bnf_spec(self.phi);
        let v = restrict(w, self.table.sub@, self.n as nat);
        let ap = table_props(self.table.nodes@);
        convert_bnf_is_bnf(self.phi);
        convert_bnf_welldef(self.phi);
        convert_bnf_complen(self.phi);
        convert_bnf_equiv(self.phi);
        atoms_in_table(self.table.nodes@, self.table.sub@, self.root as int);
        assign_agrees_trace(v, g, 0, 0, self.n as nat, ap, 0);
        let pi = self.decoded_w(w);
        lemma_drop_zero(pi);
        assert(semantics_mltl(pi, g));
    }

    /// The CNF is equisatisfiable with `MLTL_SAT_LEN φ (complen φ)`
    /// (the counterpart of the Isabelle `mltl_dimacs_correct`).
    pub proof fn equisatisfiable(&self)
        requires
            self.inv(),
        ensures
            dimacs_satisfiable(self.cnf_spec()) == mltl_sat_len(self.formula(), complen_mltl(self.formula())),
    {
        if dimacs_satisfiable(cnf_seqs(self.cnf@)) {
            let w = choose|w: spec_fn(nat) -> bool| #[trigger] dimacs_models(w, cnf_seqs(self.cnf@));
            self.model_decodes_w(w);
            let pi = self.decoded_w(w);
            assert(pi.len() >= complen_mltl(self.phi) && semantics_mltl(pi, self.phi));
        }
    }

    /// Check the solver's claim about this encoding's CNF.
    pub fn decide(&self, out: SolverOutput) -> (r: Answer)
        requires
            self.inv(),
        ensures
            match r {
                // A trace of length `complen φ` that satisfies `φ`.
                Answer::Sat(trace) => {
                    &&& trace@.len() == complen_mltl(self.formula())
                    &&& semantics_mltl(trace_view(trace@), self.formula())
                    &&& mltl_sat_len(self.formula(), complen_mltl(self.formula()))
                },
                // No trace of length `complen φ` satisfies `φ`.
                Answer::Unsat => !mltl_sat_len(self.formula(), complen_mltl(self.formula())),
                Answer::Unknown => true,
            },
            // A genuine model of the CNF is never rejected.
            match out {
                SolverOutput::Sat(model) => dimacs_models(model_valuation(model@), self.cnf_spec()) ==> r is Sat,
                _ => true,
            },
    {
        match out {
            SolverOutput::Sat(model) => {
                let trace = self.decode(&model);
                proof {
                    if dimacs_models(model_valuation(model@), cnf_seqs(self.cnf@)) {
                        self.model_decodes(model@);
                    }
                }
                if mltl_eval(&self.phi, trace.as_slice()) {
                    proof {
                        let pi = trace_view(trace@);
                        assert(pi.len() == trace@.len());
                        assert(semantics_mltl(pi, self.phi));
                        assert(mltl_sat_len(self.phi, complen_mltl(self.phi)));
                    }
                    Answer::Sat(trace)
                } else {
                    Answer::Unknown
                }
            },
            SolverOutput::Unsat(steps) => {
                if check_lrat(&self.cnf, &steps) {
                    Answer::Unsat
                } else {
                    Answer::Unknown
                }
            },
            SolverOutput::Unknown => Answer::Unknown,
        }
    }
}

/// Run the SAT solver (CaDiCaL, as a subprocess: `crate::cadical`).
/// Trusted only to be memory safe and to return: its contract promises
/// nothing about the result, and `solve` checks whatever comes back.
#[verifier::external_body]
pub fn run_solver(cnf: &Vec<Vec<i32>>) -> SolverOutput {
    crate::cadical::run_cadical(cnf)
}

/// Nanoseconds since some fixed point (a clock reading). Trusted only to
/// be memory safe and to return; nothing is assumed about the value.
#[verifier::external_body]
pub fn now_ns() -> u64 {
    crate::cadical::clock_ns()
}

/// Time spent in each phase of [`solve`] (benchmark data only).
pub struct Timings {
    pub encode_ns: u64,
    pub solve_ns: u64,
    pub check_ns: u64,
    pub vars: usize,
    pub clauses: usize,
}

/// Largest variable in a CNF.
fn max_var(cnf: &Vec<Vec<i32>>) -> usize {
    let mut m: usize = 0;
    let mut i: usize = 0;
    while i < cnf.len()
        decreases cnf.len() - i,
    {
        let c = &cnf[i];
        let mut j: usize = 0;
        while j < c.len()
            decreases c.len() - j,
        {
            let l = c[j];
            if l != i32::MIN {
                let x: usize = if l < 0 { (-l) as usize } else { l as usize };
                if x > m {
                    m = x;
                }
            }
            j += 1;
        }
        i += 1;
    }
    m
}

/// Decide whether some trace of length `complen f` satisfies `f`, with the
/// time each phase took.
pub fn solve(f: &Mltl<usize>) -> (r: Option<(Answer, Timings)>)
    ensures
        match r {
            // A satisfying trace of `f`, of length `complen f`.
            Some((Answer::Sat(trace), _)) => {
                &&& trace@.len() == complen_mltl(*f)
                &&& semantics_mltl(trace_view(trace@), *f)
            },
            // No trace of length `complen f` satisfies `f`.
            Some((Answer::Unsat, _)) => !mltl_sat_len(*f, complen_mltl(*f)),
            // The solver's output did not check: it was neither a model of
            // the CNF nor an LRAT refutation our checker accepts.
            Some((Answer::Unknown, _)) => true,
            // `f` has an ill-formed interval, or needs more than `i32` variables.
            None => true,
        },
{
    let t0 = now_ns();
    let enc = match encode(f) {
        Some(enc) => enc,
        None => return None,
    };
    let t1 = now_ns();
    let out = run_solver(enc.cnf());
    let t2 = now_ns();
    let answer = enc.decide(out);
    let t3 = now_ns();
    let timings = Timings {
        encode_ns: t1.wrapping_sub(t0),
        solve_ns: t2.wrapping_sub(t1),
        check_ns: t3.wrapping_sub(t2),
        vars: max_var(enc.cnf()),
        clauses: enc.cnf().len(),
    };
    Some((answer, timings))
}

} // verus!
