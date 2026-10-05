//! The observer record (Isabelle `R2U2_Observer.thy`): per-node temporal
//! bookkeeping used by UNTIL.
use vstd::prelude::*;
use crate::verdict::*;

verus! {

/// `record observer`: temporal bookkeeping of UNTIL nodes.
/// `last_edge` is kept for Isabelle's record but UNTIL does not use it.
pub struct Observer {
    pub lower_bound: nat,
    pub upper_bound: nat,
    pub last_edge: Option<Verdict>,
    pub prev_verdict: Option<Verdict>,
}

/// `initial_observer lb ub` (`undecidedV` is `None`).
pub open spec fn initial_observer(lb: nat, ub: nat) -> Observer {
    Observer { lower_bound: lb, upper_bound: ub, last_edge: None, prev_verdict: None }
}

} // verus!
