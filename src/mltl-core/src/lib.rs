//! MLTL syntax and semantics, ported from AFP `Mission_Time_LTL`.
use vstd::prelude::*;

verus! {

/// Placeholder until T2.2: checks the verification pipeline end to end.
proof fn toolchain_smoke(n: nat)
    ensures n + n == 2 * n,
{
}

} // verus!
