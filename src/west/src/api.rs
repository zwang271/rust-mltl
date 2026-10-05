//! Entry points for tools: a checked `fast_reg`, and reading the packed
//! result back as WEST bits or as WEST's text format (`s1,0s`: one
//! character per atom, `s` = either, states separated by commas).
use vstd::prelude::*;
use mltl_core::mltl::*;
use mltl_core::properties::*;
use crate::algorithms::*;
use crate::bits::*;
use crate::matching::*;
use crate::packed::*;
use crate::exec::*;
use crate::fast::*;
use crate::fast_reg::*;

verus! {

/// `WEST_num_vars f`, or `None` if it exceeds `usize::MAX`.
pub fn num_vars_checked(f: &Mltl<usize>) -> (r: Option<usize>)
    ensures
        match r {
            Some(x) => x == WEST_num_vars_spec(*f),
            None => WEST_num_vars_spec(*f) > usize::MAX,
        },
    decreases f,
{
    match f {
        Mltl::True | Mltl::False => Some(1),
        Mltl::Prop(p) => if *p == usize::MAX { None } else { Some(*p + 1) },
        Mltl::Not(g) | Mltl::Future(_, _, g) | Mltl::Global(_, _, g) => num_vars_checked(g),
        Mltl::And(g, h) | Mltl::Or(g, h) | Mltl::Until(g, _, _, h) | Mltl::Release(g, _, _, h) => {
            let x = num_vars_checked(g)?;
            let y = num_vars_checked(h)?;
            Some(if x >= y { x } else { y })
        },
    }
}

/// `fast_reg f` when the sizes fit in machine words (`None` otherwise, and
/// only then).
pub fn fast_reg_checked(f: &Mltl<usize>) -> (r: Option<Packed>)
    ensures
        r is None <==> !(WEST_num_vars_spec(*f) <= usize::MAX && fits(WEST_num_vars_spec(*f), bound_sum(*f) + 1)),
        r matches Some(out) ==> pwf(out)
            && out.n == WEST_num_vars_spec(*f)
            && out.len == complen_mltl(*f)
            && (intervals_welldef(*f) ==> forall|pi: WestTrace| pi.len() >= complen_mltl(*f) ==>
                (#[trigger] west_match(pi, pview(out)) <==> semantics_mltl(pi, *f))),
{
    let n = match num_vars_checked(f) {
        Some(n) => n,
        None => return None,
    };
    let bs = match bound_sum_checked(f) {
        Some(b) => b,
        None => {
            proof {
                WEST_num_vars_pos(*f);
                let b = bound_sum(*f);
                assert(!(2 * n * (b + 1) + 64 <= usize::MAX)) by (nonlinear_arith)
                    requires b > usize::MAX, n >= 1;
            }
            return None;
        },
    };
    if bs == usize::MAX {
        proof {
            WEST_num_vars_pos(*f);
            let b = bound_sum(*f);
            assert(!(2 * n * (b + 1) + 64 <= usize::MAX)) by (nonlinear_arith)
                requires b == usize::MAX, n >= 1;
        }
        return None;
    }
    let b1 = bs + 1;
    let q = (usize::MAX - 64) / 2 / b1;
    if n > q {
        proof {
            let m = (usize::MAX - 64) as int;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, 2);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m / 2, b1 as int);
            vstd::arithmetic::div_mod::lemma_mod_bound(m / 2, b1 as int);
            vstd::arithmetic::div_mod::lemma_mod_bound(m, 2);
            assert(n * b1 > m / 2) by (nonlinear_arith)
                requires n > q, q == (m / 2) / (b1 as int), m / 2 == (b1 as int) * ((m / 2) / (b1 as int)) + (m / 2) % (b1 as int),
                    (m / 2) % (b1 as int) < b1, b1 >= 1;
            assert(!(2 * n * b1 + 64 <= usize::MAX)) by (nonlinear_arith)
                requires n * b1 > m / 2, m == 2 * (m / 2) + m % 2, m % 2 < 2, m == usize::MAX - 64;
        }
        return None;
    }
    proof {
        let m = (usize::MAX - 64) as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m, 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(m / 2, b1 as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(m / 2, b1 as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(m, 2);
        assert(n * b1 <= m / 2) by (nonlinear_arith)
            requires n <= q, q == (m / 2) / (b1 as int), m / 2 == (b1 as int) * ((m / 2) / (b1 as int)) + (m / 2) % (b1 as int),
                (m / 2) % (b1 as int) >= 0, b1 >= 1;
        assert(2 * n * b1 + 64 <= usize::MAX) by (nonlinear_arith)
            requires n * b1 <= m / 2, m == 2 * (m / 2) + m % 2, m % 2 >= 0, m == usize::MAX - 64;
    }
    Some(fast_reg(f))
}

// ---------------------------------------------------------------------------
// Reading results
// ---------------------------------------------------------------------------

/// Trace regex `i` as WEST bits.
pub fn decode_trace(r: &Packed, i: usize) -> (out: Vec<Vec<WestBit>>)
    requires
        pwf(*r),
        i < r.traces.len(),
    ensures
        out@.map_values(|s: Vec<WestBit>| s@) == pview(*r)[i as int],
{
    let ghost x = r.traces@[i as int]@;
    let xs = &r.traces[i];
    let n = r.n;
    let ghost target = tr(x, n as nat, r.len as nat);
    assert(twf(x, n as nat, r.len as nat));
    proof { lemma_words_for(n as nat, r.len as nat); }
    let mut out: Vec<Vec<WestBit>> = Vec::with_capacity(r.len);
    let mut t: usize = 0;
    while t < r.len
        invariant
            pwf(*r),
            i < r.traces.len(),
            x == r.traces@[i as int]@,
            xs@ == x,
            n == r.n,
            target == tr(x, n as nat, r.len as nat),
            t <= r.len,
            out@.map_values(|s: Vec<WestBit>| s@) == target.subrange(0, t as int),
        decreases r.len - t,
    {
        let mut st: Vec<WestBit> = Vec::with_capacity(n);
        let mut v: usize = 0;
        while v < n
            invariant
                pwf(*r),
                i < r.traces.len(),
                x == r.traces@[i as int]@,
                xs@ == x,
                n == r.n,
                target == tr(x, n as nat, r.len as nat),
                t < r.len,
                v <= n,
                st@ == target[t as int].subrange(0, v as int),
            decreases n - v,
        {
            proof {
                lemma_grid_bound(n as nat, r.len as nat, t as int, v as int);
                assert(n * r.len <= 2 * n * r.len) by (nonlinear_arith);
            }
            let p = n * t + v;
            proof {
                lemma_pair_pos(p as int);
                vstd::arithmetic::div_mod::lemma_mod_bound(p as int, 32);
                vstd::arithmetic::div_mod::lemma_div_pos_is_pos(p as int, 32);
                assert(p as int / 32 < x.len()) by {
                    assert(p < 32 * x.len()) by (nonlinear_arith)
                        requires p < n * r.len, 2 * n * r.len <= 64 * x.len();
                    crate::packed_ops::div_lt(p as int, 32, x.len() as int);
                }
            }
            let word = xs[p / 32];
            let o: u64 = (p % 32) as u64;
            let lo = (word >> (2 * o)) & 1u64 == 1u64;
            let hi = (word >> (2 * o + 1)) & 1u64 == 1u64;
            let b = if lo && hi { WestBit::S } else if hi { WestBit::One } else { WestBit::Zero };
            proof {
                assert(lo == gb(x, 2 * p));
                assert(hi == gb(x, 2 * p + 1));
                assert(b == pentry(x, p as int));
                lemma_tr_entry(x, n as nat, r.len as nat, t as int, v as int);
            }
            st.push(b);
            v += 1;
            assert(st@ =~= target[t as int].subrange(0, v as int));
        }
        let ghost sv = st@;
        let ghost before = out@.map_values(|s: Vec<WestBit>| s@);
        out.push(st);
        proof {
            assert(sv =~= target[t as int]);
            assert(out@.map_values(|s: Vec<WestBit>| s@) =~= before.push(sv));
        }
        t += 1;
        assert(out@.map_values(|s: Vec<WestBit>| s@) =~= target.subrange(0, t as int));
    }
    assert(target.subrange(0, r.len as int) =~= target);
    assert(pview(*r)[i as int] == target);
    out
}

/// WEST's character for a bit.
pub open spec fn bit_char(b: WestBit) -> u8 {
    match b {
        WestBit::S => 's' as u8,
        WestBit::One => '1' as u8,
        WestBit::Zero => '0' as u8,
    }
}

/// A trace regex in WEST's text format, e.g. `s1,0s`.
pub open spec fn trace_text(t: TraceRegex) -> Seq<u8>
    decreases t.len(),
{
    if t.len() == 0 {
        Seq::empty()
    } else if t.len() == 1 {
        t[0].map_values(|b: WestBit| bit_char(b))
    } else {
        trace_text(t.drop_last()) + seq![',' as u8] + t.last().map_values(|b: WestBit| bit_char(b))
    }
}

/// Trace regex `i` in WEST's text format.
pub fn trace_to_text(r: &Packed, i: usize) -> (out: Vec<u8>)
    requires
        pwf(*r),
        i < r.traces.len(),
    ensures
        out@ == trace_text(pview(*r)[i as int]),
{
    let states = decode_trace(r, i);
    let ghost tv = states@.map_values(|s: Vec<WestBit>| s@);
    let mut out: Vec<u8> = Vec::new();
    let mut t: usize = 0;
    while t < states.len()
        invariant
            t <= states.len(),
            tv == states@.map_values(|s: Vec<WestBit>| s@),
            out@ == trace_text(tv.subrange(0, t as int)),
        decreases states.len() - t,
    {
        let ghost before = out@;
        if t > 0 {
            out.push(',' as u8);
        }
        let mut v: usize = 0;
        let ghost mid = out@;
        while v < states[t].len()
            invariant
                t < states.len(),
                v <= states@[t as int]@.len(),
                out@ == mid + states@[t as int]@.subrange(0, v as int).map_values(|b: WestBit| bit_char(b)),
            decreases states@[t as int]@.len() - v,
        {
            let c: u8 = match states[t][v] {
                WestBit::S => 's' as u8,
                WestBit::One => '1' as u8,
                WestBit::Zero => '0' as u8,
            };
            out.push(c);
            v += 1;
            assert(out@ =~= mid + states@[t as int]@.subrange(0, v as int).map_values(|b: WestBit| bit_char(b)));
        }
        proof {
            let pre = tv.subrange(0, t as int);
            let post = tv.subrange(0, t + 1);
            assert(states@[t as int]@.subrange(0, v as int) =~= states@[t as int]@);
            assert(post.drop_last() =~= pre);
            assert(post.last() == tv[t as int]);
            assert(tv[t as int] == states@[t as int]@);
            if t == 0 {
                assert(post.len() == 1);
                assert(out@ =~= trace_text(post));
            } else {
                assert(out@ =~= trace_text(post));
            }
        }
        t += 1;
    }
    assert(tv.subrange(0, states.len() as int) =~= tv);
    out
}

} // verus!
