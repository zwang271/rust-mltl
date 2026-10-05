//! Bit-level facts for the packed fast WEST (`fast.rs`), proved with
//! Verus's `bit_vector` solver. A packed state uses 2 bits per atom: bit
//! 2p = "may be false", bit 2p+1 = "may be true" (11 = S, 10 = One,
//! 01 = Zero, 00 = contradiction).
use vstd::prelude::*;

verus! {

/// Bit `k` of `x` (for `k < 64`).
pub open spec fn bit(x: u64, k: int) -> bool {
    ((x >> (k as u64)) & 1u64) == 1u64
}

/// Pair `p` of `z` (bits 2p, 2p+1) is not `00`.
pub open spec fn pair_ok(z: u64, p: int) -> bool {
    bit(z, 2 * p) || bit(z, 2 * p + 1)
}

/// The even-position mask `0b0101…01`.
pub const LO: u64 = 0x5555_5555_5555_5555u64;

pub proof fn lemma_bit_and(x: u64, y: u64, k: u64)
    requires
        k < 64,
    ensures
        bit(x & y, k as int) == (bit(x, k as int) && bit(y, k as int)),
{
    assert(((x & y) >> k) & 1u64 == 1u64 <==> (((x >> k) & 1u64) == 1u64 && ((y >> k) & 1u64) == 1u64)) by (bit_vector)
        requires k < 64u64;
}

pub proof fn lemma_bit_or(x: u64, y: u64, k: u64)
    requires
        k < 64,
    ensures
        bit(x | y, k as int) == (bit(x, k as int) || bit(y, k as int)),
{
    assert(((x | y) >> k) & 1u64 == 1u64 <==> (((x >> k) & 1u64) == 1u64 || ((y >> k) & 1u64) == 1u64)) by (bit_vector)
        requires k < 64u64;
}

pub proof fn lemma_bit_xor(x: u64, y: u64, k: u64)
    requires
        k < 64,
    ensures
        bit(x ^ y, k as int) == (bit(x, k as int) != bit(y, k as int)),
{
    assert(((x ^ y) >> k) & 1u64 == 1u64 <==> (((x >> k) & 1u64) == 1u64) != (((y >> k) & 1u64) == 1u64)) by (bit_vector)
        requires k < 64u64;
}

pub proof fn lemma_bit_ones(k: u64)
    requires
        k < 64,
    ensures
        bit(!0u64, k as int),
{
    assert(((!0u64) >> k) & 1u64 == 1u64) by (bit_vector)
        requires k < 64u64;
}

/// A word passes the contradiction check exactly when none of its 32 pairs
/// is `00`. (`⟸` lists the 32 pairs, since `bit_vector` has no quantifiers.)
pub proof fn lemma_pairs_ok_word(z: u64)
    ensures
        ((z | (z >> 1u64)) & LO) == LO <==> forall|p: int| 0 <= p < 32 ==> #[trigger] pair_ok(z, p),
{
    if ((z | (z >> 1u64)) & LO) == LO {
        assert forall|p: int| 0 <= p < 32 implies #[trigger] pair_ok(z, p) by {
            let p = p as u64;
            assert(((z >> mul(2u64, p)) & 1u64) == 1u64 || ((z >> add(mul(2u64, p), 1u64)) & 1u64) == 1u64) by (bit_vector)
                requires ((z | (z >> 1u64)) & 0x5555_5555_5555_5555u64) == 0x5555_5555_5555_5555u64, p < 32u64;
        }
    }
    if forall|p: int| 0 <= p < 32 ==> #[trigger] pair_ok(z, p) {
        assert(pair_ok(z, 0));
        assert(pair_ok(z, 1));
        assert(pair_ok(z, 2));
        assert(pair_ok(z, 3));
        assert(pair_ok(z, 4));
        assert(pair_ok(z, 5));
        assert(pair_ok(z, 6));
        assert(pair_ok(z, 7));
        assert(pair_ok(z, 8));
        assert(pair_ok(z, 9));
        assert(pair_ok(z, 10));
        assert(pair_ok(z, 11));
        assert(pair_ok(z, 12));
        assert(pair_ok(z, 13));
        assert(pair_ok(z, 14));
        assert(pair_ok(z, 15));
        assert(pair_ok(z, 16));
        assert(pair_ok(z, 17));
        assert(pair_ok(z, 18));
        assert(pair_ok(z, 19));
        assert(pair_ok(z, 20));
        assert(pair_ok(z, 21));
        assert(pair_ok(z, 22));
        assert(pair_ok(z, 23));
        assert(pair_ok(z, 24));
        assert(pair_ok(z, 25));
        assert(pair_ok(z, 26));
        assert(pair_ok(z, 27));
        assert(pair_ok(z, 28));
        assert(pair_ok(z, 29));
        assert(pair_ok(z, 30));
        assert(pair_ok(z, 31));
        assert(((z | (z >> 1u64)) & 0x5555_5555_5555_5555u64) == 0x5555_5555_5555_5555u64) by (bit_vector)
            requires
            ((z >> 0u64) & 1u64) == 1u64 || ((z >> 1u64) & 1u64) == 1u64,
            ((z >> 2u64) & 1u64) == 1u64 || ((z >> 3u64) & 1u64) == 1u64,
            ((z >> 4u64) & 1u64) == 1u64 || ((z >> 5u64) & 1u64) == 1u64,
            ((z >> 6u64) & 1u64) == 1u64 || ((z >> 7u64) & 1u64) == 1u64,
            ((z >> 8u64) & 1u64) == 1u64 || ((z >> 9u64) & 1u64) == 1u64,
            ((z >> 10u64) & 1u64) == 1u64 || ((z >> 11u64) & 1u64) == 1u64,
            ((z >> 12u64) & 1u64) == 1u64 || ((z >> 13u64) & 1u64) == 1u64,
            ((z >> 14u64) & 1u64) == 1u64 || ((z >> 15u64) & 1u64) == 1u64,
            ((z >> 16u64) & 1u64) == 1u64 || ((z >> 17u64) & 1u64) == 1u64,
            ((z >> 18u64) & 1u64) == 1u64 || ((z >> 19u64) & 1u64) == 1u64,
            ((z >> 20u64) & 1u64) == 1u64 || ((z >> 21u64) & 1u64) == 1u64,
            ((z >> 22u64) & 1u64) == 1u64 || ((z >> 23u64) & 1u64) == 1u64,
            ((z >> 24u64) & 1u64) == 1u64 || ((z >> 25u64) & 1u64) == 1u64,
            ((z >> 26u64) & 1u64) == 1u64 || ((z >> 27u64) & 1u64) == 1u64,
            ((z >> 28u64) & 1u64) == 1u64 || ((z >> 29u64) & 1u64) == 1u64,
            ((z >> 30u64) & 1u64) == 1u64 || ((z >> 31u64) & 1u64) == 1u64,
            ((z >> 32u64) & 1u64) == 1u64 || ((z >> 33u64) & 1u64) == 1u64,
            ((z >> 34u64) & 1u64) == 1u64 || ((z >> 35u64) & 1u64) == 1u64,
            ((z >> 36u64) & 1u64) == 1u64 || ((z >> 37u64) & 1u64) == 1u64,
            ((z >> 38u64) & 1u64) == 1u64 || ((z >> 39u64) & 1u64) == 1u64,
            ((z >> 40u64) & 1u64) == 1u64 || ((z >> 41u64) & 1u64) == 1u64,
            ((z >> 42u64) & 1u64) == 1u64 || ((z >> 43u64) & 1u64) == 1u64,
            ((z >> 44u64) & 1u64) == 1u64 || ((z >> 45u64) & 1u64) == 1u64,
            ((z >> 46u64) & 1u64) == 1u64 || ((z >> 47u64) & 1u64) == 1u64,
            ((z >> 48u64) & 1u64) == 1u64 || ((z >> 49u64) & 1u64) == 1u64,
            ((z >> 50u64) & 1u64) == 1u64 || ((z >> 51u64) & 1u64) == 1u64,
            ((z >> 52u64) & 1u64) == 1u64 || ((z >> 53u64) & 1u64) == 1u64,
            ((z >> 54u64) & 1u64) == 1u64 || ((z >> 55u64) & 1u64) == 1u64,
            ((z >> 56u64) & 1u64) == 1u64 || ((z >> 57u64) & 1u64) == 1u64,
            ((z >> 58u64) & 1u64) == 1u64 || ((z >> 59u64) & 1u64) == 1u64,
            ((z >> 60u64) & 1u64) == 1u64 || ((z >> 61u64) & 1u64) == 1u64,
            ((z >> 62u64) & 1u64) == 1u64 || ((z >> 63u64) & 1u64) == 1u64;
    }
}

/// Bit `2p` of `(d | d >> 1) & LO` says whether pair `p` of `d` is nonzero;
/// odd bits are 0.
pub proof fn lemma_pair_diff(d: u64, p: u64)
    requires
        p < 32,
    ensures
        bit((d | (d >> 1u64)) & LO, 2 * p as int) == (bit(d, 2 * p as int) || bit(d, 2 * p as int + 1)),
        !bit((d | (d >> 1u64)) & LO, 2 * p as int + 1),
{
    assert(((((d | (d >> 1u64)) & 0x5555_5555_5555_5555u64) >> mul(2u64, p)) & 1u64 == 1u64)
        <==> (((d >> mul(2u64, p)) & 1u64) == 1u64 || ((d >> add(mul(2u64, p), 1u64)) & 1u64) == 1u64)) by (bit_vector)
        requires p < 32u64;
    assert(((((d | (d >> 1u64)) & 0x5555_5555_5555_5555u64) >> add(mul(2u64, p), 1u64)) & 1u64) != 1u64) by (bit_vector)
        requires p < 32u64;
}

/// `e & (e - 1) == 0`: at most one bit of `e` is set.
pub proof fn lemma_at_most_one_bit(e: u64, i: u64, j: u64)
    requires
        e & sub(e, 1u64) == 0u64 || e == 0u64,
        i < j < 64,
    ensures
        !(bit(e, i as int) && bit(e, j as int)),
{
    assert(!(((e >> i) & 1u64) == 1u64 && ((e >> j) & 1u64) == 1u64)) by (bit_vector)
        requires (e & sub(e, 1u64)) == 0u64 || e == 0u64, i < j, j < 64u64;
}

/// Shifting a word sequence up by `bs` bits (`0 < bs < 64`): bit `r` of
/// `(hi << bs) | (lo >> (64 - bs))` comes from `hi` at `r - bs`, or from
/// `lo` at `64 - bs + r`.
pub proof fn lemma_shift_carry(hi: u64, lo: u64, bs: u64, r: u64)
    requires
        0 < bs < 64,
        r < 64,
    ensures
        bit((hi << bs) | (lo >> sub(64u64, bs)), r as int)
            == if r >= bs { bit(hi, r - bs) } else { bit(lo, 64 - bs + r) },
{
    if r >= bs {
        assert((((hi << bs) | (lo >> sub(64u64, bs))) >> r) & 1u64 == (hi >> sub(r, bs)) & 1u64) by (bit_vector)
            requires 0u64 < bs, bs < 64u64, r < 64u64, r >= bs;
    } else {
        assert((((hi << bs) | (lo >> sub(64u64, bs))) >> r) & 1u64 == (lo >> add(sub(64u64, bs), r)) & 1u64) by (bit_vector)
            requires 0u64 < bs, bs < 64u64, r < 64u64, r < bs;
    }
}

/// Clearing / setting pair `p` (bits 2p, 2p+1) of an all-ones word.
pub proof fn lemma_set_pair(bits: u64, p: u64, k: u64)
    requires
        bits < 4,
        p < 32,
        k < 64,
    ensures
        bit((!0u64 & !(3u64 << mul(2u64, p))) | (bits << mul(2u64, p)), k as int)
            == if k == 2 * p { bits & 1 == 1 } else if k == 2 * p + 1 { bits & 2 == 2 } else { true },
{
    assert(((((!0u64 & !(3u64 << mul(2u64, p))) | (bits << mul(2u64, p))) >> k) & 1u64 == 1u64)
        == if k == mul(2u64, p) { bits & 1u64 == 1u64 } else if k == add(mul(2u64, p), 1u64) { bits & 2u64 == 2u64 } else { true }) by (bit_vector)
        requires bits < 4u64, p < 32u64, k < 64u64;
}

} // verus!
