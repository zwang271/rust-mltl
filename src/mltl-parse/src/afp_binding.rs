//! The "binding examples" of AFP `MLTL_Encoding.thy`, as lemmas about the
//! grammar: the tokens of each text form the grouping Isabelle's notation
//! gives it. (Isabelle writes `And`, `Or`, `Not` for `&`, `|`, `!`.) The
//! lemmas are about tokens, since grouping is decided by the grammar; how
//! text becomes tokens is the lexer's specification.
use vstd::prelude::*;
use mltl_core::mltl::*;
use crate::lexer::*;
use crate::grammar::*;
use crate::printer::*;

verus! {

pub open spec fn p() -> SpecFormula { Mltl::Prop(seq![112u8]) }
pub open spec fn q() -> SpecFormula { Mltl::Prop(seq![113u8]) }
pub open spec fn r() -> SpecFormula { Mltl::Prop(seq![114u8]) }

/// A one-letter lowercase name other than `t`, `f` is a valid name.
proof fn lemma_letter_name(c: u8)
    requires
        97 <= c <= 122, c != 116, c != 102,
    ensures
        valid_name(seq![c]),
{
    let n = seq![c];
    assert(n[0] == c);
    assert(!is_word(n, seq![70u8])) by { assert(n[0] != seq![70u8][0]); }
    assert(!is_word(n, seq![71u8])) by { assert(n[0] != seq![71u8][0]); }
    assert(!is_word(n, seq![85u8])) by { assert(n[0] != seq![85u8][0]); }
    assert(!is_word(n, seq![82u8])) by { assert(n[0] != seq![82u8][0]); }
    assert(!is_word(n, seq![116u8])) by { assert(n[0] != seq![116u8][0]); }
    assert(!is_word(n, seq![102u8])) by { assert(n[0] != seq![102u8][0]); }
}

proof fn lemma_pqr_valid()
    ensures
        valid_name(seq![112u8]),
        valid_name(seq![113u8]),
        valid_name(seq![114u8]),
{
    lemma_letter_name(112);
    lemma_letter_name(113);
    lemma_letter_name(114);
}

pub open spec fn tp() -> SpecToken { Token::Name(seq![112u8]) }
pub open spec fn tq() -> SpecToken { Token::Name(seq![113u8]) }
pub open spec fn tr() -> SpecToken { Token::Name(seq![114u8]) }

/// `Not p And q = And_mltl (Not_mltl p) q`: `!p & q`.
pub proof fn binding_not_and()
    ensures
        ({
            let ts = seq![Token::Not, tp(), Token::And, tq()];
            formula(ts, 0, ts.len() as int, Mltl::And(Box::new(Mltl::Not(Box::new(p()))), Box::new(q())))
        }),
{
    let f = Mltl::And(Box::new(Mltl::Not(Box::new(p()))), Box::new(q()));
    lemma_pqr_valid();
    reveal_with_fuel(valid_names, 4);
    reveal_with_fuel(mltl_core::properties::intervals_welldef, 4);
    reveal_with_fuel(tokens_at, 8);
    reveal_with_fuel(raw_tokens, 8);
    lemma_print_tokens(f);
    assert(print_tokens(f) =~= seq![Token::Not, tp(), Token::And, tq()]);
}

/// `p And q Or r = Or_mltl (And_mltl p q) r`: `p & q | r`.
pub proof fn binding_and_or()
    ensures
        ({
            let ts = seq![tp(), Token::And, tq(), Token::Or, tr()];
            formula(ts, 0, ts.len() as int, Mltl::Or(Box::new(Mltl::And(Box::new(p()), Box::new(q()))), Box::new(r())))
        }),
{
    let f = Mltl::Or(Box::new(Mltl::And(Box::new(p()), Box::new(q()))), Box::new(r()));
    lemma_pqr_valid();
    reveal_with_fuel(valid_names, 4);
    reveal_with_fuel(mltl_core::properties::intervals_welldef, 4);
    reveal_with_fuel(tokens_at, 8);
    reveal_with_fuel(raw_tokens, 8);
    lemma_print_tokens(f);
    assert(print_tokens(f) =~= seq![tp(), Token::And, tq(), Token::Or, tr()]);
}

/// `F[0,1] p And q = And_mltl (Future_mltl 0 1 p) q`: `F[0,1] p & q`.
pub proof fn binding_future_and()
    ensures
        ({
            let ts = seq![Token::KwF, Token::LBrack, Token::Num(0), Token::Comma, Token::Num(1), Token::RBrack,
                tp(), Token::And, tq()];
            formula(ts, 0, ts.len() as int, Mltl::And(Box::new(Mltl::Future(0, 1, Box::new(p()))), Box::new(q())))
        }),
{
    let f = Mltl::And(Box::new(Mltl::Future(0, 1, Box::new(p()))), Box::new(q()));
    lemma_pqr_valid();
    reveal_with_fuel(valid_names, 4);
    reveal_with_fuel(mltl_core::properties::intervals_welldef, 4);
    reveal_with_fuel(tokens_at, 8);
    reveal_with_fuel(raw_tokens, 8);
    lemma_print_tokens(f);
    assert(print_tokens(f) =~= seq![Token::KwF, Token::LBrack, Token::Num(0), Token::Comma, Token::Num(1),
        Token::RBrack, tp(), Token::And, tq()]);
}

/// `p U[0,1] q And r = And_mltl (Until_mltl p 0 1 q) r`: `p U[0,1] q & r`.
pub proof fn binding_until_and()
    ensures
        ({
            let ts = seq![tp(), Token::KwU, Token::LBrack, Token::Num(0), Token::Comma, Token::Num(1), Token::RBrack,
                tq(), Token::And, tr()];
            formula(ts, 0, ts.len() as int,
                Mltl::And(Box::new(Mltl::Until(Box::new(p()), 0, 1, Box::new(q()))), Box::new(r())))
        }),
{
    let f = Mltl::And(Box::new(Mltl::Until(Box::new(p()), 0, 1, Box::new(q()))), Box::new(r()));
    lemma_pqr_valid();
    reveal_with_fuel(valid_names, 4);
    reveal_with_fuel(mltl_core::properties::intervals_welldef, 4);
    reveal_with_fuel(tokens_at, 8);
    reveal_with_fuel(raw_tokens, 8);
    lemma_print_tokens(f);
    assert(print_tokens(f) =~= seq![tp(), Token::KwU, Token::LBrack, Token::Num(0), Token::Comma, Token::Num(1),
        Token::RBrack, tq(), Token::And, tr()]);
}

} // verus!
