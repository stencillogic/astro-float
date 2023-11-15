//! Functons used by macros

use crate::{BigFloat, RoundingMode};

/// Computes error for BigFloat values near 1. This function is for internal use by macro `expr`.
pub fn compute_added_err_near_one(arg: &BigFloat, p: usize) -> usize {
    let d: BigFloat;
    if arg.is_zero() {
        return 0;
    }

    if let Some(arg_sign) = arg.sign() {
        let one = BigFloat::from(arg_sign.to_int());

        if let Some(0) = arg.exponent() {
            d = one.sub(&arg, p, RoundingMode::None);
        } else if let Some(1) = arg.exponent() {
            d = arg.sub(&one, p, RoundingMode::None);
        } else {
            return 0;
        }

        if d.is_zero() && d.inexact() {
            return p;
        } else if let Some(e) = d.exponent() {
            return (-e) as usize;
        }
    }

    return 0;
}

#[cfg(test)]
mod tests {

    use crate::{
        Exponent, Sign, Word, INF_NEG, INF_POS, NAN, WORD_BIT_SIZE, WORD_MAX, WORD_SIGNIFICANT_BIT,
    };

    use super::*;

    fn assert(expected: usize, words: &[Word], s: Sign, e: Exponent, p: usize) {
        let d = BigFloat::from_words(words, s, e);
        assert_eq!(
            compute_added_err_near_one(&d, p),
            expected,
            "Expected error {} for d = {:?}",
            expected,
            d
        );
    }

    #[test]
    fn test_compute_added_err_near_one() {
        for s in [Sign::Pos, Sign::Neg] {
            for p in [128, 192, 256] {
                // 0
                assert(0, &[0, 0, 0], s, 0, p);

                // 1 and 0.5
                for e in [0, 1] {
                    assert(0, &[0, 0, WORD_SIGNIFICANT_BIT], s, e, p);
                }

                // close to 1
                assert(WORD_BIT_SIZE - 1, &[0, 0, WORD_MAX], s, 0, p);
                assert(
                    WORD_BIT_SIZE - 1,
                    &[0, WORD_MAX, WORD_SIGNIFICANT_BIT],
                    s,
                    1,
                    p,
                );

                // exponent is neither 0 nor 1
                assert(0, &[0, 123, WORD_MAX], s, -1, p);
                assert(0, &[0, 123, WORD_SIGNIFICANT_BIT], s, 2, p);

                let mut d = BigFloat::from_words(&[WORD_SIGNIFICANT_BIT], s, 1);
                d.set_inexact(true);
                assert_eq!(
                    compute_added_err_near_one(&d, p),
                    p,
                    "Expected error {} for d = {:?}",
                    p,
                    d
                );
            }
        }

        // inf and nan
        assert_eq!(
            compute_added_err_near_one(&INF_POS, 128),
            0,
            "Expected error 0 for INF_POS"
        );
        assert_eq!(
            compute_added_err_near_one(&INF_NEG, 128),
            0,
            "Expected error 0 for INF_NEG"
        );
        assert_eq!(
            compute_added_err_near_one(&NAN, 128),
            0,
            "Expected error 0 for NAN"
        );
    }
}
