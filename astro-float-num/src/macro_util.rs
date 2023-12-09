//! Functons used by macros

use crate::{
    common::util::{count_leading_ones, count_leading_zeroes_skip_first},
    defs::DEFAULT_P,
    BigFloat, Consts, Exponent, RoundingMode, Sign, EXPONENT_BIT_SIZE, INF_NEG, INF_POS,
};

/// Computes error for BigFloat values near 1. This function is for internal use by macro `expr`.
pub fn compute_added_err_near_one(arg: &BigFloat, emin: Exponent) -> usize {
    if arg.is_zero() {
        return 0;
    }

    let n = match arg.exponent() {
        Some(1) => count_leading_zeroes_skip_first(arg.mantissa_digits().unwrap_or(&[])),
        Some(0) => count_leading_ones(arg.mantissa_digits().unwrap_or(&[])),
        _ => 0,
    };

    if n > emin.unsigned_abs() as usize {
        0
    } else {
        n
    }
}

#[derive(Debug)]
pub enum TrigFun {
    Sin,
    Cos,
    Tan,
}

/// Algorithm of error computation.
#[derive(Debug)]
pub enum ErrAlgo<'a> {
    Log(&'a BigFloat, usize, Exponent),
    Log2(&'a BigFloat, &'a BigFloat, Exponent),
    Pow(&'a BigFloat, &'a BigFloat, Exponent),
    Trig(&'a BigFloat, usize, TrigFun, &'a mut Consts, Exponent),
    Asin(&'a BigFloat, Exponent),
    Acos(&'a BigFloat, Exponent),
    Acosh(&'a BigFloat, Exponent),
    Atanh(&'a BigFloat, Exponent),
}

/// Computes the precision increment of an arguments to cover the error for a given algorithm.
#[inline]
pub fn compute_added_err(algo: ErrAlgo<'_>) -> usize {
    match algo {
        ErrAlgo::Log(arg, c, emin) => {
            if arg.inexact() && arg.is_positive() {
                c + compute_added_err_near_one(arg, emin)
            } else {
                0
            }
        }
        ErrAlgo::Log2(base, arg, emin) => {
            if (arg.inexact() || base.inexact()) && arg.is_positive() && base.is_positive() {
                let y = if base.inexact() { compute_added_err_near_one(base, emin) } else { 0 };
                let x = if arg.inexact() { compute_added_err_near_one(arg, emin) } else { 0 };
                5 + x.max(y)
            } else {
                0
            }
        }
        ErrAlgo::Pow(base, arg, emin) => {
            if arg.inexact() || base.inexact() {
                if let Some(earg) = arg.exponent() {
                    let v = if !base.inexact() || earg <= 0 {
                        0
                    } else {
                        let n = compute_added_err_near_one(base, emin);
                        if earg as usize > n + EXPONENT_BIT_SIZE {
                            0
                        } else {
                            n.min(earg as usize)
                        }
                    };
                    5 + v + EXPONENT_BIT_SIZE
                } else {
                    0
                }
            } else {
                0
            }
        }
        ErrAlgo::Trig(arg, p, fun, cc, emin) => {
            if arg.inexact() {
                if let Some(e) = arg.exponent() {
                    let err = if e < 1 {
                        0
                    } else {
                        let err = match fun {
                            TrigFun::Sin => {
                                let pi = cc.pi(p, RoundingMode::None);
                                let mut argrem = arg.rem(&pi);
                                argrem.set_sign(Sign::Pos);
                                if argrem.exponent().unwrap_or(0) > 1 {
                                    argrem = argrem.sub(&pi, p, RoundingMode::None);
                                }
                                if argrem.is_zero() {
                                    if p > emin.unsigned_abs() as usize {
                                        0
                                    } else {
                                        p
                                    }
                                } else {
                                    argrem.exponent().map_or(0, |e| {
                                        if e < 0 && e >= emin {
                                            e.unsigned_abs() as usize
                                        } else {
                                            0
                                        }
                                    })
                                }
                            }
                            TrigFun::Cos => {
                                let mut pi = cc.pi(p, RoundingMode::None);
                                let mut argrem = arg.rem(&pi);
                                if argrem.exponent().unwrap_or(0) == 1 {
                                    argrem.set_sign(Sign::Pos);
                                    pi.set_exponent(1);
                                    argrem = argrem.sub(&pi, p, RoundingMode::None);
                                    if argrem.is_zero() {
                                        if p > emin.unsigned_abs() as usize {
                                            0
                                        } else {
                                            p
                                        }
                                    } else {
                                        argrem.exponent().map_or(0, |e| {
                                            if e < 0 && e >= emin {
                                                e.unsigned_abs() as usize
                                            } else {
                                                0
                                            }
                                        })
                                    }
                                } else {
                                    0
                                }
                            }
                            TrigFun::Tan => {
                                let mut pi = cc.pi(p, RoundingMode::None);
                                pi.set_exponent(1);
                                let mut argrem = arg.rem(&pi);
                                argrem.set_sign(Sign::Pos);
                                if argrem.exponent().unwrap_or(0) > 0 {
                                    argrem = argrem.sub(&pi, p, RoundingMode::None);
                                }
                                if argrem.is_zero() {
                                    if p > emin.unsigned_abs() as usize {
                                        0
                                    } else {
                                        p
                                    }
                                } else {
                                    argrem.exponent().map_or(0, |e| {
                                        if e < emin {
                                            0
                                        } else {
                                            e.unsigned_abs() as usize
                                        }
                                    })
                                }
                            }
                        };

                        err + e.unsigned_abs() as usize
                    };

                    err + 2
                } else {
                    0
                }
            } else {
                0
            }
        }
        ErrAlgo::Asin(arg, emin) => {
            if arg.inexact() && arg.exponent().unwrap_or(1) < 1 {
                let n = compute_added_err_near_one(arg, emin);
                2 + (n + 1) / 2
            } else {
                0
            }
        }
        ErrAlgo::Acos(arg, emin) => {
            if arg.inexact() && arg.exponent().unwrap_or(1) < 1 {
                let n = compute_added_err_near_one(arg, emin);
                2 + if arg.is_positive() { n } else { n / 2 }
            } else {
                0
            }
        }
        ErrAlgo::Acosh(arg, emin) => {
            if arg.inexact() && arg.is_positive() && arg.exponent().unwrap_or(0) >= 1 {
                2 + compute_added_err_near_one(arg, emin)
            } else {
                0
            }
        }
        ErrAlgo::Atanh(arg, emin) => {
            if arg.inexact() && arg.exponent().unwrap_or(1) < 1 {
                2 + compute_added_err_near_one(arg, emin)
            } else {
                0
            }
        }
    }
}

/// Checks if the number's exponent is in the given exponent range.
/// Returns Inf if the exponent of `n` is larger than `emax`.
/// The sign of the infinity is determined by the sign of `n`.
/// Returns 0 if the exponent of `n` is smaller than `emin`.
/// Return `n` itself otherwise.
#[inline]
pub fn check_exponent_range(n: BigFloat, emin: Exponent, emax: Exponent) -> BigFloat {
    if let Some(e) = n.exponent() {
        if e > emax {
            if n.is_positive() {
                INF_POS
            } else {
                INF_NEG
            }
        } else if e < emin {
            BigFloat::new(n.mantissa_max_bit_len().unwrap_or(DEFAULT_P))
        } else {
            n
        }
    } else {
        n
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        ext::ONE, mantissa::Mantissa, num::BigFloatNumber, Consts, Exponent, RoundingMode, Sign,
        Word, EXPONENT_MAX, EXPONENT_MIN, INF_NEG, INF_POS, NAN, WORD_BIT_SIZE, WORD_MAX,
        WORD_SIGNIFICANT_BIT,
    };

    use super::*;

    fn assert(expected: usize, words: &[Word], s: Sign, e: Exponent) {
        let d = BigFloat::from_words(words, s, e);
        assert_eq!(
            compute_added_err_near_one(&d, EXPONENT_MIN),
            expected,
            "Expected error {} for d = {:?}",
            expected,
            d
        );
    }

    #[test]
    fn test_compute_err_near_one() {
        for s in [Sign::Pos, Sign::Neg] {
            // 0
            assert(0, &[0, 0, 0], s, 0);

            // 1 and 0.5
            assert(1, &[0, 0, WORD_SIGNIFICANT_BIT], s, 0);
            assert(WORD_BIT_SIZE * 3, &[0, 0, WORD_SIGNIFICANT_BIT], s, 1);

            // close to 1
            assert(WORD_BIT_SIZE, &[0, 0, WORD_MAX], s, 0);
            assert(WORD_BIT_SIZE, &[0, WORD_MAX, WORD_SIGNIFICANT_BIT], s, 1);

            // exponent is neither 0 nor 1
            assert(0, &[0, 123, WORD_MAX], s, -1);
            assert(0, &[0, 123, WORD_SIGNIFICANT_BIT], s, 2);
        }

        // inf and nan
        assert_eq!(
            compute_added_err_near_one(&INF_POS, EXPONENT_MIN),
            0,
            "Expected error 0 for INF_POS"
        );
        assert_eq!(
            compute_added_err_near_one(&INF_NEG, EXPONENT_MIN),
            0,
            "Expected error 0 for INF_NEG"
        );
        assert_eq!(
            compute_added_err_near_one(&NAN, EXPONENT_MIN),
            0,
            "Expected error 0 for NAN"
        );
    }

    fn gen_pair(m1: Mantissa, mut e: Exponent) -> (BigFloat, BigFloat) {
        let s = if rand::random::<i8>() & 1 == 0 { Sign::Pos } else { Sign::Neg };

        let mut m2 = m1.clone().unwrap();

        let n1 = BigFloatNumber::from_raw_unchecked(m1, s, e, true);

        if m2.add_ulp() {
            assert!(e < EXPONENT_MAX);
            *m2.digits_mut().iter_mut().last().unwrap() = WORD_SIGNIFICANT_BIT;
            e += 1;
        }

        let n2 = BigFloatNumber::from_raw_unchecked(m2, s, e, true);

        (n1.into(), n2.into())
    }

    fn gen_num_pair(p: usize, e: Exponent, near1: i32) -> (BigFloat, BigFloat) {
        let mut m1 = Mantissa::random_normal(p).unwrap();

        if near1 != 0 {
            let mut bits = rand::random::<usize>() % (p - 1) + 1;
            let mut iter = m1.digits_mut().iter_mut().rev();

            while bits >= WORD_BIT_SIZE {
                if near1.is_negative() {
                    *iter.next().unwrap() = WORD_MAX;
                } else {
                    *iter.next().unwrap() = 0;
                }
                bits -= WORD_BIT_SIZE;
            }

            if bits > 0 {
                if near1.is_negative() {
                    *iter.next().unwrap() |= WORD_MAX << (WORD_BIT_SIZE - bits);
                } else {
                    *iter.next().unwrap() &= WORD_MAX >> bits;
                }
            }

            *m1.digits_mut().iter_mut().last().unwrap() |= WORD_SIGNIFICANT_BIT;
        }

        gen_pair(m1, e)
    }

    fn gen_num_pair_trig(
        p: usize,
        e: Exponent,
        near_pi: i32,
        cc: &mut Consts,
        add_half_pi: bool,
    ) -> (BigFloat, BigFloat) {
        let mut m1 = Mantissa::random_normal(p).unwrap();

        if near_pi != 0 {
            let bits = rand::random::<usize>() % (p - 1) + 1;

            let pirm = if near_pi < 0 { RoundingMode::ToZero } else { RoundingMode::FromZero };

            let mut pi = cc.pi(p, pirm);
            pi.set_exponent(0);
            let pi_rounded = pi.round(bits, pirm);
            let pi_digits = pi_rounded.mantissa_digits().unwrap();

            let l = m1.len();
            m1.digits_mut()[l - pi_digits.len() + 1..].copy_from_slice(&pi_digits[1..]);
            let shift = bits % WORD_BIT_SIZE;
            if shift > 0 {
                m1.digits_mut()[l - pi_digits.len()] &= WORD_MAX >> shift;
                m1.digits_mut()[l - pi_digits.len()] |= pi_digits[0];
            }

            if add_half_pi {
                let n = BigFloatNumber::from_raw_unchecked(m1, Sign::Pos, e, true);
                pi.set_exponent(1);
                let n = pi.add(&n.into(), p, RoundingMode::ToZero);
                let w = n.as_raw_parts().unwrap().0;
                m1 = Mantissa::from_words(w.len() * WORD_BIT_SIZE, w).unwrap();
            }
        }

        gen_pair(m1, e)
    }

    fn calc_err(mut d1: BigFloat, mut d2: BigFloat, p: usize) -> usize {
        if d1 == d2 {
            0
        } else {
            if let (Some(e1), Some(e2)) = (d1.exponent(), d2.exponent()) {
                let emax = e1.max(e2);
                d1.set_exponent(e1 - emax);
                d2.set_exponent(e2 - emax);
                let a = d1
                    .sub(&d2, p, RoundingMode::None)
                    .exponent()
                    .unwrap()
                    .unsigned_abs() as usize;
                p.saturating_sub(a)
            } else {
                0
            }
        }
    }

    #[test]
    fn test_compute_added_err() {
        let mut cc = Consts::new().unwrap();
        let emin = EXPONENT_MIN;

        /* let n = BigFloat::from_words(&[16302899892790296137], Sign::Pos, -2);
        let r = n.reciprocal(64, RoundingMode::None);
        println!("{:?}", r);
        return; */

        for _ in 0..10 {
            let ernd = rand::random::<Exponent>() % (EXPONENT_BIT_SIZE as Exponent - 5);

            for e in [0, 1, 2, EXPONENT_BIT_SIZE as Exponent + ernd, 1000 + ernd, 1000000 + ernd] {
                for esign in [1, -1] {
                    let near1set = if e <= 1 { vec![0, -1, 1] } else { vec![0] };

                    for near1 in near1set {
                        let e = e * esign;
                        let p = (rand::random::<usize>() % 10 + 1) * WORD_BIT_SIZE;

                        let (n1, n2) = gen_num_pair(p, e, near1);

                        //println!("n1 {:?}", n1);
                        //println!("n2 {:?}", n2);

                        // reciprocal
                        let d1 = BigFloat::reciprocal(&n1, p, RoundingMode::None);
                        let d2 = BigFloat::reciprocal(&n2, p, RoundingMode::None);
                        let err = calc_err(d1, d2, p);

                        //println!("recip {:?}", err);
                        assert!(err <= 2);

                        // sqrt
                        let d1 = BigFloat::sqrt(&n1, p, RoundingMode::None);
                        let d2 = BigFloat::sqrt(&n2, p, RoundingMode::None);
                        let err = calc_err(d1, d2, p);

                        //println!("sqrt {:?}", err);
                        assert!(err <= 1);

                        // cbrt
                        let d1 = BigFloat::cbrt(&n1, p, RoundingMode::None);
                        let d2 = BigFloat::cbrt(&n2, p, RoundingMode::None);
                        let err = calc_err(d1, d2, p);

                        //println!("cbrt {:?}", err);
                        assert!(err <= 1);

                        // ln
                        let d1 = BigFloat::ln(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::ln(&n2, p, RoundingMode::None, &mut cc);

                        let err_estimate = compute_added_err(ErrAlgo::Log(&n1, 2, emin));
                        let err = calc_err(d1, d2, p);

                        //println!("ln {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // log base 2
                        let d1 = BigFloat::log2(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::log2(&n2, p, RoundingMode::None, &mut cc);

                        let err_estimate = compute_added_err(ErrAlgo::Log(&n1, 3, emin));
                        let err = calc_err(d1, d2, p);

                        //println!("log2 {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // log base 10
                        let d1 = BigFloat::log10(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::log10(&n2, p, RoundingMode::None, &mut cc);

                        let err_estimate = compute_added_err(ErrAlgo::Log(&n1, 6, emin));
                        let err = calc_err(d1, d2, p);

                        //println!("log10 {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // log base b, pow
                        let mut nc = [n1.clone(), n2.clone()];

                        for e2 in [
                            0,
                            1,
                            2,
                            EXPONENT_BIT_SIZE as Exponent + ernd,
                            1000 + ernd,
                            1000000 + ernd,
                        ] {
                            for esign2 in [1, -1] {
                                let near1set2 = if e2 <= 1 { vec![0, -1, 1] } else { vec![0] };

                                for near12 in near1set2 {
                                    let e2 = e2 * esign2;
                                    let (b1, b2) = gen_num_pair(p, e2, near12);
                                    let mut bc = [b1, b2];

                                    for (i1, i2) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
                                        for (j1, j2) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
                                            if i1 == i2 && j1 == j2 {
                                                continue;
                                            }

                                            if i1 == i2 {
                                                nc[0].set_inexact(false);
                                                nc[1].set_inexact(false);
                                            } else {
                                                nc[0].set_inexact(true);
                                                nc[1].set_inexact(true);
                                            }

                                            if j1 == j2 {
                                                bc[0].set_inexact(false);
                                                bc[1].set_inexact(false);
                                            } else {
                                                bc[0].set_inexact(true);
                                                bc[1].set_inexact(true);
                                            }

                                            let n = &nc[i1];
                                            let nn = &nc[i2];

                                            let b = &bc[j1];
                                            let bb = &bc[j2];

                                            let d1 =
                                                BigFloat::log(n, b, p, RoundingMode::None, &mut cc);
                                            let d2 = BigFloat::log(
                                                nn,
                                                bb,
                                                p,
                                                RoundingMode::None,
                                                &mut cc,
                                            );

                                            let err_estimate =
                                                compute_added_err(ErrAlgo::Log2(b, n, emin));
                                            let err = calc_err(d1, d2, p);

                                            let err_estimate = 1.max(err_estimate);

                                            //println!("log {:?} {:?}", err, err_estimate);
                                            assert!(err <= err_estimate);

                                            let d1 =
                                                BigFloat::pow(b, n, p, RoundingMode::None, &mut cc);
                                            let d2 = BigFloat::pow(
                                                bb,
                                                nn,
                                                p,
                                                RoundingMode::None,
                                                &mut cc,
                                            );

                                            let err_estimate =
                                                compute_added_err(ErrAlgo::Pow(b, n, emin));
                                            let err = calc_err(d1, d2, p);

                                            if !(b.abs().cmp(&ONE) == Some(0)
                                                || bb.abs().cmp(&ONE) == Some(0))
                                            {
                                                let err_estimate = 1.max(err_estimate);
                                                //println!("pow {:?} {:?}", err, err_estimate);
                                                assert!(err <= err_estimate);
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        // exp
                        let d1 = BigFloat::exp(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::exp(&n2, p, RoundingMode::None, &mut cc);

                        let err = calc_err(d1, d2, p);

                        //println!("exp {:?}", err);
                        assert!(err <= EXPONENT_BIT_SIZE + 1);

                        // sinh
                        let d1 = BigFloat::sinh(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::sinh(&n2, p, RoundingMode::None, &mut cc);

                        let err = calc_err(d1, d2, p);

                        //println!("sinh {:?}", err);
                        assert!(err <= EXPONENT_BIT_SIZE + 1);

                        // cosh
                        let d1 = BigFloat::cosh(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::cosh(&n2, p, RoundingMode::None, &mut cc);

                        let err = calc_err(d1, d2, p);

                        //println!("cosh {:?}", err);
                        assert!(err <= EXPONENT_BIT_SIZE + 1);

                        // tanh
                        let d1 = BigFloat::tanh(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::tanh(&n2, p, RoundingMode::None, &mut cc);

                        let err = calc_err(d1, d2, p);

                        //println!("tanh {:?}", err);
                        assert!(err <= 2);

                        // asinh
                        let d1 = BigFloat::asinh(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::asinh(&n2, p, RoundingMode::None, &mut cc);

                        let err = calc_err(d1, d2, p);

                        //println!("asinh {:?}", err);
                        assert!(err <= 2);

                        // acosh
                        let d1 = BigFloat::acosh(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::acosh(&n2, p, RoundingMode::None, &mut cc);

                        let err_estimate = compute_added_err(ErrAlgo::Acosh(&n1, emin));
                        let err = calc_err(d1, d2, p);

                        //println!("acosh {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // atanh
                        let d1 = BigFloat::atanh(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::atanh(&n2, p, RoundingMode::None, &mut cc);

                        let err_estimate = compute_added_err(ErrAlgo::Atanh(&n1, emin));
                        let err = calc_err(d1, d2, p);

                        //println!("atanh {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // atan
                        let d1 = BigFloat::atan(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::atan(&n2, p, RoundingMode::None, &mut cc);

                        let err = calc_err(d1, d2, p);

                        //println!("atan {:?}", err);
                        assert!(err <= 2);
                    }
                }
            }

            // sin, cos, tan
            for e in [0, 1, 2, EXPONENT_BIT_SIZE as Exponent + ernd, 1000 + ernd] {
                for esign in [1, -1] {
                    for near_pi in [0, 1, -1] {
                        for add_half_pi in [false, true] {
                            let e = e * esign;
                            let p = (rand::random::<usize>() % 10 + 1) * WORD_BIT_SIZE;

                            let (n1, n2) = gen_num_pair_trig(p, e, near_pi, &mut cc, add_half_pi);

                            // sin
                            let d1 = BigFloat::sin(&n1, p, RoundingMode::None, &mut cc);
                            let d2 = BigFloat::sin(&n2, p, RoundingMode::None, &mut cc);
                            let err_estimate = compute_added_err(ErrAlgo::Trig(
                                &n1,
                                p,
                                TrigFun::Sin,
                                &mut cc,
                                emin,
                            ));
                            let err = calc_err(d1, d2, p);

                            //println!("sin {:?} {:?}", err, err_estimate);
                            assert!(err <= err_estimate);

                            // cos
                            let d1 = BigFloat::cos(&n1, p, RoundingMode::None, &mut cc);
                            let d2 = BigFloat::cos(&n2, p, RoundingMode::None, &mut cc);
                            let err_estimate = compute_added_err(ErrAlgo::Trig(
                                &n1,
                                p,
                                TrigFun::Cos,
                                &mut cc,
                                emin,
                            ));
                            let err = calc_err(d1, d2, p);

                            //println!("cos {:?} {:?}", err, err_estimate);
                            assert!(err <= err_estimate);

                            // tan
                            let d1 = BigFloat::tan(&n1, p, RoundingMode::None, &mut cc);
                            let d2 = BigFloat::tan(&n2, p, RoundingMode::None, &mut cc);

                            let err_estimate = compute_added_err(ErrAlgo::Trig(
                                &n1,
                                p,
                                TrigFun::Tan,
                                &mut cc,
                                emin,
                            ));
                            let err = calc_err(d1, d2, p);

                            //println!("tan {:?} {:?}", err, err_estimate);
                            assert!(err <= err_estimate);
                        }
                    }
                }
            }

            // asin, acos
            for e in [0, -1, -2, -(EXPONENT_BIT_SIZE as Exponent + ernd), -(1000 + ernd)] {
                let near1set = if e == 0 { vec![0, -1] } else { vec![0] };

                for near1 in near1set {
                    let p = (rand::random::<usize>() % 10 + 1) * WORD_BIT_SIZE;

                    let (n1, n2) = gen_num_pair(p, e, near1);

                    // asin
                    let d1 = BigFloat::asin(&n1, p, RoundingMode::None, &mut cc);
                    let d2 = BigFloat::asin(&n2, p, RoundingMode::None, &mut cc);

                    let err_estimate = compute_added_err(ErrAlgo::Asin(&n1, emin));
                    let err = calc_err(d1, d2, p);

                    //println!("asin {:?} {:?}", err, err_estimate);
                    assert!(err <= err_estimate);

                    // acos
                    let d1 = BigFloat::acos(&n1, p, RoundingMode::None, &mut cc);
                    let d2 = BigFloat::acos(&n2, p, RoundingMode::None, &mut cc);

                    let err_estimate = compute_added_err(ErrAlgo::Acos(&n1, emin));
                    let err = calc_err(d1, d2, p);

                    //println!("acos {:?} {:?}", err, err_estimate);
                    assert!(err <= err_estimate);
                }
            }
        }
    }
}
