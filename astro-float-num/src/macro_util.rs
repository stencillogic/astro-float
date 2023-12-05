//! Functons used by macros

use crate::{
    common::util::{count_leading_ones, count_leading_zeroes_skip_first},
    BigFloat, Consts, RoundingMode, Sign, EXPONENT_BIT_SIZE,
};

/// Computes error for BigFloat values near 1. This function is for internal use by macro `expr`.
pub fn compute_added_err_near_one(arg: &BigFloat, _p: usize) -> usize {
    if arg.is_zero() {
        return 0;
    }

    match arg.exponent() {
        Some(1) => count_leading_zeroes_skip_first(arg.mantissa_digits().unwrap_or(&[])),
        Some(0) => count_leading_ones(arg.mantissa_digits().unwrap_or(&[])),
        _ => 0,
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
    Log(&'a BigFloat, usize),
    Log2(&'a BigFloat, &'a BigFloat),
    Pow(&'a BigFloat, &'a BigFloat),
    Trig(&'a BigFloat, usize, TrigFun, &'a mut Consts),
    Asin(&'a BigFloat),
    Acos(&'a BigFloat),
    Acosh(&'a BigFloat),
    Atanh(&'a BigFloat),
}

/// Computes the precision increment of an arguments to cover the error for a given algorithm.
pub fn compute_added_err(algo: ErrAlgo<'_>) -> usize {
    match algo {
        ErrAlgo::Log(arg, c) => c + compute_added_err_near_one(arg, 0),
        ErrAlgo::Log2(base, arg) => {
            let y = compute_added_err_near_one(base, 0);
            let x = compute_added_err_near_one(arg, 0);
            5 + x.max(y)
        },
        ErrAlgo::Pow(base, arg) => {
            if let Some(earg) = arg.exponent() {
                let n = compute_added_err_near_one(base, 0);
                let v = if earg <= 0 || earg as usize > n + EXPONENT_BIT_SIZE {
                    0
                } else {
                    n.min(earg.unsigned_abs() as usize)
                };
                5 + v + EXPONENT_BIT_SIZE
            } else {
                0
            }
        },
        ErrAlgo::Trig(arg, p, fun, cc) => {
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
                                p
                            } else {
                                argrem.exponent().map_or(0, |e| {
                                    if e < 0 {
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
                            argrem.set_sign(Sign::Pos);
                            pi.set_exponent(1);
                            if argrem.exponent().unwrap_or(0) > 0 {
                                argrem = argrem.sub(&pi, p, RoundingMode::None);
                            }
                            if argrem.is_zero() {
                                p
                            } else {
                                argrem.exponent().map_or(0, |e| {
                                    if e < 0 {
                                        e.unsigned_abs() as usize
                                    } else {
                                        0
                                    }
                                })
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
                                p
                            } else {
                                argrem.exponent().map_or(0, |e| e.unsigned_abs() as usize)
                            }
                        }
                    };

                    err + e.unsigned_abs() as usize
                };

                err + 2
            } else {
                0
            }
        },
        ErrAlgo::Asin(arg) => {
            let n = compute_added_err_near_one(arg, 0);
            2 + (n + 1) / 2
        },
        ErrAlgo::Acos(arg) => {
            let n = compute_added_err_near_one(arg, 0);
            2 + if arg.is_positive() {
                n
            } else {
                n / 2
            }
        },
        ErrAlgo::Acosh(arg) => {
            if arg.is_positive() && arg.exponent().unwrap_or(0) >= 1 {
                2 + compute_added_err_near_one(arg, 0)
            } else {
                0
            }
        },
        ErrAlgo::Atanh(arg) => {
            if arg.exponent().unwrap_or(0) < 1 {
                2 + compute_added_err_near_one(arg, 0)
            } else {
                0
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        ext::ONE, mantissa::Mantissa, num::BigFloatNumber, Consts, Exponent, RoundingMode, Sign,
        Word, EXPONENT_MAX, INF_NEG, INF_POS, NAN, WORD_BIT_SIZE, WORD_MAX, WORD_SIGNIFICANT_BIT,
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
    fn test_compute_err_near_one() {
        for s in [Sign::Pos, Sign::Neg] {
            for p in [128, 192, 256] {
                // 0
                assert(0, &[0, 0, 0], s, 0, p);

                // 1 and 0.5
                assert(1, &[0, 0, WORD_SIGNIFICANT_BIT], s, 0, p);
                assert(WORD_BIT_SIZE * 3, &[0, 0, WORD_SIGNIFICANT_BIT], s, 1, p);

                // close to 1
                assert(WORD_BIT_SIZE, &[0, 0, WORD_MAX], s, 0, p);
                assert(WORD_BIT_SIZE, &[0, WORD_MAX, WORD_SIGNIFICANT_BIT], s, 1, p);

                // exponent is neither 0 nor 1
                assert(0, &[0, 123, WORD_MAX], s, -1, p);
                assert(0, &[0, 123, WORD_SIGNIFICANT_BIT], s, 2, p);
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

    fn gen_pair(m1: Mantissa, mut e: Exponent) -> (BigFloat, BigFloat) {
        let s = if rand::random::<i8>() & 1 == 0 { Sign::Pos } else { Sign::Neg };

        let mut m2 = m1.clone().unwrap();

        let n1 = BigFloatNumber::from_raw_unchecked(m1, s, e, false);

        if m2.add_ulp() {
            assert!(e < EXPONENT_MAX);
            *m2.digits_mut().iter_mut().last().unwrap() = WORD_SIGNIFICANT_BIT;
            e += 1;
        }

        let n2 = BigFloatNumber::from_raw_unchecked(m2, s, e, false);

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

            let (mut n1, mut n2) = gen_pair(m1, e);

            if add_half_pi {
                pi.set_exponent(1);
                pi.set_sign(n1.sign().unwrap());

                n1 = n1.add(&pi, p, pirm);
                n2 = n2.add(&pi, p, pirm);
            }

            (n1, n2)
        } else {
            gen_pair(m1, e)
        }
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

        /* let n = BigFloat::from_words(&[16302899892790296137], Sign::Pos, -2);
        let r = n.reciprocal(64, RoundingMode::None);
        println!("{:?}", r);
        return; */

        for _ in 0..10 {
            let ernd = rand::random::<Exponent>() % (EXPONENT_BIT_SIZE as Exponent - 5);

            for e in [0, 1, 2, EXPONENT_BIT_SIZE as Exponent + ernd, 1000 + ernd, 1000000 + ernd] {
                for esign in [1, -1] {
                    let near1set = if e <= 2 { vec![0, -1, 1] } else { vec![0] };

                    for near1 in near1set {
                        let e = e * esign;
                        let p = (rand::random::<usize>() % 10 + 1) * WORD_BIT_SIZE;

                        let (n1, n2) = gen_num_pair(p, e, near1);
                        let (n1_abs, n2_abs) = (n1.abs(), n2.abs());

                        //println!("n1 {:?}", n1);
                        //println!("n2 {:?}", n2);

                        // reciprocal
                        let d1 = BigFloat::reciprocal(&n1, p, RoundingMode::None);
                        let d2 = BigFloat::reciprocal(&n2, p, RoundingMode::None);
                        let err = calc_err(d1, d2, p);

                        //println!("recip {:?}", err);
                        assert!(err <= 2);

                        // sqrt
                        let d1 = BigFloat::sqrt(&n1_abs, p, RoundingMode::None);
                        let d2 = BigFloat::sqrt(&n2_abs, p, RoundingMode::None);
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
                        let d1 = BigFloat::ln(&n1_abs, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::ln(&n2_abs, p, RoundingMode::None, &mut cc);

                        let err_estimate = compute_added_err(ErrAlgo::Log(&n1, 2));
                        let err = calc_err(d1, d2, p);

                        //println!("ln {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // log base 2
                        let d1 = BigFloat::log2(&n1_abs, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::log2(&n2_abs, p, RoundingMode::None, &mut cc);

                        let err_estimate = compute_added_err(ErrAlgo::Log(&n1, 3));
                        let err = calc_err(d1, d2, p);

                        //println!("log2 {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // log base 10
                        let d1 = BigFloat::log10(&n1_abs, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::log10(&n2_abs, p, RoundingMode::None, &mut cc);

                        let err_estimate = compute_added_err(ErrAlgo::Log(&n1, 6));
                        let err = calc_err(d1, d2, p);

                        //println!("log10 {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // log base b, pow
                        for e2 in [0, 1, 2, EXPONENT_BIT_SIZE as Exponent + ernd, 1000 + ernd, 1000000 + ernd] {
                            for esign2 in [1, -1] {
                                let near1set2 = if e2 <= 2 { vec![0, -1, 1] } else { vec![0] };

                                for near12 in near1set2 {
                                    let e2 = e2 * esign2;
                                    let (b1, b2) = gen_num_pair(p, e2, near12);
                                    let (b1_abs, b2_abs) = (b1.abs(), b2.abs());

                                    let d1 = BigFloat::log(
                                        &n1_abs,
                                        &b1_abs,
                                        p,
                                        RoundingMode::None,
                                        &mut cc,
                                    );
                                    let d2 = BigFloat::log(
                                        &n2_abs,
                                        &b2_abs,
                                        p,
                                        RoundingMode::None,
                                        &mut cc,
                                    );

                                    let err_estimate =
                                        compute_added_err(ErrAlgo::Log2(&b1_abs, &n1_abs));
                                    let err = calc_err(d1, d2, p);

                                    //println!("log {:?} {:?}", err, err_estimate);
                                    assert!(err <= err_estimate);

                                    //println!("\nb1 {:?}", b1_abs);
                                    //println!("n1 {:?}", n1_abs);
                                    let d1 = BigFloat::pow(
                                        &b1_abs,
                                        &n1_abs,
                                        p,
                                        RoundingMode::None,
                                        &mut cc,
                                    );
                                    let d2 = BigFloat::pow(
                                        &b2_abs,
                                        &n2_abs,
                                        p,
                                        RoundingMode::None,
                                        &mut cc,
                                    );

                                    let err_estimate =
                                        compute_added_err(ErrAlgo::Pow(&b1_abs, &n1_abs));
                                    let err = calc_err(d1, d2, p);

                                    if !(b1_abs.cmp(&ONE) == Some(0) || b2_abs.cmp(&ONE) == Some(0))
                                    {
                                        assert!(err <= err_estimate);
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

                        let err_estimate =
                        compute_added_err(ErrAlgo::Acosh(&n1));
                        let err = calc_err(d1, d2, p);

                        //println!("acosh {:?} {:?}", err, err_estimate);
                        assert!(err <= err_estimate);

                        // atanh
                        let d1 = BigFloat::atanh(&n1, p, RoundingMode::None, &mut cc);
                        let d2 = BigFloat::atanh(&n2, p, RoundingMode::None, &mut cc);

                        let err_estimate =
                        compute_added_err(ErrAlgo::Atanh(&n1));
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

                            let err_estimate =
                                compute_added_err(ErrAlgo::Trig(&n1, p, TrigFun::Sin, &mut cc));
                            let err = calc_err(d1, d2, p);

                            //println!("sin {:?} {:?}", err, err_estimate);
                            assert!(err <= err_estimate);

                            // cos
                            let d1 = BigFloat::cos(&n1, p, RoundingMode::None, &mut cc);
                            let d2 = BigFloat::cos(&n2, p, RoundingMode::None, &mut cc);

                            let err_estimate =
                                compute_added_err(ErrAlgo::Trig(&n1, p, TrigFun::Cos, &mut cc));
                            let err = calc_err(d1, d2, p);

                            //println!("cos {:?} {:?}", err, err_estimate);
                            assert!(err <= err_estimate);

                            // tan
                            let d1 = BigFloat::tan(&n1, p, RoundingMode::None, &mut cc);
                            let d2 = BigFloat::tan(&n2, p, RoundingMode::None, &mut cc);

                            let err_estimate =
                                compute_added_err(ErrAlgo::Trig(&n1, p, TrigFun::Tan, &mut cc));
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
    
                    let err_estimate =
                        compute_added_err(ErrAlgo::Asin(&n1));
                    let err = calc_err(d1, d2, p);
    
                    //println!("asin {:?} {:?}", err, err_estimate);
                    assert!(err <= err_estimate);

                    // acos
                    let d1 = BigFloat::acos(&n1, p, RoundingMode::None, &mut cc);
                    let d2 = BigFloat::acos(&n2, p, RoundingMode::None, &mut cc);

                    let err_estimate =
                        compute_added_err(ErrAlgo::Acos(&n1));
                    let err = calc_err(d1, d2, p);
    
                    //println!("acos {:?} {:?}", err, err_estimate);
                    assert!(err <= err_estimate);
                }
            }
        }
    }
}
