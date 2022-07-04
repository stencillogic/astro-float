//! Multiple precision floating point numbers implemented purely in Rust. 
//! Number has fixed-size mantissa and exponent, but increased precision compared to f32 or f64 values.
//!
//! Number characteristics:
//!
//! | Name                          | Value  |
//! |:------------------------------|-------:|
//! | Decimal positions in mantissa |     40 |
//! | Exponent minimum value        |   -128 |
//! | Exponent maximum value        |    127 |
//! 
//! ## Examples
//! 
//! ```
//! use num_bigfloat::BigFloat;
//! use num_bigfloat::ONE;
//! use num_bigfloat::PI;
//! 
//! // compute pi: pi = 6*arctan(1/sqrt(3))
//! let six: BigFloat = 6.0.into(); // note: conversion from f64,f32 are not loss-less.
//! let three: BigFloat = BigFloat::parse("3.0").unwrap();
//! let pi = six * (ONE / three.sqrt()).atan();
//! let epsilon = 1.0e-38.into();
//! 
//! assert!((pi - PI).abs() < epsilon);
//! 
//! println!("{}", pi);
//! // output: 3.141592653589793238462643383279502884196e-39
//! ```
//! 
//! ## Performance
//! 
//! The fixed-size mantissa allowed the introduction of precomputed tables to speed up most calculations.
//! With regard to anything else, the implementation is straightforward.
//! 
//! ## no_std
//!
//! Library can be used without the standard Rust library. This can be achieved by turning off `std` feature.

#![deny(clippy::suspicious)]

mod defs;
mod inc;
mod ops;
mod ext;

#[cfg(feature = "std")]
mod parser;

pub use crate::ext::BigFloat;
pub use crate::ext::MAX;
pub use crate::ext::MAX_EXP;
pub use crate::ext::MIN;
pub use crate::ext::MIN_EXP;
pub use crate::ext::MIN_POSITIVE;
pub use crate::ext::RADIX;
pub use crate::ext::NAN;
pub use crate::ext::INF_POS;
pub use crate::ext::INF_NEG;
pub use crate::ext::ZERO;
pub use crate::ext::ONE;
pub use crate::ext::TWO;
pub use crate::ext::E;
pub use crate::ext::PI;
pub use crate::ext::HALF_PI;


#[cfg(test)]
mod tests {

    use rand::random;
    use crate::{
        BigFloat,
        INF_POS, 
        INF_NEG, 
        MIN_POSITIVE,
        ONE,
        TWO,
        MIN,
        MAX, 
        PI, 
        HALF_PI, 
        ZERO,
    };
    use crate::defs::{
        DECIMAL_SIGN_POS, 
        DECIMAL_MIN_EXPONENT, 
        DECIMAL_MAX_EXPONENT, 
        DECIMAL_POSITIONS, DECIMAL_BASE, DECIMAL_PARTS, DECIMAL_SIGN_NEG,
    };


    #[test]
    fn test_bigfloat() {

        let mut d1;
        let mut d2;
        let mut d3;
        let mut ref_num;

        // creation & deconstruction

        // regular buf
        let bytes1: [u8; 20] = [1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20];
        let expected1: [u8; 30] = [1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,0,0,0,0,0,0,0,0,0,0];
        let exp1 = 123;
        let d4 = BigFloat::from_bytes(&bytes1, 1, exp1);

        let mut mantissa_buf1 = [0; 30];
        d4.get_mantissa_bytes(&mut mantissa_buf1);
        assert!(mantissa_buf1 == expected1);
        assert!(d4.get_mantissa_len() == bytes1.len());
        assert!(d4.get_sign() == 1);
        assert!(d4.get_exponent() == exp1);

        // too long buf
        let bytes2: [u8; 45] = [1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20,1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20,21,22,3,4,5];
        let expected2: [u8; 42] = [1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,0,0];
        let exp2 = -128;
        let d4 = BigFloat::from_bytes(&bytes2, -2, exp2);

        let mut mantissa_buf2 = [0; 42];
        d4.get_mantissa_bytes(&mut mantissa_buf2);
        assert!(mantissa_buf2 == expected2);
        assert!(d4.get_mantissa_len() == 40);
        assert!(d4.get_sign() == -1);
        assert!(d4.get_exponent() == exp2);

        // conversions

        // inf
        assert!(BigFloat::from_f64(f64::INFINITY).cmp(&INF_POS) == Some(0));
        assert!(BigFloat::from_f64(f64::NEG_INFINITY).cmp(&INF_NEG) == Some(0));

        // nan
        assert!(BigFloat::from_f64(f64::NAN).is_nan());

        // 0.0
        assert!(BigFloat::from_f64(0.0).to_f64() == 0.0);
        

        // conversions
        for _ in 0..10000 {
            let f: f64 = random_f64_exp(50, 25);
            if f.is_finite() && f != 0.0 {
                d1 = BigFloat::from_f64(f);
                assert!((d1.to_f64() / f - 1.0).abs() < 100.0*f64::EPSILON);
                if (f as f32).is_finite() && (f as f32) != 0.0 {
                    d1 = BigFloat::from_f32(f as f32);
                    assert!((d1.to_f32() / f as f32 - 1.0).abs() < 100.0*f32::EPSILON);
                }
            }
        }

        // 0 * 0
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        d3 = d1.mul(&d2);
        assert!(d3.cmp(&ref_num) == Some(0));

        // 0.99 * 0
        d1 = BigFloat::from_f64(0.99);
        d3 = d1.mul(&d2);
        assert!(d3.cmp(&ref_num) == Some(0));

        // 0 * 12349999
        d1 = BigFloat::new();
        d2 = BigFloat::from_f64(12349999.0);
        d3 = d1.mul(&d2);
        assert!(d3.cmp(&ref_num) == Some(0));

        // 1 * 1
        d1 = BigFloat::from_f64(1.0);
        d2 = BigFloat::from_f64(1.0);
        d3 = d1.mul(&d2);
        assert!(d3.cmp(&d1) == Some(0));

        // 1 * -1
        d1 = BigFloat::from_f64(1.0);
        d2 = BigFloat::from_f64(1.0).inv_sign();
        d3 = d1.mul(&d2);
        assert!(d3.cmp(&d2) == Some(0));

        // -1 * 1
        d3 = d2.mul(&d1);
        assert!(d3.cmp(&d2) == Some(0));

        // -1 * -1
        d1 = d1.inv_sign();
        d3 = d1.mul(&d2);
        ref_num = BigFloat::from_f64(1.0);
        assert!(d3.cmp(&ref_num) == Some(0));

        // 0 / 0 
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        assert!(d1.div(&d2).is_nan());

        // d2 / 0
        d2 = BigFloat::from_f64(123.0);
        assert!(d2.div(&d1).is_inf_pos());

        // 0 / d2
        d3 = d1.div(&d2);
        ref_num = BigFloat::new();
        assert!(d3.cmp(&ref_num) == Some(0));

        // 0 / -d2
        d2 = d2.inv_sign();
        d3 = d1.div(&d2);
        assert!(d3.cmp(&ref_num) == Some(0));


        // add & sub & cmp
        for _ in 0..10000 {
            // avoid subnormal numbers
            d1 = random_normal_float(4, 30);
            d2 = random_normal_float(4, 34);
            let n1 = d1.add(&d2);
            if n1.sub(&d1).get_mantissa_len() > 5 {
                let n2 = n1.sub(&d2);
                assert!(n2.sub(&d1).get_mantissa_len() < 4);
            }
        }

        // mul & div
        for _ in 0..10000 {
            // avoid subnormal numbers
            d1 = random_normal_float(40, 40);
            d2 = random_normal_float(40, 40);
            if d2.cmp(&ZERO).unwrap() != 0 {
                let n1 = d1.div(&d2);
                let n2 = n1.mul(&d2);
                assert!(n2.sub(&d1).abs().get_mantissa_len() <= 4);
            }
        }


        // subnormal numbers
        d1 = MIN_POSITIVE;
        d2 = MIN_POSITIVE;
        ref_num = MIN_POSITIVE.mul(&TWO);

        // min_positive + min_positive = 2*min_positive
        assert!(d1.add(&d2).cmp(&ref_num) == Some(0));
        assert!(d1.add(&d2).cmp(&d1).unwrap() > 0);
        assert!(d1.cmp(&d1.add(&d2)).unwrap() < 0);

        // min_positive - min_positive = 0
        ref_num = BigFloat::new();
        assert!(d1.sub(&d2).cmp(&ref_num) == Some(0));

        // 1 * min_positive = min_positive
        assert!(ONE.mul(&d2).cmp(&d2) == Some(0));

        // min_positive / 1 = min_positive
        assert!(d2.div(&ONE).cmp(&d2) == Some(0));

        // min_positive / 1 = min_positive
        assert!(d2.div(&ONE).cmp(&d2) == Some(0));

        // normal -> subnormal -> normal
        d1 = ONE;
        d1.set_exponent(DECIMAL_MIN_EXPONENT);
        d2 = MIN_POSITIVE;
        assert!(!d1.is_subnormal());
        assert!(d1.sub(&d2).cmp(&d1).unwrap() < 0);
        assert!(d1.cmp(&d1.sub(&d2)).unwrap() > 0);
        d1 = d1.sub(&d2);
        assert!(d1.is_subnormal());
        d1 = d1.add(&d2);
        assert!(!d1.is_subnormal());

        // overflow
        d1 = ONE;
        d1.set_exponent(DECIMAL_MAX_EXPONENT - (DECIMAL_POSITIONS as i8 - 1));
        assert!(MAX.add(&d1).is_inf_pos());
        assert!(MIN.sub(&d1).is_inf_neg());
        assert!(MAX.mul(&MAX).is_inf_pos());
        d1 = ONE;
        d1.set_exponent(DECIMAL_MIN_EXPONENT);
        assert!(MAX.div(&d1).is_inf_pos());

        // fract & int
        let f1 = 12345.6789;
        d1 = BigFloat::from_f64(f1);
        assert!((d1.frac().to_f64() - f1.fract()).abs() < 100000.0*f64::EPSILON);
        assert!((d1.int().to_f64() - (f1 as u64) as f64).abs() < 100000.0*f64::EPSILON);

        let f1 = -0.006789;
        d1 = BigFloat::from_f64(f1);
        assert!(d1.frac().cmp(&d1) == Some(0));
        assert!(d1.int().is_zero());

        d1 = BigFloat::from_bytes(&[2,2,2,2,2,0,0,0], DECIMAL_SIGN_POS, -2);
        assert!(d1.frac().is_zero());
        assert!(d1.int().cmp(&d1) == Some(0));

        assert!(MIN_POSITIVE.frac().cmp(&MIN_POSITIVE) == Some(0));
        assert!(MIN_POSITIVE.int().is_zero());

        d1 = BigFloat::new();
        assert!(d1.frac().is_zero());
        assert!(d1.int().is_zero());

        // ceil & floor
        d1 = BigFloat::from_f64(12.3);
        assert!(d1.floor().to_f64() == 12.0);
        assert!(d1.ceil().to_f64() == 13.0);
        d1 = BigFloat::from_f64(12.0);
        assert!(d1.floor().to_f64() == 12.0);
        assert!(d1.ceil().to_f64() == 12.0);

        d1 = BigFloat::from_f64(-12.3);
        assert!(d1.floor().to_f64() == -13.0);
        assert!(d1.ceil().to_f64() == -12.0);
        d1 = BigFloat::from_f64(-12.0);
        assert!(d1.floor().to_f64() == -12.0);
        assert!(d1.ceil().to_f64() == -12.0);

        // abs
        d1 = BigFloat::from_f64(12.3);
        assert!(d1.abs().to_f64() == 12.3);
        d1 = BigFloat::from_f64(-12.3);
        assert!(d1.abs().to_f64() == 12.3);

        // sqrt
        for _ in 0..10000 {
            let num = random_normal_float(256, 128).abs();
            let sq = num.sqrt();
            let ret = sq.mul(&sq);
            assert!(num.sub(&ret).abs().get_mantissa_len() < 2);
        }

        // sqrt of max
        let n = MAX.sqrt();
        assert!(n.cmp(&ZERO).unwrap() > 0 && MAX.cmp(&n).unwrap() > 0);
        let n = n.mul(&n);
        assert!(n.is_inf_pos() || MAX.sub(&n).get_mantissa_len() < 2);

        // sqrt of min positive
        let n = MIN_POSITIVE.sqrt();
        assert!(n.cmp(&ZERO).unwrap() > 0 && MIN_POSITIVE.cmp(&n).unwrap() < 0);
        let n = n.mul(&n);
        assert!(n.is_zero() || MIN_POSITIVE.sub(&n).get_mantissa_len() < 2);


        // pow
        for _ in 0..10000 {
            let a = random_normal_float(4, 40);
            let n = random_normal_float(4, 40);
            let inv = ONE.div(&n);
            let p = a.pow(&n);
            if  !p.is_inf() && p.get_mantissa_len() >= DECIMAL_POSITIONS - 1 {
                let ret = p.pow(&inv);
                assert!(a.sub(&ret).abs().get_mantissa_len() < 3);
            }
        }

        // ln
        for _ in 0..10000 {
            let num = random_normal_float(256, 127).abs();
            if num.is_zero() {
                assert!(num.ln().is_nan());
            } else {
                let l = num.ln();
                let e = l.exp();
                assert!(num.sub(&e).abs().get_mantissa_len() < 5);
            }
        }

        // crossing x axis at x = 1
        let n = ONE.ln();
        assert!(n.is_zero() || ZERO.sub(&n).get_mantissa_len() < 2);

        // ln of max
        let n = MAX.ln();
        assert!(n.cmp(&ZERO).unwrap() > 0 && MAX.cmp(&n).unwrap() > 0);
        let n = n.exp();
        assert!(n.is_inf_pos() || MAX.sub(&n).get_mantissa_len() < 2);

        // ln of min positive
        let n = MIN_POSITIVE.ln();
        assert!(n.cmp(&ZERO).unwrap() < 0 && MIN_POSITIVE.cmp(&n.abs()).unwrap() < 0);
        let n = n.exp();
        assert!(n.is_inf_neg() || MIN_POSITIVE.sub(&n).get_mantissa_len() < 2);


        // sin, asin
        for _ in 0..10000 {
            let num = random_normal_float(90, 127);
            let s = num.sin();
            let a = s.asin();
            if num.abs().cmp(&HALF_PI).unwrap() <= 0 {
                assert!(num.sub(&a).get_mantissa_len() < 4);
            } else {
                let mut sub1 = num.add(&a).abs().div(&PI).frac();
                let mut sub2 = num.sub(&a).abs().div(&PI).frac();
                if sub1.get_mantissa_len() > 2 {
                    sub1 = ONE.sub(&sub1);
                }
                if sub2.get_mantissa_len() > 2 {
                    sub2 = ONE.sub(&sub2);
                }
                assert!(sub1.get_mantissa_len() <= 2 || sub2.get_mantissa_len() < 4);
            }
        }

        // x axis crossing points: 0, PI, 2*PI
        let n = ZERO.sin();
        assert!(n.is_zero() || ZERO.sub(&n).get_mantissa_len() < 2);

        let n = PI.sin();
        assert!(n.is_zero() || ZERO.sub(&n).get_exponent() < -(DECIMAL_POSITIONS as i8) - 38);

        let n = PI.add(&PI).sin();
        assert!(n.is_zero() || ZERO.sub(&n).get_exponent() < -(DECIMAL_POSITIONS as i8) - 38);

        // sin near 0
        let n = MIN_POSITIVE.sin();
        assert!(MIN_POSITIVE.sub(&n).get_mantissa_len() < 2);
        let n = MIN_POSITIVE.inv_sign().sin();
        assert!(MIN_POSITIVE.inv_sign().sub(&n).get_mantissa_len() < 2);

        // sin extremums PI/2, 3*PI/2
        let eps = BigFloat::parse("1.0e-39").unwrap();
        let exp_err = -(DECIMAL_POSITIONS as i8) - 38;
        test_extremum(BigFloat::sin, &HALF_PI, &ONE, 3, 2, 2, &eps, exp_err);
        test_extremum(BigFloat::sin, &HALF_PI.add(&PI), &ONE.inv_sign(), 3, 2, 2, &eps, exp_err);

        // asin extremums: 1, -1
        test_extremum(BigFloat::asin, &ONE, &HALF_PI, 2, 2, 22, &eps, exp_err);
        test_extremum(BigFloat::asin, &ONE.inv_sign(), &HALF_PI.inv_sign(), 1, 2, 22, &eps, exp_err);

        // asin near 0
        let n = MIN_POSITIVE.asin();
        assert!(MIN_POSITIVE.sub(&n).get_mantissa_len() < 2);
        let n = MIN_POSITIVE.inv_sign().asin();
        assert!(MIN_POSITIVE.inv_sign().sub(&n).get_mantissa_len() < 2);

        // cos, acos
        for _ in 0..10000 {
            let num = random_normal_float(3, 40);
            let c = num.cos();
            let a = c.acos();
            if num.abs().cmp(&PI).unwrap() <= 0 {
                assert!(num.abs().sub(&a).get_mantissa_len() < 5);
            } else {
                let mut sub1 = num.add(&a).abs().div(&PI).frac();
                let mut sub2 = num.sub(&a).abs().div(&PI).frac();
                if sub1.get_mantissa_len() > 2 {
                    sub1 = ONE.sub(&sub1);
                }
                if sub2.get_mantissa_len() > 2 {
                    sub2 = ONE.sub(&sub2);
                }
                assert!(sub1.get_mantissa_len() < 5 || sub2.get_mantissa_len() < 5);
            }
        }

        // x axis crossing points: PI/2, 3*PI/2
        let n = HALF_PI.cos();
        assert!(n.is_zero() || ZERO.sub(&n).get_exponent() < -(DECIMAL_POSITIONS as i8) - 38);

        let n = HALF_PI.add(&PI).cos();
        assert!(n.is_zero() || ZERO.sub(&n).get_exponent() < -(DECIMAL_POSITIONS as i8) - 38);

        // cos extremums: 0, PI
        let eps = BigFloat::parse("1.0e-39").unwrap();
        test_extremum(BigFloat::cos, &ZERO, &ONE, 3, 2, 2, &eps, exp_err);
        test_extremum(BigFloat::cos, &PI, &ONE.inv_sign(), 3, 2, 2, &eps, exp_err);

        // acos extremums: 1, -1
        let exp_err = -(DECIMAL_POSITIONS as i8) - 18;
        test_extremum(BigFloat::acos, &ONE, &ZERO, 2, 2, 22, &eps, exp_err);
        test_extremum(BigFloat::acos, &ONE.inv_sign(), &PI, 1, 2, 22, &eps, exp_err);

        // tan, atan
        for _ in 0..10000 {
            let num = random_normal_float(3, 40);
            let t = num.tan();
            let a = t.atan();
            if num.abs().cmp(&HALF_PI).unwrap() <= 0 {
                assert!(num.sub(&a).get_mantissa_len() < 3);
            } else {
                let mut sub1 = num.add(&a).abs().div(&PI).frac();
                let mut sub2 = num.sub(&a).abs().div(&PI).frac();
                if sub1.get_mantissa_len() > 2 {
                    sub1 = ONE.sub(&sub1);
                }
                if sub2.get_mantissa_len() > 2 {
                    sub2 = ONE.sub(&sub2);
                }
                assert!(sub1.get_mantissa_len() < 3 || sub2.get_mantissa_len() < 3);
            }
        }

        // near pi/2, -pi/2
        let n = HALF_PI.tan();
        assert!(n.get_mantissa_len() as i8 + n.get_exponent() > 39);
        let n = HALF_PI.sub(&eps).tan();
        assert!(n.get_mantissa_len() as i8 + n.get_exponent() > 39 && n.is_positive());
        let n = HALF_PI.inv_sign().tan();
        assert!(n.get_mantissa_len() as i8 + n.get_exponent() > 39);
        let n = HALF_PI.sub(&eps).inv_sign().tan();
        assert!(n.get_mantissa_len() as i8 + n.get_exponent() > 39 && n.is_negative());

        // atan for large negative and large positive.
        let n = MAX.atan();
        assert!(HALF_PI.sub(&n).get_mantissa_len() < 2);
        let n = MIN.atan();
        assert!(HALF_PI.inv_sign().sub(&n).get_mantissa_len() < 2);

        let mut n = MAX;
        n.set_exponent(n.get_exponent() - (DECIMAL_POSITIONS as i8));
        let n = n.atan();
        assert!(HALF_PI.sub(&n).get_mantissa_len() < 2);

        let mut n = MIN;
        n.set_exponent(n.get_exponent() - (DECIMAL_POSITIONS as i8));
        let n = n.atan();
        assert!(HALF_PI.inv_sign().sub(&n).get_mantissa_len() < 2);

        // sinh, asinh
        for _ in 0..10000 {
            let num = random_normal_float(90, 127);
            let s = num.sinh();
            let a = s.asinh();
            assert!(num.sub(&a).get_mantissa_len() < 4);
        }

        // cosh, acosh
        for _ in 0..10000 {
            let num = random_normal_float(90, 127);
            let s = num.sinh();
            let a = s.asinh();
            assert!(num.sub(&a).get_mantissa_len() < 4);
        }

        // cosh extremums at 0
        let exp_err = -(DECIMAL_POSITIONS as i8) - 38;
        let eps = BigFloat::parse("1.0e-19").unwrap();
        test_extremum(BigFloat::cosh, &ZERO, &ONE, 3, 2, 2, &eps, exp_err);

        // tanh, atanh
        for _ in 0..10000 {
            let num = random_normal_float(88, 127);
            let s = num.tanh();
            let a = s.atanh();
            assert!(num.sub(&a).get_mantissa_len() < 6);
        }
    }

    fn random_f64_exp(exp_range: i32, exp_shift: i32) -> f64 {
        let mut f: f64 = random();
        f = f.powi(random::<i32>().abs() % exp_range - exp_shift);
        if random::<i8>() & 1 == 0 {
            f = -f;
        }
        f
    }

    fn random_normal_float(exp_range: i32, exp_shift: i32) -> BigFloat {
        let mut mantissa = [0i16; DECIMAL_PARTS];
        for i in 0..DECIMAL_PARTS {
            mantissa[i] = (random::<u16>() % DECIMAL_BASE as u16) as i16;
        }
        if mantissa[DECIMAL_PARTS-1] == 0 {
            mantissa[DECIMAL_PARTS-1] = (DECIMAL_BASE-1) as i16;
        }
        while mantissa[DECIMAL_PARTS-1] / 1000 == 0 {
            mantissa[DECIMAL_PARTS-1] *= 10;
        }
        let sign = if random::<i8>() & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
        let exp = random::<i32>().abs() % exp_range - exp_shift;
        BigFloat::from_raw_parts(mantissa, DECIMAL_POSITIONS as i16, sign, exp as i8)
    }

    // test function extremum
    // sides: 3 - both, 2 - left, 1 - right, 0 - none (just exact value).
    // x - input value, y - expected value.
    // err - number of digits in mantissa allowed for error at point near extremum.
    // exact_err - number of digits in mantissa allowed for error at extremum.
    // exp_err - compare exponent of difference to exp_err
    fn test_extremum(f: fn (&BigFloat) -> BigFloat, x: &BigFloat, y: &BigFloat, sides: u8, 
                    exact_err: usize, err: usize, eps: &BigFloat, exp_err: i8) {
        let n = f(x);
        assert_close(&n, y, exact_err, exp_err);

        if sides & 1 != 0 {
            let x1 = x.add(eps);
            let n = f(&x1);
            assert_close(&n, y, err, exp_err);
        }

        if sides & 2 != 0 {
            let x1 = x.sub(eps);
            let n = f(&x1);
            assert_close(&n, y, err, exp_err);
        }
    }

    // assert n is close to y
    fn assert_close(n: &BigFloat, y: &BigFloat, err: usize, exp_err: i8) {
        assert!(n.cmp(y).unwrap() == 0 || n.sub(y).get_mantissa_len() < err || n.sub(y).get_exponent() < exp_err);
    }
}