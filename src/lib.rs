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
//! # #[cfg(feature = "std")] {
//! let six: BigFloat = 6.0.into(); // note: conversion from f64,f32 are not loss-less.
//! let three: BigFloat = BigFloat::parse("3.0").unwrap();
//! let pi = six * (ONE / three.sqrt()).atan();
//! let epsilon = 1.0e-38.into();
//! 
//! assert!((pi - PI).abs() < epsilon);
//! 
//! println!("{}", pi);
//! # }
//! // output: 3.141592653589793238462643383279502884196e-39
//! ```
//! 
//! `no_std` example:
//! 
//! ``` 
//! use num_bigfloat::BigFloat;
//! use num_bigfloat::ONE;
//! use num_bigfloat::PI;
//! 
//! // compute pi: pi = 6*arctan(1/sqrt(3))
//! let six: BigFloat = BigFloat::from_u8(6);
//! let three: BigFloat = BigFloat::from_u8(3);
//! let pi = six.mul(&ONE.div(&three.sqrt()).atan());
//! let epsilon = BigFloat::from_f64(1.0e-38);
//! 
//! assert!(pi.sub(&PI).abs().cmp(&epsilon).unwrap() < 0);
//! ```
//!
//! ## Precision
//!
//! The use of additional digits of the manitissa in calculations allows minimizing the error and rounding the results correctly (i.e. as if the result was a rounded infinitely precise number).
//! The precision of the results may be lost under certain conditions, such as when the argument is a subnormal number, or when the function is periodic, such as sine or cosine, when the argument is much larger than pi.
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

pub use crate::defs::RoundingMode;
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
        NAN,
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
        d2 = BigFloat::from_u32(12349999);
        d3 = d1.mul(&d2);
        assert!(d3.cmp(&ref_num) == Some(0));

        // 1 * 1
        d1 = BigFloat::from_u8(1);
        d2 = BigFloat::from_u8(1);
        d3 = d1.mul(&d2);
        assert!(d3.cmp(&d1) == Some(0));

        // 1 * -1
        d1 = BigFloat::from_u8(1);
        d2 = BigFloat::from_u8(1).inv_sign();
        d3 = d1.mul(&d2);
        assert!(d3.cmp(&d2) == Some(0));

        // -1 * 1
        d3 = d2.mul(&d1);
        assert!(d3.cmp(&d2) == Some(0));

        // -1 * -1
        d1 = d1.inv_sign();
        d3 = d1.mul(&d2);
        ref_num = BigFloat::from_u8(1);
        assert!(d3.cmp(&ref_num) == Some(0));

        // 0 / 0 
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        assert!(d1.div(&d2).is_nan());

        // d2 / 0
        d2 = BigFloat::from_u8(123);
        assert!(d2.div(&d1).is_inf_pos());

        // 0 / d2
        d3 = d1.div(&d2);
        ref_num = BigFloat::new();
        assert!(d3.cmp(&ref_num) == Some(0));

        // 0 / -d2
        d2 = d2.inv_sign();
        d3 = d1.div(&d2);
        assert!(d3.cmp(&ref_num) == Some(0));

        // add & sub
        for _ in 0..10000 {
            // avoid subnormal numbers
            d1 = random_normal_float(4, 30);
            d2 = random_normal_float(4, 34);
            let n1 = d1.add(&d2);
            let n2 = n1.sub(&d2);
            assert_small(&n2.sub(&d1), 2, &d1);
        }

        // mul & div
        for _ in 0..10000 {
            // avoid subnormal numbers
            d1 = random_normal_float(40, 40);
            d2 = random_normal_float(40, 40);
            if d2.cmp(&ZERO).unwrap() != 0 {
                let n1 = d1.div(&d2);
                let n2 = n1.mul(&d2);
                assert_small(&n2.sub(&d1), 2, &d1);
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
            assert_small(&num.sub(&ret), 2, &num);
        }

        // sqrt of max
        let n = MAX.sqrt();
        assert!(n.cmp(&ZERO).unwrap() > 0 && MAX.cmp(&n).unwrap() > 0);
        let n = n.mul(&n);
        assert_small_if_not(n.is_inf_pos(), &MAX.sub(&n), 2, &MAX);

        // sqrt of zero
        let n = ZERO.sqrt();
        assert!(n.cmp(&ZERO).unwrap() == 0);

        // sqrt of min positive
        let n = MIN_POSITIVE.sqrt();
        assert!(n.cmp(&ZERO).unwrap() > 0 && MIN_POSITIVE.cmp(&n).unwrap() < 0);
        let n = n.mul(&n);
        assert_small_if_not(n.is_zero(), &MIN_POSITIVE.sub(&n), 2, &MIN_POSITIVE);

        // sqrt of negative
        let n = MIN_POSITIVE.inv_sign().sqrt();
        assert!(n.is_nan());


        // cbrt
        for _ in 0..10000 {
            let num = random_normal_float(256, 128);
            let sq = num.cbrt();
            let ret = sq.mul(&sq).mul(&sq);
            assert_small(&num.sub(&ret), 2, &num);
        }

        // cbrt of max
        let n = MAX.cbrt();
        assert!(n.cmp(&ZERO).unwrap() > 0 && MAX.cmp(&n).unwrap() > 0);
        let n = n.mul(&n).mul(&n);
        assert_small_if_not(n.is_inf_pos(), &MAX.sub(&n), 2, &MAX);

        // cbrt of zero
        let n = ZERO.cbrt();
        assert!(n.cmp(&ZERO).unwrap() == 0);

        // cbrt of min positive
        let n = MIN_POSITIVE.cbrt();
        assert!(n.cmp(&ZERO).unwrap() > 0 && MIN_POSITIVE.cmp(&n).unwrap() < 0);
        let n = n.mul(&n).mul(&n);
        assert_small_if_not(n.is_zero(), &MIN_POSITIVE.sub(&n), 2, &MIN_POSITIVE);

        // cbrt of negative MAX
        let n = MAX.inv_sign().cbrt();
        assert!(n.cmp(&ZERO).unwrap() < 0 && MAX.inv_sign().cmp(&n).unwrap() < 0);
        let n = n.mul(&n).mul(&n);
        assert_small_if_not(n.is_inf_neg(), &MAX.inv_sign().sub(&n), 2, &MAX.inv_sign());

        // cbrt of negative MIN_POSITIVE
        let n = MIN_POSITIVE.inv_sign().cbrt();
        assert!(n.cmp(&ZERO).unwrap() < 0 && MIN_POSITIVE.inv_sign().cmp(&n).unwrap() > 0);
        let n = n.mul(&n).mul(&n);
        assert_small_if_not(n.is_zero(), &MIN_POSITIVE.inv_sign().sub(&n), 2, &MIN_POSITIVE.inv_sign());


        // pow
        for _ in 0..10000 {
            let a = random_normal_float(4, 40);
            let n = random_normal_float(4, 40);
            let inv = ONE.div(&n);
            let p = a.pow(&n);
            if  !p.is_inf() && p.get_mantissa_len() >= DECIMAL_POSITIONS - 1 {
                let ret = p.pow(&inv);
                assert_small(&a.sub(&ret), 3, &a);
            }
        }

        // one^any = one
        assert!(ONE.pow(&MIN_POSITIVE).cmp(&ONE).unwrap() == 0);
        assert!(ONE.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE).unwrap() == 0);
        assert!(ONE.pow(&MAX).cmp(&ONE).unwrap() == 0);
        assert!(ONE.pow(&MIN).cmp(&ONE).unwrap() == 0);
        assert!(ONE.pow(&TWO).cmp(&ONE).unwrap() == 0);
        assert!(ONE.pow(&ONE.div(&TWO)).cmp(&ONE).unwrap() == 0);
        assert!(ONE.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // (> 1)^n
        assert!(TWO.pow(&MIN_POSITIVE).cmp(&ONE).unwrap() == 0);
        assert!(TWO.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE).unwrap() == 0);
        assert!(TWO.pow(&MAX).is_inf_pos());
        assert!(TWO.pow(&MIN).is_zero());
        assert!(TWO.pow(&ONE).cmp(&TWO).unwrap() == 0);
        assert!(TWO.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // (< 1)^n
        let n = ONE.div(&TWO);
        assert!(n.pow(&MIN_POSITIVE).cmp(&ONE).unwrap() == 0);
        assert!(n.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE).unwrap() == 0);
        assert!(n.pow(&MAX).is_zero());
        assert!(n.pow(&MIN).is_inf_pos());
        assert!(n.pow(&ONE).cmp(&n).unwrap() == 0);
        assert!(n.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // 0^n
        assert!(ZERO.pow(&MIN_POSITIVE).is_zero());
        assert!(ZERO.pow(&MIN_POSITIVE.inv_sign()).is_inf_pos());
        assert!(ZERO.pow(&MAX).is_zero());
        assert!(ZERO.pow(&MIN).is_inf_pos());
        assert!(ZERO.pow(&ONE).is_zero());
        assert!(ZERO.pow(&ZERO).is_nan());

        // -(> 1)^n
        let n = TWO.inv_sign();
        assert!(n.pow(&MIN_POSITIVE).cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(n.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(n.pow(&MAX).is_inf_neg());
        assert!(n.pow(&MIN).is_zero());
        assert!(n.pow(&ONE).cmp(&TWO.inv_sign()).unwrap() == 0);
        assert!(n.pow(&TWO).is_positive());
        assert!(n.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // -(< 1)^n
        let n = ONE.div(&TWO).inv_sign();
        assert!(n.pow(&MIN_POSITIVE).cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(n.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(n.pow(&MAX).is_zero());
        assert!(n.pow(&MIN).is_inf_neg());
        assert!(n.pow(&ONE).cmp(&n).unwrap() == 0);
        assert!(n.pow(&TWO).is_positive());
        assert!(n.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // MAX^n
        assert!(MAX.pow(&MIN_POSITIVE).cmp(&ONE).unwrap() == 0);
        assert!(MAX.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE).unwrap() == 0);
        assert!(MAX.pow(&MAX).is_inf_pos());
        assert!(MAX.pow(&MIN).is_zero());
        assert!(MAX.pow(&ONE).cmp(&MAX).unwrap() == 0);
        assert!(MAX.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // MIN^n
        assert!(MIN.pow(&MIN_POSITIVE).cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(MIN.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(MIN.pow(&MAX).is_inf_neg());
        assert!(MIN.pow(&MIN).is_zero());
        assert!(MIN.pow(&ONE).cmp(&MIN).unwrap() == 0);
        assert!(MIN.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // MIN_POSITIVE^n
        assert!(MIN_POSITIVE.pow(&MIN_POSITIVE).cmp(&ONE).unwrap() == 0);
        assert!(MIN_POSITIVE.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE).unwrap() == 0);
        assert!(MIN_POSITIVE.pow(&MAX).is_zero());
        assert!(MIN_POSITIVE.pow(&MIN).is_inf_pos());
        assert!(MIN_POSITIVE.pow(&ONE).cmp(&MIN_POSITIVE).unwrap() == 0);
        assert!(MIN_POSITIVE.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // (-MIN_POSITIVE)^n
        let n = MIN_POSITIVE.inv_sign();
        assert!(n.pow(&MIN_POSITIVE).cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(n.pow(&MIN_POSITIVE.inv_sign()).cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(n.pow(&MAX).is_zero());
        assert!(n.pow(&MIN).is_inf_neg());
        assert!(n.pow(&ONE).cmp(&n).unwrap() == 0);
        assert!(n.pow(&TWO).is_positive());
        assert!(n.pow(&ZERO).cmp(&ONE).unwrap() == 0);

        // ln
        let ten = BigFloat::from_u8(10);
        for _ in 0..10000 {
            let num = random_normal_float(256, 127).abs();
            if num.is_zero() {
                assert!(num.ln().is_nan());
                assert!(num.log2().is_nan());
                assert!(num.log10().is_nan());
            } else {
                let l = num.ln();
                let e = l.exp();
                assert_small(&num.sub(&e), 4, &num);

                let l = num.log2();
                let e = TWO.pow(&l);
                assert_small(&num.sub(&e), 4, &num);

                let l = num.log10();
                let e = ten.pow(&l);
                assert_small(&num.sub(&e), 5, &num);
            }
        }

        let ops = [BigFloat::ln, BigFloat::log2, BigFloat::log10,];
        let bases = [crate::E, TWO, ten];
        for i in 0..ops.len() {
            let op = ops[i];
            let base = bases[i];

            // crossing x axis at x = 1
            let n = op(&ONE);
            assert_small_if_not(n.is_zero(), &ZERO.sub(&n), 2, &n);

            // ln of max
            let n = op(&MAX);
            assert!(n.cmp(&ZERO).unwrap() > 0 && MAX.cmp(&n).unwrap() > 0);
            let n = base.pow(&n);
            assert_small_if_not(n.is_inf_pos(), &MAX.sub(&n), 4, &MAX);

            // ln of min positive
            let n = op(&MIN_POSITIVE);
            assert!(n.cmp(&ZERO).unwrap() < 0 && MIN_POSITIVE.cmp(&n.abs()).unwrap() < 0);
            let n = base.pow(&n);
            assert_small_if_not(n.is_inf_neg(), &MIN_POSITIVE.sub(&n), 2, &n);

            // ln of negative
            let n = op(&MIN_POSITIVE.inv_sign());
            assert!(n.is_nan());

            // ln of zero
            let n = op(&ZERO.inv_sign());
            assert!(n.is_nan());
        }

        // log
        for _ in 0..10000 {
            let base = random_normal_float(256, 127).abs();
            let num = random_normal_float(256, 127).abs();
            if num.is_zero() || base.is_zero() {
                assert!(num.log(&base).is_nan());
            } else {
                let l = num.log(&base);
                let e = base.pow(&l);
                assert_small(&num.sub(&e), 5, &num);
            }
        }

        // log crossing x axis at x = 1
        let base1 = BigFloat::from_f64(5.4321);
        let base2 = BigFloat::from_f64(0.4321);
        let n = ONE.log(&base1);
        assert_small_if_not(n.is_zero(), &ZERO.sub(&n), 2, &n);
        let n = ONE.log(&base2);
        assert_small_if_not(n.is_zero(), &ZERO.sub(&n), 2, &n);

        // log of max
        let n = MAX.log(&base1);
        assert!(n.cmp(&ZERO).unwrap() > 0 && MAX.cmp(&n).unwrap() > 0);
        let n = base1.pow(&n);
        assert_small_if_not(n.is_inf_pos(), &MAX.sub(&n), 4, &MAX);
        let n = MAX.log(&base2);
        assert!(n.cmp(&ZERO).unwrap() < 0 && MAX.cmp(&n.inv_sign()).unwrap() > 0);
        let n = base2.pow(&n);
        assert_small_if_not(n.is_inf_pos(), &MAX.sub(&n), 2, &MAX);

        // log of min positive
        let n = MIN_POSITIVE.log(&base1);
        assert!(n.cmp(&ZERO).unwrap() < 0 && MIN_POSITIVE.cmp(&n.abs()).unwrap() < 0);
        let n = base1.pow(&n);
        assert_small_if_not(n.is_inf_neg(), &MIN_POSITIVE.sub(&n), 2, &n);
        let n = MIN_POSITIVE.log(&base2);
        assert!(n.cmp(&ZERO).unwrap() > 0 && MIN_POSITIVE.cmp(&n.abs()).unwrap() < 0);
        let n = base2.pow(&n);
        assert_small_if_not(n.is_inf_neg(), &MIN_POSITIVE.sub(&n), 2, &n);

        // log of negative
        let n = MIN_POSITIVE.inv_sign().log(&base1);
        assert!(n.is_nan());
        let n = MIN_POSITIVE.inv_sign().log(&base2);
        assert!(n.is_nan());

        // negative base
        assert!(TWO.log(&base1.inv_sign()).is_nan());

        // log of zero
        let n = ZERO.inv_sign().log(&base1);
        assert!(n.is_nan());
        let n = ZERO.inv_sign().log(&base2);
        assert!(n.is_nan());

        // zero base
        assert!(TWO.log(&ZERO).is_nan());

        
        // sin, asin
        for _ in 0..10000 {
            let num = random_normal_float(90, 127);
            let s = num.sin();
            let a = s.asin();
            assert!(HALF_PI.cmp(&a).unwrap() >= 0 && HALF_PI.inv_sign().cmp(&a).unwrap() <= 0);
            if num.abs().cmp(&HALF_PI).unwrap() <= 0 {
                assert_small(&num.sub(&a), 5, &num);
            } else {
                let mut sub1 = num.add(&a).abs().div(&PI).frac();
                let mut sub2 = num.sub(&a).abs().div(&PI).frac();
                if sub1.get_mantissa_len() > 5 {
                    sub1 = ONE.sub(&sub1);
                }
                if sub2.get_mantissa_len() > 5 {
                    sub2 = ONE.sub(&sub2);
                }
                assert_small_any(&sub1, &sub2, 5, &num);
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
        let eps = BigFloat::from_f64(1.0e-39);
        let exp_err = -(DECIMAL_POSITIONS as i8) - 18;
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

        // asin resulting to NAN
        let n = TWO.asin();
        assert!(n.is_nan());
        let n = TWO.inv_sign().asin();
        assert!(n.is_nan());

        // cos, acos
        for _ in 0..10000 {
            let num = random_normal_float(3, 40);
            let c = num.cos();
            let a = c.acos();
            assert!(PI.cmp(&a).unwrap() >= 0 && ZERO.inv_sign().cmp(&a).unwrap() <= 0);
            if num.abs().cmp(&PI).unwrap() <= 0 {
                assert_small(&num.abs().sub(&a), 5, &num);
            } else {
                let mut sub1 = num.add(&a).abs().div(&PI).frac();
                let mut sub2 = num.sub(&a).abs().div(&PI).frac();
                if sub1.get_mantissa_len() > 5 {
                    sub1 = ONE.sub(&sub1);
                }
                if sub2.get_mantissa_len() > 5 {
                    sub2 = ONE.sub(&sub2);
                }
                assert_small_any(&sub1, &sub2, 5, &num);
            }
        }

        // x axis crossing points: PI/2, 3*PI/2
        let n = HALF_PI.cos();
        assert!(n.is_zero() || ZERO.sub(&n).get_exponent() < -(DECIMAL_POSITIONS as i8) - 38);

        let n = HALF_PI.add(&PI).cos();
        assert!(n.is_zero() || ZERO.sub(&n).get_exponent() < -(DECIMAL_POSITIONS as i8) - 38);

        // cos extremums: 0, PI
        let eps = BigFloat::from_f64(1.0e-39);
        test_extremum(BigFloat::cos, &ZERO, &ONE, 3, 2, 2, &eps, exp_err);
        test_extremum(BigFloat::cos, &PI, &ONE.inv_sign(), 3, 2, 2, &eps, exp_err);

        // acos extremums: 1, -1
        let exp_err = -(DECIMAL_POSITIONS as i8) - 18;
        test_extremum(BigFloat::acos, &ONE, &ZERO, 2, 2, 22, &eps, exp_err);
        test_extremum(BigFloat::acos, &ONE.inv_sign(), &PI, 1, 2, 22, &eps, exp_err);

        // acos resulting to NAN
        let n = TWO.acos();
        assert!(n.is_nan());
        let n = TWO.inv_sign().acos();
        assert!(n.is_nan());

        // tan, atan
        for _ in 0..10000 {
            let num = random_normal_float(3, 40);
            let t = num.tan();
            let a = t.atan();
            assert!(HALF_PI.cmp(&a).unwrap() >= 0 && HALF_PI.inv_sign().cmp(&a).unwrap() <= 0);
            if num.abs().cmp(&HALF_PI).unwrap() <= 0 {
                assert_small(&num.sub(&a), 2, &num);
            } else {
                let mut sub1 = num.add(&a).abs().div(&PI).frac();
                let mut sub2 = num.sub(&a).abs().div(&PI).frac();
                if sub1.get_mantissa_len() > 2 {
                    sub1 = ONE.sub(&sub1);
                }
                if sub2.get_mantissa_len() > 2 {
                    sub2 = ONE.sub(&sub2);
                }
                assert_small_any(&sub1, &sub2, 2, &num);
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
        assert_small(&HALF_PI.sub(&n), 2, &HALF_PI);
        let n = MIN.atan();
        assert_small(&HALF_PI.inv_sign().sub(&n), 2, &HALF_PI.inv_sign());

        let mut n = MAX;
        n.set_exponent(n.get_exponent() - (DECIMAL_POSITIONS as i8));
        let n = n.atan();
        assert_small(&HALF_PI.sub(&n), 2, &HALF_PI);

        let mut n = MIN;
        n.set_exponent(n.get_exponent() - (DECIMAL_POSITIONS as i8));
        let n = n.atan();
        assert_small(&HALF_PI.inv_sign().sub(&n), 2, &HALF_PI.inv_sign());

        // sinh, asinh
        for _ in 0..10000 {
            let num = random_normal_float(91, 127);
            let s = num.sinh();
            let a = s.asinh();
            if !a.is_inf() && !s.is_inf() {
                assert_small(&num.sub(&a), 2, &num);
            }
        }

        // sinh of MAX
        let n = MAX.sinh();
        assert!(n.is_inf_pos());
        let n = MIN.sinh();
        assert!(n.is_inf_neg());

        // asinh of MAX
        let n = MAX.asinh();
        assert!(n.cmp(&MAX).unwrap() < 0);
        let n = n.sinh();
        assert_small_if_not(n.is_inf_pos(), &MAX.sub(&n), 4, &MAX);
        let n = MIN.asinh();
        assert!(n.cmp(&MIN).unwrap() > 0);
        let n = n.sinh();
        assert_small_if_not(n.is_inf_neg(), &MIN.sub(&n), 4, &MIN);

        // cosh, acosh
        for _ in 0..10000 {
            let num = random_normal_float(4, 40);
            let s = num.cosh();
            let a = s.acosh();
            if !a.is_inf() && !s.is_inf() {
                assert_small(&num.abs().sub(&a), 3, &num);
            }
        }

        // cosh extremums at 0
        let exp_err = -(DECIMAL_POSITIONS as i8) - 37;
        let eps = BigFloat::from_f64(1.0e-19);
        test_extremum(BigFloat::cosh, &ZERO, &ONE, 3, 2, 2, &eps, exp_err);

        // cosh of MAX
        let n = MAX.cosh();
        assert!(n.is_inf_pos());
        let n = MIN.cosh();
        assert!(n.is_inf_pos());

        // acosh of MAX
        let n = MAX.acosh();
        assert!(n.cmp(&MAX).unwrap() < 0);
        let n = n.cosh();
        assert_small_if_not(n.is_inf_pos(), &MAX.sub(&n), 2, &MAX);

        // acosh extrema at 1
        let exp_err = -(DECIMAL_POSITIONS as i8) - 18;
        let eps = BigFloat::from_f64(1.0e-39);
        test_extremum(BigFloat::acosh, &ONE, &ZERO, 1, 2, 2, &eps, exp_err);

        // acosh resulting to NAN
        let n = ZERO.acosh();
        assert!(n.is_nan());

        // tanh, atanh
        for _ in 0..10000 {
            let num = random_normal_float(88, 127);
            let s = num.tanh();
            let a = s.atanh();
            assert_small(&num.sub(&a), 2, &num);
        }

        // tanh of MAX
        let n = MAX.tanh();
        assert!(n.cmp(&ONE).unwrap() == 0);
        let n = MIN.tanh();
        assert!(n.cmp(&ONE.inv_sign()).unwrap() == 0);

        // atanh of 1, -1
        let n = ONE.atanh();
        assert!(n.is_inf_pos());
        let n = ONE.inv_sign().atanh();
        assert!(n.is_inf_neg());

        // atanh of MAX
        let n = MAX.atanh();
        assert!(n.sub(&ZERO).get_mantissa_len() < 2);
        let n = MIN.atanh();
        assert!(n.sub(&ZERO).get_mantissa_len() < 2);

        // atanh resulting to NAN
        let n = TWO.atanh();
        assert!(n.is_nan());
        let n = TWO.inv_sign().atanh();
        assert!(n.is_nan());

        // min, max
        for _ in 0..1000 {
            let num1 = random_normal_float(256, 127);
            let num2 = random_normal_float(256, 127);
            let n1 = num1.max(&num2);
            let n2 = num1.min(&num2);
            if num1.cmp(&num2).unwrap() > 0 {
                assert!(n1.cmp(&num1).unwrap() == 0);
                assert!(n2.cmp(&num2).unwrap() == 0);
            } else {
                assert!(n1.cmp(&num2).unwrap() == 0);
                assert!(n2.cmp(&num1).unwrap() == 0);
            }
        }

        assert!(ONE.max(&INF_POS).cmp(&INF_POS).unwrap() == 0);
        assert!(INF_POS.max(&ONE).cmp(&INF_POS).unwrap() == 0);
        assert!(ONE.max(&INF_NEG).cmp(&ONE).unwrap() == 0);
        assert!(INF_NEG.max(&ONE).cmp(&ONE).unwrap() == 0);
        assert!(INF_POS.max(&INF_NEG).cmp(&INF_POS).unwrap() == 0);
        assert!(INF_NEG.max(&INF_POS).cmp(&INF_POS).unwrap() == 0);
        assert!(NAN.max(&ONE).is_nan());
        assert!(NAN.max(&NAN).is_nan());
        assert!(ONE.max(&NAN).is_nan());
        assert!(INF_POS.max(&NAN).is_nan());
        assert!(INF_NEG.max(&NAN).is_nan());
        assert!(NAN.max(&INF_POS).is_nan());
        assert!(NAN.max(&INF_NEG).is_nan());

        assert!(ONE.min(&INF_POS).cmp(&ONE).unwrap() == 0);
        assert!(INF_POS.min(&ONE).cmp(&ONE).unwrap() == 0);
        assert!(ONE.min(&INF_NEG).cmp(&INF_NEG).unwrap() == 0);
        assert!(INF_NEG.min(&ONE).cmp(&INF_NEG).unwrap() == 0);
        assert!(INF_POS.min(&INF_NEG).cmp(&INF_NEG).unwrap() == 0);
        assert!(INF_NEG.min(&INF_POS).cmp(&INF_NEG).unwrap() == 0);
        assert!(NAN.min(&ONE).is_nan());
        assert!(NAN.min(&NAN).is_nan());
        assert!(ONE.min(&NAN).is_nan());
        assert!(INF_POS.min(&NAN).is_nan());
        assert!(INF_NEG.min(&NAN).is_nan());
        assert!(NAN.min(&INF_POS).is_nan());
        assert!(NAN.min(&INF_NEG).is_nan());

        // clamp
        for _ in 0..1000 {
            let num1 = random_normal_float(256, 127);
            let num2 = random_normal_float(256, 127);
            let num3 = random_normal_float(256, 127);
            let upper = num1.max(&num2);
            let lower = num1.min(&num2);
            let n = num3.clamp(&lower, &upper);
            assert!(n.cmp(&upper).unwrap() <= 0);
            assert!(n.cmp(&lower).unwrap() >= 0);
        }

        assert!(TWO.clamp(&ONE, &ONE).cmp(&ONE).unwrap() == 0);
        assert!(INF_POS.clamp(&ONE, &TWO).cmp(&TWO).unwrap() == 0);
        assert!(INF_NEG.clamp(&ONE, &TWO).cmp(&ONE).unwrap() == 0);

        assert!(ONE.clamp(&INF_NEG, &INF_POS).cmp(&ONE).unwrap() == 0);
        assert!(INF_POS.clamp(&INF_NEG, &INF_POS).cmp(&INF_POS).unwrap() == 0);
        assert!(INF_NEG.clamp(&INF_NEG, &INF_POS).cmp(&INF_NEG).unwrap() == 0);

        assert!(ONE.clamp(&TWO, &INF_POS).cmp(&TWO).unwrap() == 0);
        assert!(INF_POS.clamp(&TWO, &INF_POS).cmp(&INF_POS).unwrap() == 0);
        assert!(INF_NEG.clamp(&TWO, &INF_POS).cmp(&TWO).unwrap() == 0);

        assert!(TWO.clamp(&INF_NEG, &ONE).cmp(&ONE).unwrap() == 0);
        assert!(INF_POS.clamp(&INF_NEG, &ONE).cmp(&ONE).unwrap() == 0);
        assert!(INF_NEG.clamp(&INF_NEG, &ONE).cmp(&INF_NEG).unwrap() == 0);

        assert!(ZERO.clamp(&INF_POS, &INF_NEG).is_nan());
        assert!(ZERO.clamp(&TWO, &ONE).is_nan());
        assert!(ZERO.clamp(&INF_POS, &ONE).is_nan());
        assert!(ZERO.clamp(&TWO, &INF_NEG).is_nan());

        for i in 1..0b111 {
            let n1 = if i & 1 == 0 { NAN } else { ONE };
            let n2 = if i & 0b10 == 0 { NAN } else { ONE };
            let n3 = if i & 0b100 == 0 { NAN } else { ONE };
            assert!(n1.clamp(&n2, &n3).is_nan());
        }

        // signum
        assert!(TWO.signum().cmp(&ONE).unwrap() == 0);
        assert!(ZERO.signum().cmp(&ONE).unwrap() == 0);
        assert!(TWO.inv_sign().signum().cmp(&ONE.inv_sign()).unwrap() == 0);
        assert!(NAN.signum().is_nan());
        assert!(INF_POS.signum().cmp(&ONE).unwrap() == 0);
        assert!(INF_NEG.signum().cmp(&ONE.inv_sign()).unwrap() == 0);
    }
    
    #[test]
    fn test_stable() {
        let mut d1: BigFloat;
        let mut d2: BigFloat;
        
        for _ in 0..1000 {
            d1 = random_normal_float(4, 30);
            d2 = random_normal_float(4, 34);
            check_stable1(BigFloat::add, BigFloat::sub, &d1, &d2);
        }

        for _ in 0..1000 {
            d1 = random_normal_float(40, 40);
            d2 = random_normal_float(40, 40);
            check_stable1(BigFloat::mul, BigFloat::div, &d1, &d2);
        }

        for _ in 0..1000 {
            d1 = random_normal_float(256, 128).abs();
            check_stable2(BigFloat::sqrt, |x| {x.mul(x)}, &d1);
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(256, 128).abs();
            check_stable2(BigFloat::cbrt, |x| {x.mul(x).mul(x)}, &d1);
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(256, 127).abs();
            check_stable2(BigFloat::ln, BigFloat::exp, &d1);
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(256, 127).abs();
            let d2 = random_normal_float(256, 127).abs();
            if !d1.is_zero() && !d1.is_zero() {
                check_stable1(BigFloat::log, |p1, p2| {BigFloat::pow(p2, p1)}, &d1, &d2);
            }
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(90, 127).abs();
            check_stable2(BigFloat::sin, BigFloat::asin, &d1);
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(3, 40).abs();
            check_stable2(BigFloat::cos, BigFloat::acos, &d1);
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(3, 40).abs();
            check_stable2(BigFloat::tan, BigFloat::atan, &d1);
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(91, 127);
            check_stable2(BigFloat::sinh, BigFloat::asinh, &d1);
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(91, 127);
            check_stable2(BigFloat::cosh, BigFloat::acosh, &d1);
        }
    
        for _ in 0..1000 {
            d1 = random_normal_float(88, 127);
            check_stable2(BigFloat::tanh, BigFloat::atanh, &d1);
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
        let exp = (if exp_range != 0 {random::<i32>().abs() % exp_range} else {0}) - exp_shift;
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

    // assert v is as large as ndigits digits of scale_num's mantissa, i.e. make sure v << scale_num
    fn assert_small(v: &BigFloat, ndigits: i32, scale_num: &BigFloat) {
        let eps = get_assert_small_eps(ndigits, scale_num);
        assert!(v.abs().cmp(&eps).unwrap() < 0);
    }

    // assert_small if not other condition true
    fn assert_small_if_not(cond: bool, v: &BigFloat, ndigits: i32, scale_num: &BigFloat) {
        if !cond {
            assert_small(v, ndigits, scale_num);
        }
    }

    // assert_small either for v1 or for v2
    fn assert_small_any(v1: &BigFloat, v2: &BigFloat, ndigits: i32, scale_num: &BigFloat) {
        let eps = get_assert_small_eps(ndigits, scale_num);
        assert!(v1.abs().cmp(&eps).unwrap() < 0 || v2.abs().cmp(&eps).unwrap() < 0);
    }

    // prepare epsilon value
    fn get_assert_small_eps(ndigits: i32, scale_num: &BigFloat) -> BigFloat {
        let mut eps = ONE;
        let e = ndigits - eps.get_mantissa_len() as i32 - (DECIMAL_POSITIONS as i32) + scale_num.get_exponent() as i32 + scale_num.get_mantissa_len() as i32;
        if e < DECIMAL_MIN_EXPONENT as i32 {
            eps = MIN_POSITIVE;
            if e + DECIMAL_POSITIONS as i32 > DECIMAL_MIN_EXPONENT as i32 {
                eps.set_exponent((e + DECIMAL_POSITIONS as i32) as i8);
            }
        } else if e > DECIMAL_MAX_EXPONENT as i32 {
            eps = MAX;
        } else {
            eps.set_exponent(e as i8);
        }
        eps
    }

    // make sure consecutive application of f and inverse f do not diverge
    fn check_stable1(f: fn (&BigFloat, &BigFloat) -> BigFloat, 
                    finv: fn (&BigFloat, &BigFloat) -> BigFloat, 
                    d1: &BigFloat, 
                    d2: &BigFloat) {
        let mut n1 = *d1;
        let mut n2;
        for _ in 0..10 {
            let p = f(&n1, d2);
            n2 = finv(&p, d2);
            n1 = n2;
        }
        n2 = f(&n1, d2);
        n2 = finv(&n2, d2);
        assert!((n1.is_nan() && n2.is_nan()) || n1.cmp(&n2).unwrap() == 0);              
    }


    // make sure consecutive application of f and inverse f do not diverge
    fn check_stable2(f: fn (&BigFloat) -> BigFloat, 
                    finv: fn (&BigFloat) -> BigFloat, 
                    d1: &BigFloat) {
        let mut n1 = *d1;
        let mut n2;
        for _ in 0..10 {
            let p = f(&n1);
            n2 = finv(&p);
            n1 = n2;
        }
        n2 = f(&n1);
        n2 = finv(&n2);
        assert!((n1.is_nan() && n2.is_nan()) || n1.cmp(&n2).unwrap() == 0);            
    }
    
}