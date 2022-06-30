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
//! let six: BigFloat = 6.0.into();
//! let three: BigFloat = 3.0.into();
//! let pi = six * (ONE / three.sqrt()).atan();
//! let epsilon = 1.0e-39.into();
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
//! With regard to anything else, the implementation is straightforward and does not utilize sophisticated algorithms.
//! 
//! ## no_std
//!
//! Library can be used without the standard Rust library. This can be achieved by turning off `std` feature.

#![deny(clippy::suspicious)]

mod defs;
mod inc;
mod ops;
mod ext;

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
    use crate::defs::BigFloatNum;
    use crate::defs::Error;
    use crate::defs::{
        DECIMAL_SIGN_POS, 
        DECIMAL_SIGN_NEG, 
        DECIMAL_MIN_EXPONENT, 
        DECIMAL_MAX_EXPONENT, 
        DECIMAL_POSITIONS,
        ONE,
        MIN,
        MAX,
        MIN_POSITIVE,
    };


    #[test]
    fn test_bigfloat() {

        //
        // creation and deconstruction
        //

        let mut d1;

        // regular buf
        let bytes1: [u8; 20] = [1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20];
        let expected1: [u8; 30] = [1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,0,0,0,0,0,0,0,0,0,0];
        let exp1 = 123;
        let d4 = BigFloatNum::from_bytes(&bytes1, 1, exp1);

        let mut mantissa_buf1 = [0; 30];
        d4.get_mantissa_bytes(&mut mantissa_buf1);
        assert!(mantissa_buf1 == expected1);
        assert!(d4.get_mantissa_len() == bytes1.len());
        assert!(d4.sign == 1);
        assert!(d4.e == exp1);

        // too long buf
        let bytes2: [u8; 45] = [1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20,1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20,21,22,3,4,5];
        let expected2: [u8; 42] = [1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,0,0];
        let exp2 = -128;
        let d4 = BigFloatNum::from_bytes(&bytes2, -2, exp2);

        let mut mantissa_buf2 = [0; 42];
        d4.get_mantissa_bytes(&mut mantissa_buf2);
        assert!(mantissa_buf2 == expected2);
        assert!(d4.get_mantissa_len() == 40);
        assert!(d4.sign == -1);
        assert!(d4.e == exp2);


        //
        // conversions
        //


        for _ in 0..1000 {
            let i: i8 = random::<i8>() % 10i8;
            let mut f: f64 = random::<f64>().powf(i as f64);
            if i & 1 == 0 {
                f = -f;
            }
            d1 = BigFloatNum::from_f64(f).unwrap();
            let f2 = d1.to_f64();
            if f2 != 0f64 {
                assert!((1f64 - f/f2).abs() < 0.000000000000001f64);
            } else {
                assert!((f - f2).abs() < 0.000000000000001f64);
            }
        }

        for _ in 0..1000 {
            let i: i8 = random::<i8>() % 10i8;
            let mut f: f32 = random::<f32>().powf(i as f32);
            if i & 1 == 0 {
                f = -f;
            }
            d1 = BigFloatNum::from_f32(f).unwrap();
            let f2 = d1.to_f32();
            if f2 != 0f32 {
                assert!((1f32 - f/f2).abs() < 0.000001f32);
            } else {
                assert!((f - f2).abs() < 0.000001f32);
            }
        }
    }


    #[test]
    fn test_num() {

        let mut d1;
        let mut d2;
        let mut d3;
        let mut ref_num;

        // inf
        assert!(BigFloatNum::from_f64(f64::INFINITY).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));
        assert!(BigFloatNum::from_f64(f64::NEG_INFINITY).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_NEG));

        // nan
        assert!(BigFloatNum::from_f64(f64::NAN).unwrap_err() == Error::InvalidArgument);

        // 0.0
        assert!(BigFloatNum::from_f64(0.0).unwrap().to_f64() == 0.0);

        d1 = BigFloatNum::from_f64(1.3510326597545574e-124).unwrap();
        d1.to_f64();

        // conversions
        for _ in 0..10000 {
            let f: f64 = random_f64_exp(50, 25);
            if f.is_finite() && f != 0.0 {
                d1 = BigFloatNum::from_f64(f).unwrap();
                assert!((d1.to_f64() / f - 1.0).abs() < 1000.0*f64::EPSILON);
                if (f as f32).is_finite() && (f as f32) != 0.0 {
                    d1 = BigFloatNum::from_f32(f as f32).unwrap();
                    assert!((d1.to_f32() / f as f32 - 1.0).abs() < 1000.0*f32::EPSILON);
                }
            }
        }

        // 0 * 0
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0.99 * 0
        d1 = BigFloatNum::from_f64(0.99).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 * 12349999
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::from_f64(12349999.0).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * 1
        d1 = BigFloatNum::from_f64(1.0).unwrap();
        d2 = BigFloatNum::from_f64(1.0).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&d1) == 0);

        // 1 * -1
        d1 = BigFloatNum::from_f64(1.0).unwrap();
        d2 = BigFloatNum::from_f64(1.0).unwrap().inv_sign();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * 1
        d3 = d2.mul(&d1).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * -1
        d1 = d1.inv_sign();
        d3 = d1.mul(&d2).unwrap();
        ref_num = BigFloatNum::from_f64(1.0).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / 0 
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        assert!(d1.div(&d2).unwrap_err() == Error::DivisionByZero);

        // d2 / 0
        d2 = BigFloatNum::from_f64(123.0).unwrap();
        assert!(d2.div(&d1).unwrap_err() == Error::DivisionByZero);

        // 0 / d2
        d3 = d1.div(&d2).unwrap();
        ref_num = BigFloatNum::new();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / -d2
        d2 = d2.inv_sign();
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);


        // add & sub & cmp
        for _ in 0..10000 {
            // avoid subnormal numbers
            let f1 = random_f64_exp(50, 25);
            let f2 = random_f64_exp(50, 25);
            if f1.is_finite() && f2.is_finite() {
                let f3 = f1 + f2;
                let f4 = f1 - f2;
                d1 = BigFloatNum::from_f64(f1).unwrap();
                d2 = BigFloatNum::from_f64(f2).unwrap();
                if f3 == 0.0 {
                    assert!(d1.add(&d2).unwrap().to_f64().abs() <= 10000.0*f64::EPSILON);
                } else {
                    assert!((d1.add(&d2).unwrap().to_f64() / f3 - 1.0).abs() <= 10000.0*f64::EPSILON);
                }
                if f4 == 0.0 {
                    assert!(d1.sub(&d2).unwrap().to_f64().abs() <= 10000.0*f64::EPSILON);
                } else {
                    assert!((d1.sub(&d2).unwrap().to_f64() / f4 - 1.0).abs() <= 10000.0*f64::EPSILON);
                }
                if f1 > f2 {
                    assert!(d1.cmp(&d2) > 0);
                } else if f1 < f2 {
                    assert!(d1.cmp(&d2) < 0);
                } else {
                    assert!(d1.cmp(&d2) == 0);
                }
            }
        }

        // mul & div
        for _ in 0..10000 {
            // avoid subnormal numbers
            let f1 = random_f64_exp(50, 25);
            let f2 = random_f64_exp(50, 25);
            if f1.is_finite() && f2.is_finite() && f2 != 0.0 {
                let f3 = f1*f2;
                let f4 = f1/f2;
                d1 = BigFloatNum::from_f64(f1).unwrap();
                d2 = BigFloatNum::from_f64(f2).unwrap();
                assert!((d1.mul(&d2).unwrap().to_f64() / f3 - 1.0).abs() <= 10000.0*f64::EPSILON);
                assert!((d1.div(&d2).unwrap().to_f64() / f4 - 1.0).abs() <= 10000.0*f64::EPSILON);
            }
        }


        // subnormal numbers
        d1 = MIN_POSITIVE;
        d2 = MIN_POSITIVE;
        ref_num = MIN_POSITIVE;
        ref_num.m[0] = 2;
        ref_num.n = 1;

        // min_positive + min_positive = 2*min_positive
        assert!(d1.add(&d2).unwrap().cmp(&ref_num) == 0);
        assert!(d1.add(&d2).unwrap().cmp(&d1) > 0);
        assert!(d1.cmp(&d1.add(&d2).unwrap()) < 0);

        // min_positive - min_positive = 0
        ref_num = BigFloatNum::new();
        assert!(d1.sub(&d2).unwrap().cmp(&ref_num) == 0);

        // 1 * min_positive = min_positive
        assert!(ONE.mul(&d2).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&ONE).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&ONE).unwrap().cmp(&d2) == 0);

        // normal -> subnormal -> normal
        d1 = ONE;
        d1.e = DECIMAL_MIN_EXPONENT;
        d2 = MIN_POSITIVE;
        assert!(!d1.is_subnormal());
        assert!(d1.sub(&d2).unwrap().cmp(&d1) < 0);
        assert!(d1.cmp(&d1.sub(&d2).unwrap()) > 0);
        d1 = d1.sub(&d2).unwrap();
        assert!(d1.is_subnormal());
        d1 = d1.add(&d2).unwrap();
        assert!(!d1.is_subnormal());

        // overflow
        d1 = ONE;
        d1.e = DECIMAL_MAX_EXPONENT - (DECIMAL_POSITIONS as i8 - 1);
        assert!(MAX.add(&d1).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));
        assert!(MIN.sub(&d1).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_NEG));
        assert!(MAX.mul(&MAX).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));
        d1 = ONE;
        d1.e = DECIMAL_MIN_EXPONENT;
        assert!(MAX.div(&d1).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));

        // fract & int
        let f1 = 12345.6789;
        d1 = BigFloatNum::from_f64(f1).unwrap();
        assert!((d1.frac().to_f64() - f1.fract()).abs() < 100000.0*f64::EPSILON);
        assert!((d1.int().to_f64() - (f1 as u64) as f64).abs() < 100000.0*f64::EPSILON);

        let f1 = -0.006789;
        d1 = BigFloatNum::from_f64(f1).unwrap();
        assert!(d1.frac().cmp(&d1) == 0);
        assert!(d1.int().is_zero());

        d1 = BigFloatNum::from_bytes(&[2,2,2,2,2,0,0,0], DECIMAL_SIGN_POS, -2);
        assert!(d1.frac().is_zero());
        assert!(d1.int().cmp(&d1) == 0);

        assert!(MIN_POSITIVE.frac().cmp(&MIN_POSITIVE) == 0);
        assert!(MIN_POSITIVE.int().is_zero());

        d1 = BigFloatNum::new();
        assert!(d1.frac().is_zero());
        assert!(d1.int().is_zero());

        // ceil & floor
        d1 = BigFloatNum::from_f64(12.3).unwrap();
        assert!(d1.floor().unwrap().to_f64() == 12.0);
        assert!(d1.ceil().unwrap().to_f64() == 13.0);
        d1 = BigFloatNum::from_f64(12.0).unwrap();
        assert!(d1.floor().unwrap().to_f64() == 12.0);
        assert!(d1.ceil().unwrap().to_f64() == 12.0);

        d1 = BigFloatNum::from_f64(-12.3).unwrap();
        assert!(d1.floor().unwrap().to_f64() == -13.0);
        assert!(d1.ceil().unwrap().to_f64() == -12.0);
        d1 = BigFloatNum::from_f64(-12.0).unwrap();
        assert!(d1.floor().unwrap().to_f64() == -12.0);
        assert!(d1.ceil().unwrap().to_f64() == -12.0);

        // abs
        d1 = BigFloatNum::from_f64(12.3).unwrap();
        assert!(d1.abs().to_f64() == 12.3);
        d1 = BigFloatNum::from_f64(-12.3).unwrap();
        assert!(d1.abs().to_f64() == 12.3);
    }

    fn random_f64_exp(max_exp: i32, min_exp: i32) -> f64 {
        let mut f: f64 = random();
        f = f.powi(random::<i32>().abs() % max_exp - min_exp);
        if random::<i8>() & 1 == 0 {
            f = -f;
        }
        f
    }

}