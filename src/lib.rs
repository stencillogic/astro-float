//! Multiple precision floating point numbers implemented purely in Rust. 
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
//! use num_bigfloat::ext::BigFloatExt;
//! use num_bigfloat::ext::ONE;
//! use num_bigfloat::ext::PI;
//!
//! // compute pi: pi = 6*arctan(1/sqrt(3))
//! let six: BigFloatExt = 6.0.into();
//! let three: BigFloatExt = 3.0.into();
//! let pi = six * (ONE / three.sqrt()).atan();
//! let epsilon = 1.0e-39.into();
//! 
//! assert!((pi - PI).abs() < epsilon);
//! 
//! println!("{}", pi);
//! // output: 3.141592653589793238462643383279502884196e-39
//! ```
//! 
//! ## no_std
//!
//! Library can be used without the standard Rust library. This can be achieved by turning off `std` feature.

#![deny(clippy::suspicious)]

//mod defs;
//mod increased;
mod ops;
mod num;

//pub mod ext;

/* 
pub use crate::defs::BigFloat;
pub use crate::defs::Error;

pub use crate::defs::E;
pub use crate::defs::PI;



#[cfg(test)]
mod tests {

    use super::*;
    use rand::random;
    use crate::defs::DECIMAL_PARTS;


    #[test]
    fn test_bigfloat() {


        //
        // creation and deconstruction
        //

        let mut d1;

        assert!(DECIMAL_PARTS >= 10);

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

        // raw parts
        let (m,n,s,e) = d4.to_raw_parts();
        let d5 = BigFloat::from_raw_parts(m,n,s,e);
        assert!(d5.cmp(&d4) == 0);


        //
        // conversions
        //


        for _ in 0..1000 {
            let i: i8 = random::<i8>() % 10i8;
            let mut f: f64 = random::<f64>().powf(i as f64);
            if i & 1 == 0 {
                f = -f;
            }
            d1 = BigFloat::from_f64(f).unwrap();
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
            d1 = BigFloat::from_f32(f).unwrap();
            let f2 = d1.to_f32();
            if f2 != 0f32 {
                assert!((1f32 - f/f2).abs() < 0.000001f32);
            } else {
                assert!((f - f2).abs() < 0.000001f32);
            }
        }
    }
}
*/