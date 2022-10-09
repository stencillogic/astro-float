//! Astro-float (astronomically large floating point numbers) is a library that implements arbitrary precision floating point numbers purely in Rust.
//!
//! ## Introduction
//! 
//! **Numbers**
//! 
//! 
//! The number is defined by the data type `BigFloatNumber`. Each number consists of an array of words representing the mantissa, an exponent, and the sign of the number.
//! 
//! 
//! `BigFloatNumber` creation operations take bit precision as an argument. Precision is always rounded up to the nearest word. For example, if you specify a precision of 1 bit, then it will be converted to 64 bits when one word has a size of 64 bits. If you specify a precision of 65 bits, the resulting precision will be 128 bits (2 words), and so on.
//! 
//! 
//! In most cases, unless explicitly stated, performing an operation on numbers of different precision results in a number with a precision equal to the highest precision of the operation arguments. For example, if two numbers with a precision of 128 and 192 are added together, the result will have a precision of 192.
//! 
//! 
//! Most operations take the rounding mode as an argument. The operation will typically internally result in a number with more precision than necessary. Before the result is returned to the user, the result is rounded according to the rounding mode, and reduced to the expected precision.
//! 
//! 
//! `BigFloatNumber` can be parsed from a string and formatted into a string using binary, octal, decimal, or hexadecimal representation.
//! 
//! 
//! Numbers can be subnormal. Usually any number is normalized: the most significant bit of the mantissa is set to 1. If the result of the operation has the smallest possible exponent, then normalization cannot be performed, and some significant bits of the mantissa may become 0. This allows for a more gradual transition to zero.
//! 
//! 
//! **Constants**
//! 
//! 
//! Constants such as pi or the Euler number have arbitrary precision and are evaluated lazily and then cached in the thread-local cache.
//! 
//! 
//! **Performance**
//! 
//! Since it is allowed to use numbers with different precision in operations, it is desirable to use lower precision where possible.
//! For example, multiplying a number with a value of 0.123... with a precision of 64000 by a number with a value of 3 with a precision of 64 is much faster than multiplying with a number with a value of 3 with a precision of 64000 and the result will be the same.
//! 
//!  
//! ## Examples
//! 
//! 
//! ``` rust
//! use astro_float::BigFloatNumber;
//! use astro_float::PI;
//! use astro_float::RoundingMode;
//! use astro_float::Radix;
//! use astro_float::Error;
//! 
//! // Rounding of all operations
//! let rm = RoundingMode::ToEven;
//! 
//! // Compute pi: pi = 6*arctan(1/sqrt(3))
//! let six = BigFloatNumber::from_word(6, 1).unwrap();
//! let three = BigFloatNumber::parse("3.0", Radix::Dec, 1024+8, rm).unwrap();  // +8 bits of precision to cover error
//! let mut pi = six.mul(&three.sqrt(rm).unwrap().reciprocal(rm).unwrap().atan(rm).unwrap(), rm).unwrap();
//! pi.set_precision(1024, rm).unwrap();
//! let mut epsilon = BigFloatNumber::from_word(1, 1).unwrap();
//! epsilon.set_exponent(-1021);
//! 
//! // Use library's constant for verifying the result
//! let pi_lib = PI.with(|v| -> Result<BigFloatNumber, Error> {
//!     v.borrow_mut().for_prec(1024, rm)
//! }).unwrap();
//! 
//! // Compare computed constant with library's constant
//! assert!(pi.sub(&pi_lib, rm).unwrap().abs().unwrap().cmp(&epsilon) <= 0);
//! 
//! // Print computed result as decimal number.
//! let s = pi.format(Radix::Dec, rm).unwrap();
//! println!("{}", s);
//! 
//! // output: 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458698858e+0
//! ```
//! 

#![deny(clippy::suspicious)]

mod defs;
mod mantissa;
mod num;
mod strop;
mod parser;
mod ops;
mod common;
mod conv;

pub use crate::num::BigFloatNumber;
pub use crate::defs::Sign;
pub use crate::defs::Error;
pub use crate::defs::Exponent;
pub use crate::defs::Word;
pub use crate::defs::Radix;
pub use crate::defs::RoundingMode;
pub use crate::ops::consts::std::PI;
pub use crate::ops::consts::std::E;
pub use crate::ops::consts::std::LN_2;
pub use crate::ops::consts::std::LN_10;


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_bigfloat() {

        // Rounding of all operations
        let rm = RoundingMode::ToEven;

        // Compute pi: pi = 6*arctan(1/sqrt(3))
        let six = BigFloatNumber::from_word(6, 1).unwrap();
        let three = BigFloatNumber::parse("3.0", Radix::Dec, 1024+8, rm).unwrap();
        let mut pi = six.mul(&three.sqrt(rm).unwrap().reciprocal(rm).unwrap().atan(rm).unwrap(), rm).unwrap();
        pi.set_precision(1024, rm).unwrap();
        let mut epsilon = BigFloatNumber::from_word(1, 1).unwrap();
        epsilon.set_exponent(-1021);

        // Use library's constant for verifying the result
        let pi_lib = PI.with(|v| -> Result<BigFloatNumber, Error> {
            v.borrow_mut().for_prec(1024, rm)
        }).unwrap();

        // Compare computed constant with library's constant
        assert!(pi.sub(&pi_lib, rm).unwrap().abs().unwrap().cmp(&epsilon) <= 0);
    }
}