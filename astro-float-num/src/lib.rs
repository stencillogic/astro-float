//! Astro-float (astronomically large floating point numbers) is a library that implements arbitrary precision floating point numbers.
//!
//! See main crate [docs](https://docs.rs/astro-float/latest/astro_float/).

#![cfg_attr(not(feature = "std"), no_std)]

#![deny(missing_docs)]
#![deny(clippy::suspicious)]

#![allow(clippy::comparison_chain)]
#![allow(clippy::should_implement_trait)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::collapsible_if)]
#![allow(clippy::module_inception)]


#[cfg(not(feature = "std"))]
extern crate alloc;

mod common;
mod conv;
pub mod ctx;
mod defs;
mod ext;
mod mantissa;
mod num;
mod ops;
mod parser;
mod strop;

#[cfg(feature = "std")]
mod for_3rd;

#[doc(hidden)]
pub mod macro_util;

pub use crate::defs::Error;
pub use crate::defs::Exponent;
pub use crate::defs::Radix;
pub use crate::defs::RoundingMode;
pub use crate::defs::Sign;
pub use crate::defs::Word;
pub use crate::ext::BigFloat;
pub use crate::ext::FromExt;
pub use crate::ext::INF_NEG;
pub use crate::ext::INF_POS;
pub use crate::ext::NAN;
pub use crate::ops::consts::Consts;

pub use crate::defs::EXPONENT_BIT_SIZE;
pub use crate::defs::EXPONENT_MAX;
pub use crate::defs::EXPONENT_MIN;
pub use crate::defs::WORD_BASE;
pub use crate::defs::WORD_BIT_SIZE;
pub use crate::defs::WORD_MAX;
pub use crate::defs::WORD_SIGNIFICANT_BIT;

#[cfg(test)]
mod tests {

    #[test]
    fn test_bigfloat() {
        use crate::BigFloat;
        use crate::Consts;
        use crate::RoundingMode;

        // Precision with some space for error.
        let p = 1024 + 8;

        // Rounding of all operations
        let rm = RoundingMode::ToEven;

        // Initialize mathematical constants cache
        let mut cc = Consts::new().expect("An error occured when initializing constants");

        // Compute pi: pi = 6*arctan(1/sqrt(3))
        let six = BigFloat::from_word(6, 1);
        let three = BigFloat::from_word(3, p);

        let n = three.sqrt(p, rm);
        let n = n.reciprocal(p, rm);
        let n = n.atan(p, rm, &mut cc);
        let mut pi = six.mul(&n, p, rm);

        // Reduce precision to 1024
        pi.set_precision(1024, rm).expect("Precision updated");

        // Use library's constant for verifying the result
        let pi_lib = cc.pi_num(1024, rm).unwrap().into();

        // Compare computed constant with library's constant
        assert_eq!(pi.cmp(&pi_lib), Some(0));

        // Print using decimal radix.
        //println!("{}", pi);
    }
}
