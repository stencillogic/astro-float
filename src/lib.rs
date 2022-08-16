#![deny(clippy::suspicious)]

mod defs;
mod mantissa;
mod num;
mod strop;
mod parser;
mod ops;
mod common;

pub use crate::num::BigFloatNumber;
pub use crate::defs::Sign;
pub use crate::defs::Exponent;
pub use crate::defs::Radix;
pub use crate::defs::RoundingMode;


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_bigfloat() {
    }
}