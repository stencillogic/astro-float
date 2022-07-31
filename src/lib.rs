#![deny(clippy::suspicious)]

mod defs;
mod mantissa;
mod num;
mod format;

pub use crate::num::BigFloatNumber;
pub use crate::defs::Sign;
pub use crate::defs::Exponent;


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_bigfloat() {
    }
}