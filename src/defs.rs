///!  Definitions.

pub const DECIMAL_PARTS: usize = 10;

/// Number representation.
#[derive(Copy, Clone, Debug)]
pub struct BigFloat {
    pub (crate) sign: i8,                // sign
    pub (crate) e: i8,                   // exponent
    pub (crate) n: i16,                  // the number of decimal positions in the mantissa excluding leading zeroes
    pub (crate) m: [i16; DECIMAL_PARTS], // mantissa
}

/// Possible errors.
#[derive(Eq, PartialEq, Debug)]
pub enum Error {
    /// Exponent value becomes greater than the upper bound or smaller than the lower bound for exponent value.
    ExponentOverflow,   

    /// Divizor is zero.
    DivisionByZero,     

    /// Argument must not be a negative number.
    ArgumentIsNegative,

    /// Invalid argument.
    InvalidArgument,
}
