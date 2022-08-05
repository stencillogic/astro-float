///! Definitions.

/// A digit.
pub type Digit = u16;

/// An exponent.
pub type Exponent = i16;

/// Doubled digit.
pub type DoubleDigit = u32;

/// Digit with sign.
pub type DigitSigned = i32;


/// Maximum exponent value.
pub const EXPONENT_MAX: Exponent = Exponent::MAX;

/// Minimum exponent value.
pub const EXPONENT_MIN: Exponent = Exponent::MIN;


/// Maximum value of a "digit".
pub const DIGIT_MAX: Digit = Digit::MAX;

/// Base of digits.
pub const DIGIT_BASE: DoubleDigit = DIGIT_MAX as DoubleDigit + 1;

/// Size of a "digit" in bits.
pub const DIGIT_BIT_SIZE: usize = std::mem::size_of::<Digit>() * 8;

// Digit with the most significant bit set.
pub const DIGIT_SIGNIFICANT_BIT: Digit = DIGIT_MAX << (DIGIT_BIT_SIZE - 1);

/// Sign.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Sign {
    Neg = -1,
    Pos = 1,
}

impl Sign {
    /// Changes the sign to the opposite.
    pub fn invert(&self) -> Self {
        match *self {
            Sign::Pos => Sign::Neg,
            Sign::Neg => Sign::Pos,
        }
    }
}

use std::collections::TryReserveError;

/// Possible errors.
#[derive(Eq, PartialEq, Debug)]
pub enum Error {
    /// Exponent value becomes greater than the upper bound for exponent value.
    ExponentOverflow(Sign),

    /// Divizor is zero.
    DivisionByZero,

    /// Invalid argument.
    InvalidArgument,

    /// Allocation size is incorrect.
    IncorrectAllocationSize,

    /// Memory allocation error.
    MemoryAllocation(TryReserveError),
}


/// Radix
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Radix {
    Bin = 2,
    Oct = 8,
    Dec = 10,
    Hex = 16,
}

/// Possible errors.
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum RoundingMode {
    /// Round half toward positive infinity.
    Up,

    /// Round half toward negative infinity.
    Down,

    /// Round half toward zero.
    ToZero,

    /// Round half away from zero.
    FromZero,

    /// Round half to even.
    ToEven,

    /// Round half to odd.
    ToOdd,
}
