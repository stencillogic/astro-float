//! Definitions.

use core::fmt::Display;

#[cfg(feature = "std")]
use std::collections::TryReserveError;

#[cfg(not(feature = "std"))]
use alloc::collections::TryReserveError;

/// A word.
#[cfg(not(target_arch = "x86"))]
pub type Word = u64;

/// Doubled word.
#[cfg(not(target_arch = "x86"))]
pub type DoubleWord = u128;

/// Word with sign.
#[cfg(not(target_arch = "x86"))]
pub type SignedWord = i128;

/// A word.
#[cfg(target_arch = "x86")]
pub type Word = u32;

/// Doubled word.
#[cfg(target_arch = "x86")]
pub type DoubleWord = u64;

/// Word with sign.
#[cfg(target_arch = "x86")]
pub type SignedWord = i64;

/// An exponent.
pub type Exponent = i32;

/// Maximum exponent value.
#[cfg(not(target_arch = "x86"))]
pub const EXPONENT_MAX: Exponent = Exponent::MAX;

/// Maximum exponent value.
#[cfg(target_arch = "x86")]
pub const EXPONENT_MAX: Exponent = Exponent::MAX / 4;

/// Minimum exponent value.
#[cfg(not(target_arch = "x86"))]
pub const EXPONENT_MIN: Exponent = Exponent::MIN;

/// Minimum exponent value.
#[cfg(target_arch = "x86")]
pub const EXPONENT_MIN: Exponent = Exponent::MIN / 4;

/// Maximum value of a word.
pub const WORD_MAX: Word = Word::MAX;

/// Base of words.
pub const WORD_BASE: DoubleWord = WORD_MAX as DoubleWord + 1;

/// Size of a word in bits.
pub const WORD_BIT_SIZE: usize = core::mem::size_of::<Word>() * 8;

/// Word with the most significant bit set.
pub const WORD_SIGNIFICANT_BIT: Word = WORD_MAX << (WORD_BIT_SIZE - 1);

/// Default rounding mode.
pub const DEFAULT_RM: RoundingMode = RoundingMode::ToEven;

/// Default precision.
pub const DEFAULT_P: usize = 128;

/// The size of exponent type in bits.
pub const EXPONENT_BIT_SIZE: usize = core::mem::size_of::<Exponent>() * 8;

/// Sign.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub enum Sign {
    /// Negative.
    Neg = -1,

    /// Positive.
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

    /// Returns true if `self` is positive.
    pub fn is_positive(&self) -> bool {
        *self == Sign::Pos
    }

    /// Returns true if `self` is negative.
    pub fn is_negative(&self) -> bool {
        *self == Sign::Neg
    }

    /// Returns 1 for the positive sign and -1 for the negative sign.
    pub fn to_int(&self) -> i8 {
        *self as i8
    }
}

/// Possible errors.
#[derive(Debug, Clone, Copy)]
pub enum Error {
    /// The exponent value becomes greater than the upper limit of the range of exponent values.
    ExponentOverflow(Sign),

    /// Divizor is zero.
    DivisionByZero,

    /// Invalid argument.
    InvalidArgument,

    /// Memory allocation error.
    MemoryAllocation,
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let repr = match self {
            Error::ExponentOverflow(s) => {
                if s.is_positive() {
                    "positive overflow"
                } else {
                    "negative overflow"
                }
            }
            Error::DivisionByZero => "division by zero",
            Error::InvalidArgument => "invalid argument",
            Error::MemoryAllocation => "memory allocation failure",
        };
        f.write_str(repr)
    }
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::ExponentOverflow(l0), Self::ExponentOverflow(r0)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl From<TryReserveError> for Error {
    fn from(_: TryReserveError) -> Self {
        Error::MemoryAllocation
    }
}

/// Radix.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Radix {
    /// Binary.
    Bin = 2,

    /// Octal.
    Oct = 8,

    /// Decimal.
    Dec = 10,

    /// Hexadecimal.
    Hex = 16,
}

/// Rounding modes.
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum RoundingMode {
    /// Skip rounding operation.
    None = 1,

    /// Round half toward positive infinity.
    Up = 2,

    /// Round half toward negative infinity.
    Down = 4,

    /// Round half toward zero.
    ToZero = 8,

    /// Round half away from zero.
    FromZero = 16,

    /// Round half to even.
    ToEven = 32,

    /// Round half to odd.
    ToOdd = 64,
}
