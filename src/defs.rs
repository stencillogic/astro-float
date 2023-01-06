//! Definitions.

/// A word.
#[cfg(target_arch = "x86_64")]
pub type Word = u64;

/// Doubled word.
#[cfg(target_arch = "x86_64")]
pub type DoubleWord = u128;

/// Word with sign.
#[cfg(target_arch = "x86_64")]
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
pub const EXPONENT_MAX: Exponent = Exponent::MAX;

/// Minimum exponent value.
pub const EXPONENT_MIN: Exponent = Exponent::MIN;

/// Maximum value of a word.
pub const WORD_MAX: Word = Word::MAX;

/// Base of words.
pub const WORD_BASE: DoubleWord = WORD_MAX as DoubleWord + 1;

/// Size of a word in bits. Precision is rounded according to word size.
pub const WORD_BIT_SIZE: usize = core::mem::size_of::<Word>() * 8;

/// Word with the most significant bit set.
pub const WORD_SIGNIFICANT_BIT: Word = WORD_MAX << (WORD_BIT_SIZE - 1);

/// Default rounding mode.
pub const DEFAULT_RM: RoundingMode = RoundingMode::ToEven;

/// Default precision.
pub const DEFAULT_P: usize = WORD_BIT_SIZE * 2;

/// Sign.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
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
    pub fn as_int(&self) -> i8 {
        *self as i8
    }
}

use smallvec::CollectionAllocErr;

/// Possible errors.
#[derive(Debug)]
pub enum Error {
    /// The exponent value becomes greater than the upper limit of the range of exponent values.
    ExponentOverflow(Sign),

    /// Divizor is zero.
    DivisionByZero,

    /// Invalid argument.
    InvalidArgument,

    /// Memory allocation error.
    MemoryAllocation(CollectionAllocErr),
}

impl Clone for Error {
    fn clone(&self) -> Self {
        match self {
            Self::ExponentOverflow(arg) => Self::ExponentOverflow(arg.clone()),
            Self::DivisionByZero => Self::DivisionByZero,
            Self::InvalidArgument => Self::InvalidArgument,
            Self::MemoryAllocation(arg) => Self::MemoryAllocation(match arg {
                CollectionAllocErr::CapacityOverflow => CollectionAllocErr::CapacityOverflow,
                CollectionAllocErr::AllocErr { layout } => {
                    CollectionAllocErr::AllocErr { layout: *layout }
                }
            }),
        }
    }
}

impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::ExponentOverflow(l0), Self::ExponentOverflow(r0)) => l0 == r0,
            (Self::MemoryAllocation(l0), Self::MemoryAllocation(r0)) => {
                core::mem::discriminant(l0) == core::mem::discriminant(r0)
            }
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
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
    None,

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
