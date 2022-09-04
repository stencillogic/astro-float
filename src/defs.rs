///! Definitions.

/// A word.
pub type Word = u32;

/// An exponent.
pub type Exponent = i32;

/// Doubled word.
pub type DoubleWord = u64;

/// Word with sign.
pub type SignedWord = i64;


/// Maximum exponent value.
pub const EXPONENT_MAX: Exponent = Exponent::MAX;

/// Minimum exponent value.
pub const EXPONENT_MIN: Exponent = Exponent::MIN;


/// Maximum value of a word.
pub const WORD_MAX: Word = Word::MAX;

/// Base of words.
pub const WORD_BASE: DoubleWord = WORD_MAX as DoubleWord + 1;

/// Size of a word in bits.
pub const WORD_BIT_SIZE: usize = std::mem::size_of::<Word>() * 8;

// word with the most significant bit set.
pub const WORD_SIGNIFICANT_BIT: Word = WORD_MAX << (WORD_BIT_SIZE - 1);

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

use smallvec::CollectionAllocErr;

/// Possible errors.
#[derive(Debug)]
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
    MemoryAllocation(CollectionAllocErr),
}


impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::ExponentOverflow(l0), Self::ExponentOverflow(r0)) => l0 == r0,
            (Self::MemoryAllocation(l0), Self::MemoryAllocation(r0)) => {
                core::mem::discriminant(l0) == core::mem::discriminant(r0)
            },
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
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
    
    /// None
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
