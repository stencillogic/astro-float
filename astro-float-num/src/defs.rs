//! Definitions.

use core::fmt::Display;

#[cfg(feature = "std")]
use std::collections::TryReserveError;

#[cfg(not(feature = "std"))]
use alloc::collections::TryReserveError;

#[cfg(feature = "rkyv")]
use rkyv::{Archive, Serialize, Deserialize};

/// A word.
#[cfg(not(target_pointer_width = "32"))]
pub type Word = u64;

/// Doubled word.
#[cfg(not(target_pointer_width = "32"))]
pub type DoubleWord = u128;

/// Word with sign.
#[cfg(not(target_pointer_width = "32"))]
pub type SignedWord = i128;

/// A word.
#[cfg(target_pointer_width = "32")]
pub type Word = u32;

/// Doubled word.
#[cfg(target_pointer_width = "32")]
pub type DoubleWord = u64;

/// Word with sign.
#[cfg(target_pointer_width = "32")]
pub type SignedWord = i64;

/// An exponent.
pub type Exponent = i32;

/// Maximum exponent value.
#[cfg(not(target_pointer_width = "32"))]
pub const EXPONENT_MAX: Exponent = Exponent::MAX;

/// Maximum exponent value.
#[cfg(target_pointer_width = "32")]
pub const EXPONENT_MAX: Exponent = Exponent::MAX / 4;

/// Minimum exponent value.
#[cfg(not(target_pointer_width = "32"))]
pub const EXPONENT_MIN: Exponent = Exponent::MIN;

/// Minimum exponent value.
#[cfg(target_pointer_width = "32")]
pub const EXPONENT_MIN: Exponent = Exponent::MIN / 4;

/// Maximum value of a word.
pub const WORD_MAX: Word = Word::MAX;

/// Base of words.
pub const WORD_BASE: DoubleWord = WORD_MAX as DoubleWord + 1;

/// Size of a word in bits.
pub const WORD_BIT_SIZE: usize = core::mem::size_of::<Word>() * 8;

/// Word with the most significant bit set.
pub const WORD_SIGNIFICANT_BIT: Word = WORD_MAX << (WORD_BIT_SIZE - 1);

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

#[cfg(feature = "rkyv")]
mod rkyv_impl {
  use super::Sign;
  use rkyv::{
    bytecheck::{CheckBytes, InvalidEnumDiscriminantError, Verify},
    primitive::ArchivedI16,
    rancor::{fail, Fallible, Source},
    traits::NoUndef,
    Archive, Deserialize, Place, Portable, Serialize,
  };
  // Hand-written archived enum
  #[derive(CheckBytes, Portable)]
  #[bytecheck(crate = rkyv::bytecheck, verify)]
  #[repr(C)]
  pub struct ArchivedSign(ArchivedI16);

  // Implementation detail: `ArchivedMyEnum` has no undef bytes
  unsafe impl NoUndef for ArchivedSign {}

  impl ArchivedSign {
      // Internal fallible conversion back to the original enum
      fn try_to_native(&self) -> Option<Sign> {
          Some(match self.0.to_native() {
              -1 => Sign::Neg,
              1 => Sign::Pos,
              _ => return None,
          })
      }

      // Public infallible conversion back to the original enum
      pub fn to_native(&self) -> Sign {
          unsafe { self.try_to_native().unwrap_unchecked() }
      }
  }

  unsafe impl<C: Fallible + ?Sized> Verify<C> for ArchivedSign
  where
      C::Error: Source,
  {
      // verify runs after all of the fields have been checked
      fn verify(&self, _: &mut C) -> Result<(), C::Error> {
          // Use the internal conversion to try to convert back
          if self.try_to_native().is_none() {
              // Return an error if it fails (i.e. the discriminant did not match
              // any valid discriminants)
              fail!(InvalidEnumDiscriminantError {
                  enum_name: "ArchivedSign",
                  invalid_discriminant: self.0.to_native(),
              })
          }
          Ok(())
      }
  }

  impl Archive for Sign {
      type Archived = ArchivedSign;
      type Resolver = ();

      fn resolve(&self, _: Self::Resolver, out: Place<Self::Archived>) {
          // Convert Sign -> i16 -> ArchivedI16 and write to `out`
          out.write(ArchivedSign((*self as i16).into()));
      }
  }

  // Serialization is a no-op because there's no out-of-line data
  impl<S: Fallible + ?Sized> Serialize<S> for Sign {
      fn serialize(&self, _: &mut S) -> Result<Self::Resolver, <S as Fallible>::Error> {
          Ok(())
      }
  }

  // Deserialization just calls the public conversion and returns the result
  impl<D: Fallible + ?Sized> Deserialize<Sign, D> for ArchivedSign {
      fn deserialize(&self, _: &mut D) -> Result<Sign, <D as Fallible>::Error> {
          Ok(self.to_native())
      }
  }
}
#[cfg(feature = "rkyv")]
pub use rkyv_impl::*;

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
#[cfg_attr(feature = "rkyv", derive(Archive, Serialize, Deserialize))]
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
