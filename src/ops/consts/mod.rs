mod e;
mod ln10;
mod ln2;
mod pi;

use crate::ops::consts::e::ECache;
use crate::ops::consts::ln10::Ln10Cache;
use crate::ops::consts::ln2::Ln2Cache;
use crate::ops::consts::pi::PiCache;
use crate::BigFloatNumber;
use crate::Error;
use crate::RoundingMode;

/// Constants cache contains arbitrary-precision mathematical constants.
pub struct Consts {
    pi: PiCache,
    e: ECache,
    ln2: Ln2Cache,
    ln10: Ln10Cache,
}

/// In an ideal situation, the `Consts` structure is initialized with `Consts::new` only once,
/// and then used where needed.
impl Consts {
    /// Initializes the constants cache.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn new() -> Result<Self, Error> {
        Ok(Consts {
            pi: PiCache::new()?,
            e: ECache::new()?,
            ln2: Ln2Cache::new()?,
            ln10: Ln10Cache::new()?,
        })
    }

    /// Returns the value of the pi number with precision `p` using rounding mode `rm`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: precision is incorrect.
    pub fn pi(&mut self, p: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        self.pi.for_prec(p, rm)
    }

    /// Returns the value of the Euler number with precision `p` using rounding mode `rm`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: precision is incorrect.
    pub fn e(&mut self, p: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        self.e.for_prec(p, rm)
    }

    /// Returns the value of the natural logarithm of 2 with precision `p` using rounding mode `rm`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: precision is incorrect.
    pub fn ln_2(&mut self, p: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        self.ln2.for_prec(p, rm)
    }

    /// Returns the value of the natural logarithm of 10 with precision `p` using rounding mode `rm`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: precision is incorrect.
    pub fn ln_10(&mut self, p: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        self.ln10.for_prec(p, rm)
    }
}
