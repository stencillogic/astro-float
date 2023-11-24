mod e;
mod ln10;
mod ln2;
mod pi;

use crate::common::buf::WordBuf;
use crate::common::util::round_p;
use crate::mantissa::Mantissa;
use crate::num::BigFloatNumber;
use crate::ops::consts::e::ECache;
use crate::ops::consts::ln10::Ln10Cache;
use crate::ops::consts::ln2::Ln2Cache;
use crate::ops::consts::pi::PiCache;
use crate::BigFloat;
use crate::Error;
use crate::RoundingMode;

/// Constants cache contains arbitrary-precision mathematical constants.
#[derive(Debug)]
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
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    pub(crate) fn pi_num(&mut self, p: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        let p = round_p(p);
        self.pi.for_prec(p, rm)
    }

    /// Returns the value of the Euler number with precision `p` using rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    pub(crate) fn e_num(&mut self, p: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        let p = round_p(p);
        self.e.for_prec(p, rm)
    }

    /// Returns the value of the natural logarithm of 2 with precision `p` using rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    pub(crate) fn ln_2_num(&mut self, p: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        let p = round_p(p);
        self.ln2.for_prec(p, rm)
    }

    /// Returns the value of the natural logarithm of 10 with precision `p` using rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    pub(crate) fn ln_10_num(
        &mut self,
        p: usize,
        rm: RoundingMode,
    ) -> Result<BigFloatNumber, Error> {
        let p = round_p(p);
        self.ln10.for_prec(p, rm)
    }

    /// Returns the value of the pi number with precision `p` using rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn pi(&mut self, p: usize, rm: RoundingMode) -> BigFloat {
        match self.pi_num(p, rm) {
            Ok(v) => v.into(),
            Err(e) => BigFloat::nan(Some(e)),
        }
    }

    /// Returns the value of the Euler number with precision `p` using rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn e(&mut self, p: usize, rm: RoundingMode) -> BigFloat {
        match self.e_num(p, rm) {
            Ok(v) => v.into(),
            Err(e) => BigFloat::nan(Some(e)),
        }
    }

    /// Returns the value of the natural logarithm of 2 with precision `p` using rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn ln_2(&mut self, p: usize, rm: RoundingMode) -> BigFloat {
        match self.ln_2_num(p, rm) {
            Ok(v) => v.into(),
            Err(e) => BigFloat::nan(Some(e)),
        }
    }

    /// Returns the value of the natural logarithm of 10 with precision `p` using rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn ln_10(&mut self, p: usize, rm: RoundingMode) -> BigFloat {
        match self.ln_10_num(p, rm) {
            Ok(v) => v.into(),
            Err(e) => BigFloat::nan(Some(e)),
        }
    }
}

/// Cache of powers of 10 for parsing and printing in decimal radix.
#[derive(Debug)]
pub struct TenPowers {
    tenpowers: Vec<(WordBuf, WordBuf, usize)>,
}

impl TenPowers {
    pub fn new() -> Self {
        TenPowers {
            tenpowers: Vec::new(),
        }
    }

    /// Return powers of 10: 100, 10000, 100000000, ...
    pub(crate) fn tenpowers(&mut self, p: usize) -> Result<&[(WordBuf, WordBuf, usize)], Error> {
        if p >= self.tenpowers.len() {
            Mantissa::compute_tenpowers(&mut self.tenpowers, p)?;
        }

        Ok(&self.tenpowers)
    }
}
