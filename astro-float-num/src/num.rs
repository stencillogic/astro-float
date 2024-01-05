//! BigFloatNumber definition and basic arithmetic, comparison, and number manipulation operations.

use crate::common::consts::ONE;
use crate::common::util::count_leading_zeroes_skip_first;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::Exponent;
use crate::defs::RoundingMode;
use crate::defs::Sign;
use crate::defs::SignedWord;
use crate::defs::Word;
use crate::defs::EXPONENT_MAX;
use crate::defs::EXPONENT_MIN;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_SIGNIFICANT_BIT;
use crate::mantissa::Mantissa;

/// A finite floating point number with mantissa of an arbitrary size, an exponent, and the sign.
#[derive(Debug, Hash)]
pub(crate) struct BigFloatNumber {
    e: Exponent,
    s: Sign,
    m: Mantissa,
    inexact: bool,
}

impl BigFloatNumber {
    // Check the precision so it does not cause arithmetic overflows anywhere.
    pub(super) fn p_assertion(p: usize) -> Result<(), Error> {
        if p >= (isize::MAX / 2 + EXPONENT_MIN as isize) as usize {
            Err(Error::InvalidArgument)
        } else {
            Ok(())
        }
    }

    /// Returns a new number with value of 0 and precision of `p` bits. Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn new(p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::new(p)?,
            e: 0,
            s: Sign::Pos,
            inexact: false,
        })
    }

    /// Returns a new number with value of 0, precision of `p` bits, sign `s`, and marked as inexact if `inexact` is true.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn new2(p: usize, s: Sign, inexact: bool) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::new(p)?,
            e: 0,
            s,
            inexact,
        })
    }

    /// Returns the maximum value for the specified precision `p`: all bits of the mantissa are set to 1,
    /// the exponent has the maximum possible value, and the sign is positive.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn max_value(p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::oned_mantissa(p)?,
            e: EXPONENT_MAX,
            s: Sign::Pos,
            inexact: false,
        })
    }

    /// Returns the minimum value for the specified precision `p`: all bits of the mantissa are set to 1, the exponent has the maximum possible value, and the sign is negative. Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn min_value(p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::oned_mantissa(p)?,
            e: EXPONENT_MAX,
            s: Sign::Neg,
            inexact: false,
        })
    }

    /// Returns the minimum positive subnormal value for the specified precision `p`:
    /// only the least significant bit of the mantissa is set to 1, the exponent has
    /// the minimum possible value, and the sign is positive.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn min_positive(p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::min(p)?,
            e: EXPONENT_MIN,
            s: Sign::Pos,
            inexact: false,
        })
    }

    /// Returns the minimum positive normal value for the specified precision `p`:
    /// only the most significant bit of the mantissa is set to 1, the exponent has
    /// the minimum possible value, and the sign is positive.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn min_positive_normal(p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::from_word(p, WORD_SIGNIFICANT_BIT)?,
            e: EXPONENT_MIN,
            s: Sign::Pos,
            inexact: false,
        })
    }

    /// Returns a new number with value `d` and the precision `p`. Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn from_word(mut d: Word, p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;

        if d == 0 {
            Self::new(p)
        } else {
            let mut shift = 0;
            while d & WORD_SIGNIFICANT_BIT == 0 {
                d <<= 1;
                shift += 1;
            }
            Ok(BigFloatNumber {
                m: Mantissa::from_word(p, d)?,
                e: (WORD_BIT_SIZE - shift) as Exponent,
                s: Sign::Pos,
                inexact: false,
            })
        }
    }

    pub(crate) fn from_u64_internal(d: u64, p: usize) -> Result<Self, Error> {
        #[cfg(not(target_arch = "x86"))]
        {
            Self::from_word(d, p)
        }

        #[cfg(target_arch = "x86")]
        {
            Self::p_assertion(p)?;

            if d == 0 {
                Self::new(p)
            } else {
                let mut d = d;
                let mut shift = 0;
                while d < 0x8000000000000000u64 {
                    d <<= 1;
                    shift += 1;
                }
                let words = [d as Word, (d >> WORD_BIT_SIZE) as Word];
                if p < WORD_BIT_SIZE * 2 {
                    if words[0] != 0 {
                        return Err(Error::InvalidArgument);
                    } else {
                        Ok(BigFloatNumber {
                            m: Mantissa::from_word(p, words[1])?,
                            e: (64 - shift) as Exponent,
                            s: Sign::Pos,
                            inexact: false,
                        })
                    }
                } else {
                    Ok(BigFloatNumber {
                        m: Mantissa::from_words(p, &[d as Word, (d >> WORD_BIT_SIZE) as Word])?,
                        e: (64 - shift) as Exponent,
                        s: Sign::Pos,
                        inexact: false,
                    })
                }
            }
        }
    }

    /// Returns a copy of the number with the sign reversed.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn neg(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        ret.s = ret.s.invert();
        Ok(ret)
    }

    /// Adds `d2` to `self` and returns the result of the operation with precision `p` rounded according to `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    #[inline]
    pub fn add(&self, d2: &Self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        self.add_sub(d2, p, 1, rm, false)
    }

    /// Subtracts `d2` from `self` and returns the result of the operation with precision `p` rounded according to `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    #[inline]
    pub fn sub(&self, d2: &Self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        self.add_sub(d2, p, -1, rm, false)
    }

    /// Adds `d2` to `self` and returns the result of the operation.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer addition.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    #[inline]
    pub fn add_full_prec(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, 0, 1, RoundingMode::None, true)
    }

    /// Subtracts `d2` from `self` and returns the result of the operation.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer subtraction.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    #[inline]
    pub fn sub_full_prec(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, 0, -1, RoundingMode::None, true)
    }

    /// Multiplies `d2` by `self` and returns the result of the operation with precision `p` rounded according to `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    #[inline]
    pub fn mul(&self, d2: &Self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        self.mul_general_case(d2, p, rm, false)
    }

    /// Multiplies `d2` by `self` and returns the result of the operation.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer multiplication.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    #[inline]
    pub fn mul_full_prec(&self, d2: &Self) -> Result<Self, Error> {
        self.mul_general_case(d2, 0, RoundingMode::None, true)
    }

    fn mul_general_case(
        &self,
        d2: &Self,
        p: usize,
        rm: RoundingMode,
        full_prec: bool,
    ) -> Result<Self, Error> {
        let p = round_p(p);

        // TODO: consider short multiplication.

        Self::p_assertion(p)?;

        let s = if self.s == d2.s { Sign::Pos } else { Sign::Neg };

        if self.m.is_zero() || d2.m.is_zero() {
            let mut ret = Self::new(p)?;
            ret.set_sign(s);
            return Ok(ret);
        }

        let (e1, m1_opt) = self.normalize()?;
        let m1_normalized = m1_opt.as_ref().unwrap_or(&self.m);
        let (e2, m2_opt) = d2.normalize()?;
        let m2_normalized = m2_opt.as_ref().unwrap_or(&d2.m);

        let mut inexact = self.inexact || d2.inexact;

        let (e_shift, m3) = m1_normalized.mul(
            m2_normalized,
            p,
            rm,
            s == Sign::Pos,
            full_prec,
            &mut inexact,
        )?;

        let e = e1 + e2 - e_shift;

        if e > EXPONENT_MAX as isize {
            return Err(Error::ExponentOverflow(s));
        }

        if e < EXPONENT_MIN as isize {
            let mut ret = BigFloatNumber {
                m: m3,
                s,
                e: EXPONENT_MIN,
                inexact,
            };

            ret.subnormalize(e, rm);

            Ok(ret)
        } else {
            Ok(BigFloatNumber {
                m: m3,
                s,
                e: e as Exponent,
                inexact,
            })
        }
    }

    /// Divides `self` by `d2` and returns the result of the operation with precision `p` rounded according to `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - DivisionByZero: `d2` is zero.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: both `self` and `d2` are zero or precision is incorrect.
    pub fn div(&self, d2: &Self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        if d2.m.is_zero() {
            return if self.is_zero() {
                Err(Error::InvalidArgument)
            } else {
                Err(Error::DivisionByZero)
            };
        }

        let p = round_p(p);
        Self::p_assertion(p)?;

        let s = if self.s == d2.s { Sign::Pos } else { Sign::Neg };

        if self.m.is_zero() {
            let mut ret = Self::new(p)?; // self / d2 = 0
            ret.set_sign(s);
            return Ok(ret);
        }

        let (e1, m1_opt) = self.normalize()?;
        let m1_normalized = m1_opt.as_ref().unwrap_or(&self.m);
        let (e2, m2_opt) = d2.normalize()?;
        let m2_normalized = m2_opt.as_ref().unwrap_or(&d2.m);

        let mut inexact = self.inexact || d2.inexact;

        let (e_shift, m3) =
            m1_normalized.div(m2_normalized, p, rm, s == Sign::Pos, &mut inexact)?;

        let e = e1 - e2 + e_shift;

        if e > EXPONENT_MAX as isize {
            return Err(Error::ExponentOverflow(s));
        }

        if e < EXPONENT_MIN as isize {
            let mut ret = BigFloatNumber {
                m: m3,
                s,
                e: EXPONENT_MIN,
                inexact,
            };

            ret.subnormalize(e, rm);

            Ok(ret)
        } else {
            Ok(BigFloatNumber {
                m: m3,
                s,
                e: e as Exponent,
                inexact,
            })
        }
    }

    /// Returns the remainder of division of `|self|` by `|d2|`. The sign of the result is set to the sign of `self`.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: `d2` is zero.
    pub fn rem(&self, d2: &Self) -> Result<Self, Error> {
        if d2.m.is_zero() {
            return Err(Error::InvalidArgument);
        }

        if self.m.is_zero() {
            return self.clone();
        }

        // represent as mN * 2 ^ eNeff
        let e1eff = self.e as isize - self.m.max_bit_len() as isize;

        let (e, m2_opt) = d2.normalize()?;
        let m2_normalized = m2_opt.as_ref().unwrap_or(&d2.m);
        let e2eff = e - m2_normalized.max_bit_len() as isize;

        let finalize = |mut m3: Mantissa, mut e: isize| -> Result<BigFloatNumber, Error> {
            let (m3, e) = if m3.bit_len() > 0 {
                if e > EXPONENT_MAX as isize {
                    return Err(Error::ExponentOverflow(self.s));
                }

                if e < EXPONENT_MIN as isize {
                    // first, see if m3 is already subnormal, then shift accordingly
                    let mut excess = m3.max_bit_len() - m3.bit_len();

                    if EXPONENT_MIN as isize - e > usize::MAX as isize {
                        m3.set_zero();
                        e = 0;
                    } else {
                        let shift = (EXPONENT_MIN as isize - e) as usize;

                        if excess < shift {
                            m3.extend_subnormal(shift)?;
                            excess = m3.max_bit_len() - m3.bit_len();
                        }

                        let shift = excess - shift;
                        m3.shift_left(shift);
                        m3.set_bit_len(m3.bit_len() + shift);

                        e = EXPONENT_MIN as isize;
                    }
                } else {
                    m3.normilize2();
                }

                (m3, e)
            } else {
                (m3, 0)
            };

            let ret = BigFloatNumber {
                m: m3,
                s: self.s,
                e: e as Exponent,
                inexact: self.inexact || d2.inexact,
            };

            Ok(ret)
        };

        if e1eff > e2eff {
            // (m1 * 2^(e1eff - e2eff)) mod m2 = ((m1 mod m2) * ( 2^(e1eff - e2eff) mod m2 )) mod m2

            let mut two = Mantissa::from_raw_parts(&[2], 2)?;
            let powm = if (e1eff - e2eff) as usize >= m2_normalized.max_bit_len() {
                two.pow_mod((e1eff - e2eff) as usize, m2_normalized)?
            } else {
                two.pow2((e1eff - e2eff - 1) as usize)?;
                two // m3 still becomes 0 in rare case when two == m2_normalized
            };

            let m3 = self.m.rem(m2_normalized)?;

            let m3 = m3.mul_mod(&powm, m2_normalized)?;

            let e = e2eff + m3.bit_len() as isize;

            finalize(m3, e)
        } else if (self.m.bit_len() as isize + self.e as isize)
            < (m2_normalized.bit_len() as isize + e)
        {
            // self < d2, remainder = self
            self.clone()
        } else {
            // since self.e >= d2.e and e1eff <= e2eff, then e2eff - e1eff < m1.len()
            // (m1 * 2 ^ e1eff) mod (m2 * 2 ^ e2eff) = m1 mod (m2 * 2 ^ (e2eff - e1eff))

            let mut m2_normalized = if let Some(m2) = m2_opt { m2 } else { d2.m.clone()? };

            let e2eff = e - m2_normalized.max_bit_len() as isize;
            let ediff = (e2eff - e1eff) as usize;

            let m2l = m2_normalized.max_bit_len() + ediff;
            m2_normalized.set_length(m2l)?;

            let m3 = if m2_normalized.max_bit_len() > m2l {
                let mut m = self.m.clone()?;
                m.pow2(m2_normalized.max_bit_len() - m2l)?;
                m.rem(&m2_normalized)
            } else {
                self.m.rem(&m2_normalized)
            }?;

            let e =
                e1eff + m3.bit_len() as isize - m2_normalized.max_bit_len() as isize + m2l as isize;

            finalize(m3, e)
        }
    }

    // Return normilized mantissa and exponent with corresponding shift.
    pub(super) fn normalize(&self) -> Result<(isize, Option<Mantissa>), Error> {
        if self.is_subnormal() {
            let (shift, mantissa) = self.m.normilize()?;

            #[cfg(not(target_arch = "x86"))]
            {
                // checks for the case when usize is larger than exponent
                debug_assert!((shift as isize) < (isize::MAX / 2 + EXPONENT_MIN as isize));

                if (self.e as isize) - shift as isize <= isize::MIN / 2 {
                    return Err(Error::ExponentOverflow(self.s));
                }
            }

            Ok((self.e as isize - shift as isize, Some(mantissa)))
        } else {
            Ok((self.e as isize, None))
        }
    }

    // Normalize mantissa and return exponent shift of `self`.
    pub(crate) fn normalize2(&mut self) -> usize {
        self.m.normilize2()
    }

    // Combined add and sub operations.
    fn add_sub(
        &self,
        d2: &Self,
        p: usize,
        op: i8,
        rm: RoundingMode,
        full_prec: bool,
    ) -> Result<Self, Error> {
        let p = round_p(p);
        Self::p_assertion(p)?;

        let mut d3 = Self::new(0)?;

        // one of the args is zero
        if self.m.is_zero() {
            let mut ret = if op < 0 { d2.neg() } else { d2.clone() }?;

            ret.set_precision(p, rm)?;

            return Ok(ret);
        }

        if d2.m.is_zero() {
            let mut ret = self.clone()?;

            ret.set_precision(p, rm)?;

            return Ok(ret);
        }

        let (e1, m1_opt) = self.normalize()?;
        let m1 = m1_opt.as_ref().unwrap_or(&self.m);
        let (e2, m2_opt) = d2.normalize()?;
        let m2 = m2_opt.as_ref().unwrap_or(&d2.m);

        let mut inexact = self.inexact || d2.inexact;

        let mut e;
        let (shift, m3) = if (self.s != d2.s && op >= 0) || (op < 0 && self.s == d2.s) {
            // subtract
            let cmp = self.abs_cmp(d2);
            if cmp > 0 {
                d3.s = self.s;
                e = e1;
                m1.abs_sub(
                    m2,
                    p,
                    (e1 - e2) as usize,
                    rm,
                    d3.is_positive(),
                    full_prec,
                    &mut inexact,
                )
            } else if cmp < 0 {
                d3.s = if op >= 0 { d2.s } else { d2.s.invert() };
                e = e2;
                m2.abs_sub(
                    m1,
                    p,
                    (e2 - e1) as usize,
                    rm,
                    d3.is_positive(),
                    full_prec,
                    &mut inexact,
                )
            } else {
                let mut ret = Self::new(p)?;
                ret.inexact = inexact;
                return Ok(ret);
            }
        } else {
            // add
            d3.s = self.s;
            if e1 >= e2 {
                e = e1;
                m1.abs_add(
                    m2,
                    p,
                    (e1 - e2) as usize,
                    rm,
                    d3.is_positive(),
                    full_prec,
                    &mut inexact,
                )
            } else {
                e = e2;
                m2.abs_add(
                    m1,
                    p,
                    (e2 - e1) as usize,
                    rm,
                    d3.is_positive(),
                    full_prec,
                    &mut inexact,
                )
            }
        }?;

        d3.inexact |= inexact;

        #[cfg(not(target_arch = "x86"))]
        {
            debug_assert!(shift <= isize::MAX / 2 && e >= isize::MIN / 2);
        }
        e -= shift;

        if e > EXPONENT_MAX as isize {
            return Err(Error::ExponentOverflow(d3.s));
        }

        d3.m = m3;

        if e < EXPONENT_MIN as isize {
            d3.e = EXPONENT_MIN;
            d3.subnormalize(e, rm);
        } else {
            d3.e = e as Exponent;
        }

        Ok(d3)
    }

    /// Make `self` subnormal
    pub(crate) fn subnormalize(&mut self, e: isize, rm: RoundingMode) {
        debug_assert_eq!(self.exponent(), EXPONENT_MIN);
        debug_assert!(!self.is_subnormal());

        if self.is_zero() {
            return;
        }

        let is_positive = self.is_positive();

        if (self.m.max_bit_len() as isize) + e > EXPONENT_MIN as isize {
            // subnormal

            let mut shift = (EXPONENT_MIN as isize - e) as usize;

            let mut inexact = self.inexact;

            if self.m.round_mantissa(
                shift,
                rm,
                is_positive,
                &mut false,
                self.m.max_bit_len(),
                &mut inexact,
            ) {
                shift -= 1;
            }

            self.inexact |= inexact;

            if shift > 0 {
                self.m.shift_right(shift);
                self.m.update_bit_len();
            }
        } else if rm == RoundingMode::FromZero
            || (is_positive && rm == RoundingMode::Up)
            || (!is_positive && rm == RoundingMode::Down)
        {
            // non zero for directed rounding modes
            self.m.set_zero();
            self.m.digits_mut()[0] = 1;
            self.m.set_bit_len(1);
            self.inexact |= true;
        } else {
            self.m.set_zero();
            self.e = 0;
            self.inexact |= true;
        }
    }

    /// Compares `self` to `d2`.
    /// Returns positive if `self` is greater than `d2`, negative if `self` is smaller than `d2`, 0 otherwise.
    pub fn cmp(&self, d2: &Self) -> SignedWord {
        if self.is_zero() && d2.is_zero() {
            return 0;
        }

        if self.s != d2.s {
            return self.s as SignedWord;
        }

        self.abs_cmp(d2) * self.s as SignedWord
    }

    /// Compares the absolute value of `self` to the absolute value of `d2`.
    /// Returns positive if `|self|` is greater than `|d2|`, negative if `|self|` is smaller than `|d2|`, 0 otherwise.
    pub fn abs_cmp(&self, d2: &Self) -> SignedWord {
        if self.m.is_zero() {
            if d2.m.is_zero() {
                return 0;
            } else {
                return -1;
            }
        }

        let n1 = self.mantissa_max_bit_len() as isize - self.precision() as isize;

        let n2 = d2.mantissa_max_bit_len() as isize - d2.precision() as isize;

        let e: isize = self.e as isize - n1 - d2.e as isize + n2;
        if e > 0 {
            return 1;
        } else if e < 0 {
            return -1;
        }

        self.m.abs_cmp(&d2.m, n1 == n2)
    }

    /// Returns the absolute value of a number.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn abs(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        ret.s = Sign::Pos;
        Ok(ret)
    }

    /// Constructs a number with precision `p` from f64 value.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect or `f` is NaN.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: `f` is Inf.
    pub fn from_f64(p: usize, mut f: f64) -> Result<Self, Error> {
        Self::p_assertion(p)?;

        let mut ret = Self::new(0)?;

        if f == 0.0f64 {
            return Ok(ret);
        }

        if f.is_infinite() {
            return Err(Error::ExponentOverflow(if f.is_sign_negative() {
                Sign::Neg
            } else {
                Sign::Pos
            }));
        }

        if f.is_nan() {
            return Err(Error::InvalidArgument);
        }

        if f < 0.0f64 {
            ret.s = Sign::Neg;
            f = -f;
        }

        let u = f.to_bits();
        let mut mantissa = u << 12;
        let mut exponent: Exponent = (u >> 52) as Exponent & 0b11111111111;

        if exponent != 0 {
            mantissa >>= 1;
            mantissa |= 0x8000000000000000u64;
            exponent += 1;
        }

        let (shift, m) = Mantissa::from_u64(p, mantissa)?;

        ret.m = m;
        ret.e = exponent - 0b1111111111 - shift as Exponent;

        #[cfg(target_arch = "x86")]
        debug_assert!(ret.e <= EXPONENT_MAX && ret.e >= EXPONENT_MIN);

        Ok(ret)
    }

    /// Converts a number to f64 value.
    /// Conversion rounds `self` to zero.
    #[cfg(test)]
    pub(crate) fn to_f64(&self) -> f64 {
        if self.m.is_zero() {
            return 0.0;
        }

        let mantissa = self.m.to_u64();
        let mut e: isize = self.e as isize + 0b1111111111;
        let mut ret = 0;

        if e >= 0b11111111111 {
            match self.s {
                Sign::Pos => f64::INFINITY,
                Sign::Neg => f64::NEG_INFINITY,
            }
        } else if e <= 0 {
            let shift = -e;
            if shift < 52 {
                ret |= mantissa >> (shift + 12);
                if self.s == Sign::Neg {
                    ret |= 0x8000000000000000u64;
                }
                f64::from_bits(ret)
            } else {
                0.0
            }
        } else {
            let mantissa = mantissa << 1;
            e -= 1;
            if self.s == Sign::Neg {
                ret |= 1;
            }
            ret <<= 11;
            ret |= e as u64;
            ret <<= 52;
            ret |= mantissa >> 12;
            f64::from_bits(ret)
        }
    }

    /// Returns true if `self` is subnormal. A number is subnormal if the most significant bit of the mantissa is not equal to 1.
    #[inline]
    pub fn is_subnormal(&self) -> bool {
        self.m.is_subnormal()
    }

    /// Decomposes `self` into raw parts.
    /// The function returns a reference to a slice of words representing mantissa,
    /// numbers of significant bits in the mantissa,
    /// sign, exponent, and a bool value which specify whether the number is inexact.
    #[inline]
    pub fn as_raw_parts(&self) -> (&[Word], usize, Sign, Exponent, bool) {
        let (m, n) = self.m.as_raw_parts();
        (m, n, self.s, self.e, self.inexact)
    }

    /// Consumes `self` and decomposes into raw parts.
    /// The function returns mantissa,
    /// sign, exponent, and a bool value which specify whether the number is inexact.
    #[inline]
    pub fn into_raw_parts(self) -> (Mantissa, Sign, Exponent, bool) {
        (self.m, self.s, self.e, self.inexact)
    }

    /// Constructs a number from the raw parts:
    ///
    ///  - `m` is the mantissa.
    ///  - `n` is the number of significant bits in mantissa.
    ///  - `s` is the sign.
    ///  - `e` is the exponent.
    ///  - `inexact` specify whether number is inexact.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: `n` is larger than the number of bits in `m`;
    /// `n` is smaller than the number of bits in `m`, but `m` does not represent corresponding subnormal number mantissa;
    /// `n` is smaller than the number of bits in `m`, but `e` is not the minimum possible exponent;
    /// `n` or the size of `m` is too large (larger than isize::MAX / 2 + EXPONENT_MIN);
    /// `e` is less than EXPONENT_MIN or greater than EXPONENT_MAX.
    pub fn from_raw_parts(
        m: &[Word],
        n: usize,
        s: Sign,
        mut e: Exponent,
        inexact: bool,
    ) -> Result<Self, Error> {
        let p = m.len() * WORD_BIT_SIZE;
        Self::p_assertion(p)?;

        #[cfg(target_arch = "x86")]
        if e < EXPONENT_MIN || e > EXPONENT_MAX {
            return Err(Error::InvalidArgument);
        }

        if n > p {
            Err(Error::InvalidArgument)
        } else {
            let m = Mantissa::from_words(p, m)?;

            if m.bit_len() != n {
                return Err(Error::InvalidArgument);
            }

            if n > 0 && n < p && e > EXPONENT_MIN {
                return Err(Error::InvalidArgument);
            }

            if n == 0 {
                e = 0;
            }

            Ok(BigFloatNumber { e, s, m, inexact })
        }
    }

    /// Build BigFloatNumber from raw parts unchecked.
    pub(super) fn from_raw_unchecked(m: Mantissa, s: Sign, e: Exponent, inexact: bool) -> Self {
        BigFloatNumber { e, s, m, inexact }
    }

    /// Constructs a number from the slice of words:
    ///
    ///  - `m` is the mantissa.
    ///  - `s` is the sign.
    ///  - `e` is the exponent.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: size of `m` is larger than isize::MAX / 2 + EXPONENT_MIN or
    /// when `e` is less than EXPONENT_MIN or greater than EXPONENT_MAX.
    pub fn from_words(m: &[Word], s: Sign, mut e: Exponent) -> Result<Self, Error> {
        let p = m.len() * WORD_BIT_SIZE;
        Self::p_assertion(p)?;

        #[cfg(target_arch = "x86")]
        if e < EXPONENT_MIN || e > EXPONENT_MAX {
            return Err(Error::InvalidArgument);
        }

        let mut m = Mantissa::from_words(p, m)?;
        let bl = m.bit_len();

        if m.is_zero() {
            e = 0;
        } else if bl < p {
            let mut shift = p - bl;
            if (e as isize) < EXPONENT_MIN as isize + shift as isize {
                shift = (e as isize - EXPONENT_MIN as isize) as usize;
                e = EXPONENT_MIN;
            } else {
                e -= shift as Exponent;
            }
            m.shift_left(shift);
            m.set_bit_len(bl + shift);
        }

        Ok(BigFloatNumber {
            e,
            s,
            m,
            inexact: false,
        })
    }

    /// Returns the sign of a number.
    #[inline]
    pub fn sign(&self) -> Sign {
        self.s
    }

    /// Returns true if `self` is positive.
    #[inline]
    pub fn is_positive(&self) -> bool {
        self.s == Sign::Pos
    }

    /// Returns true if `self` is negative.
    #[inline]
    pub fn is_negative(&self) -> bool {
        self.s == Sign::Neg
    }

    /// Returns the exponent of `self`.
    #[inline]
    pub fn exponent(&self) -> Exponent {
        self.e
    }

    /// Returns true if `self` is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.m.is_zero()
    }

    /// Returns the largest integer less than or equal to `self`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn floor(&self) -> Result<Self, Error> {
        let int = self.int()?;
        if self.is_negative() && !self.fract()?.m.is_zero() {
            return int.sub(&ONE, int.mantissa_max_bit_len(), RoundingMode::ToZero);
        }
        Ok(int)
    }

    /// Returns the smallest integer greater than or equal to `self`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn ceil(&self) -> Result<Self, Error> {
        let int = self.int()?;
        if self.is_positive() && !self.fract()?.m.is_zero() {
            return int.add(&ONE, int.mantissa_max_bit_len(), RoundingMode::ToZero);
        }
        Ok(int)
    }

    /// Returns fractional part of a number.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn fract(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        if self.e > 0 {
            if (self.e as usize) < self.m.max_bit_len() {
                // remove integer part of mantissa & normalize at the same time
                if let Some(shift) = self.m.find_one_from(self.e as usize) {
                    let mut e = self.e as isize - shift as isize;
                    if e < EXPONENT_MIN as isize {
                        let shift1 = (self.e as isize - EXPONENT_MIN as isize) as usize;
                        ret.m.shift_left(shift1);
                        ret.m.mask_bits(shift - shift1, true);
                        e = EXPONENT_MIN as isize;
                    } else {
                        ret.m.shift_left(shift);
                    }
                    ret.e = e as Exponent;
                } else {
                    ret.m.set_zero();
                    ret.e = 0;
                }
            } else {
                ret.m.set_zero();
                ret.e = 0;
            }
        }
        Ok(ret)
    }

    /// Returns integer part of a number.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn int(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;

        if self.e > 0 {
            if (self.e as usize) < self.m.max_bit_len() {
                ret.m
                    .mask_bits(self.m.max_bit_len() - self.e as usize, false)
            }
        } else {
            ret.m.set_zero();
            ret.e = 0;
        }

        Ok(ret)
    }

    /// Returns true if `self` is odd integer number.
    pub(crate) fn is_odd_int(&self) -> bool {
        if self.e > 0 {
            if (self.e as usize) <= self.m.max_bit_len() {
                self.m.is_odd_int(self.e as usize)
            } else {
                false
            }
        } else {
            self.is_zero()
        }
    }

    /// Returns true if `self` is an integer number.
    pub fn is_int(&self) -> bool {
        if self.e > 0 {
            if (self.e as usize) < self.m.max_bit_len() {
                self.m.find_one_from(self.e as usize).is_none()
            } else {
                true
            }
        } else {
            self.is_zero()
        }
    }

    /// Returns integer part of a number as built-in integer.
    pub(super) fn int_as_usize(&self) -> Result<usize, Error> {
        if self.e > 0 {
            debug_assert!(core::mem::size_of::<usize>() >= core::mem::size_of::<Word>());
            if (self.e as usize) <= WORD_BIT_SIZE {
                let shift = WORD_BIT_SIZE - self.e as usize;
                let ret = self.m.most_significant_word() as usize;
                Ok(ret >> shift)
            } else {
                Err(Error::InvalidArgument)
            }
        } else {
            Ok(0)
        }
    }

    /// Sets the exponent of `self`.
    /// Note that if `self` is subnormal, the exponent may not change, but the mantissa will shift instead.
    /// `e` will be clamped to the range from EXPONENT_MIN to EXPONENT_MAX if it's outside of the range.
    pub fn set_exponent(&mut self, e: Exponent) {
        #[cfg(target_arch = "x86")]
        let e = if e < EXPONENT_MIN {
            EXPONENT_MIN
        } else if e > EXPONENT_MAX {
            EXPONENT_MAX
        } else {
            e
        };

        if !self.is_zero() {
            if self.is_subnormal() && e > EXPONENT_MIN {
                let ediff = e as isize - EXPONENT_MIN as isize;

                let n = self.mantissa_max_bit_len() - self.precision();
                if n as isize >= ediff {
                    self.m.shift_left(ediff as usize);
                    self.m.set_bit_len(self.m.bit_len() + ediff as usize);
                } else {
                    self.m.shift_left(n);
                    self.m.set_bit_len(self.m.max_bit_len());
                    self.e = e - n as Exponent;
                }
            } else {
                self.e = e;
            }
        }
    }

    /// Returns the maximum mantissa length of `self` in bits regardless of whether `self` is normal or subnormal.
    #[inline]
    pub fn mantissa_max_bit_len(&self) -> usize {
        self.m.max_bit_len()
    }

    /// Returns the number of significant bits used in the mantissa. Normal numbers use all bits of the mantissa.
    /// Subnormal numbers use fewer bits than the mantissa can hold.
    #[inline]
    pub fn precision(&self) -> usize {
        self.m.bit_len()
    }

    /// Returns the rounded number with `n` binary positions in the fractional part of the number using rounding mode `rm`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: rounding causes exponent overflow.
    ///  - InvalidArgument: `n` is too large.
    pub fn round(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        if n >= (isize::MAX / 2) as usize {
            return Err(Error::InvalidArgument);
        }

        let mut ret = self.clone()?;

        let e = self.mantissa_max_bit_len() as isize - self.e as isize;

        if e > 0 && e as usize > n && !self.is_zero() {
            let m = e as usize - n;

            if m >= self.mantissa_max_bit_len() {
                let is_positive = self.is_positive();
                let msb_set = self.m.most_significant_word() & WORD_SIGNIFICANT_BIT != 0;

                ret.m.set_zero();

                if rm == RoundingMode::FromZero
                    || (is_positive && rm == RoundingMode::Up)
                    || (!is_positive && rm == RoundingMode::Down)
                    || (m == self.mantissa_max_bit_len()
                        && ((msb_set && rm == RoundingMode::ToOdd)
                            || (rm == RoundingMode::ToEven
                                && msb_set
                                && count_leading_zeroes_skip_first(self.mantissa().digits())
                                    != self.mantissa_max_bit_len())))
                {
                    // non zero for directed rounding modes,
                    // non zero for rounding to even/odd when msb of self is the rounding bit
                    *ret.m.digits_mut().last_mut().unwrap() = WORD_SIGNIFICANT_BIT;

                    let e = -(n as isize - 1);
                    if e < EXPONENT_MIN as isize {
                        ret.e = EXPONENT_MIN;
                        ret.subnormalize(e, rm);
                    } else {
                        ret.e = e as Exponent;
                    }
                } else {
                    ret.e = 0;
                }

                ret.inexact |= true; // self was not zero
            } else {
                let mut inexact = ret.inexact;

                let ovf = ret.m.round_mantissa(
                    m,
                    rm,
                    self.is_positive(),
                    &mut false,
                    ret.m.max_bit_len(),
                    &mut inexact,
                );

                ret.inexact |= inexact;

                if ovf {
                    if ret.e == EXPONENT_MAX {
                        return Err(Error::ExponentOverflow(ret.s));
                    }

                    ret.e += 1;
                } else if ret.m.is_all_zero() {
                    ret.m.set_bit_len(0);
                    ret.e = 0;
                } else if ret.m.is_subnormal() {
                    ret.m.update_bit_len();
                }
            }
        }

        Ok(ret)
    }

    #[cfg(feature = "random")]
    /// Returns a random normalized (not subnormal) BigFloat number with exponent in the range
    /// from `exp_from` to `exp_to` inclusive. The sign can be positive and negative. Zero is excluded.
    /// Precision is rounded upwards to the word size.
    /// Function does not follow any specific distribution law.
    /// The intended use of this function is for testing.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the precision is incorrect or when `exp_from` is less than EXPONENT_MIN or `exp_to` is greater than EXPONENT_MAX.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn random_normal(p: usize, exp_from: Exponent, exp_to: Exponent) -> Result<Self, Error> {
        Self::p_assertion(p)?;

        #[cfg(target_arch = "x86")]
        if exp_from < EXPONENT_MIN || exp_to > EXPONENT_MAX {
            return Err(Error::InvalidArgument);
        }

        let m = Mantissa::random_normal(p)?;
        let e = if exp_from < exp_to {
            (rand::random::<isize>().abs() % (exp_to as isize - exp_from as isize)
                + exp_from as isize) as Exponent
        } else {
            exp_from
        };
        let s = if rand::random::<u8>() & 1 == 0 { Sign::Pos } else { Sign::Neg };
        Ok(BigFloatNumber {
            e,
            s,
            m,
            inexact: false,
        })
    }

    /// Clones the number.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn clone(&self) -> Result<Self, Error> {
        Ok(BigFloatNumber {
            e: self.e,
            s: self.s,
            m: self.m.clone()?,
            inexact: self.inexact,
        })
    }

    /// Sets the precision of `self` to `p`.
    /// If the new precision is smaller than the existing one, the number is rounded using specified rounding mode `rm`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn set_precision(&mut self, p: usize, rm: RoundingMode) -> Result<(), Error> {
        self.set_precision_internal(p, rm, false, self.mantissa_max_bit_len())
            .map(|_| {})
    }

    /// Try to round and then set the precision to `p`, given `self` has `s` correct digits in mantissa.
    /// Returns true if rounding succeeded. If the fuction returns `false`, `self` is still modified, and should be discarded.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    pub(crate) fn try_set_precision(
        &mut self,
        p: usize,
        rm: RoundingMode,
        s: usize,
    ) -> Result<bool, Error> {
        self.set_precision_internal(p, rm, self.inexact(), s)
    }

    fn set_precision_internal(
        &mut self,
        p: usize,
        rm: RoundingMode,
        mut check_roundable: bool,
        s: usize,
    ) -> Result<bool, Error> {
        Self::p_assertion(p)?;

        if self.mantissa_max_bit_len() > p && p > 0 {
            let mut inexact = self.inexact;

            let ovf = self.m.round_mantissa(
                self.mantissa_max_bit_len() - p,
                rm,
                self.is_positive(),
                &mut check_roundable,
                s,
                &mut inexact,
            );

            self.inexact |= inexact;

            if check_roundable && self.inexact {
                return Ok(false);
            }

            if ovf {
                if self.e == EXPONENT_MAX {
                    return Err(Error::ExponentOverflow(self.s));
                }

                self.e += 1;
            } else if self.m.is_all_zero() {
                self.m.set_bit_len(0);
                self.e = 0;
            } else if self.is_subnormal() {
                self.m.update_bit_len();
            }
        } else if p == 0 {
            if self.is_zero() {
                if check_roundable && self.inexact {
                    return Ok(false);
                }
            } else {
                self.inexact |= true;
            }
        }

        self.m.set_length(p)?;

        Ok(true)
    }

    /// Computes the reciprocal of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - DivisionByZero: `self` is zero.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    pub fn reciprocal(&self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        ONE.div(self, p, rm)
    }

    /// Sets the sign of `self`.
    pub fn set_sign(&mut self, s: Sign) {
        self.s = s;
    }

    /// Inverts the sign of `self`.
    pub fn inv_sign(&mut self) {
        if self.is_negative() {
            self.set_sign(Sign::Pos);
        } else {
            self.set_sign(Sign::Neg);
        }
    }

    /// Create float from usize value.
    pub(crate) fn from_usize(u: usize) -> Result<Self, Error> {
        let (shift, m) = Mantissa::from_usize(u)?;
        let s = Sign::Pos;
        let e = (m.max_bit_len() - shift) as Exponent;

        Ok(BigFloatNumber {
            m,
            s,
            e,
            inexact: false,
        })
    }

    /// Returns the raw mantissa words of a number.
    pub fn mantissa_mut(&mut self) -> &mut Mantissa {
        &mut self.m
    }

    /// Returns the raw mantissa words of a number.
    pub fn mantissa(&self) -> &Mantissa {
        &self.m
    }

    /// Constructs BigFloatNumber with precision `p` from a signed integer value `i`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn from_i128(i: i128, p: usize) -> Result<Self, Error> {
        let sign = if i < 0 { Sign::Neg } else { Sign::Pos };
        let mut ret = Self::from_u128(i.unsigned_abs(), p)?;
        ret.set_sign(sign);
        Ok(ret)
    }

    /// Constructs BigFloatNumber with precision `p` from an unsigned integer value `u`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.        
    pub fn from_u128(mut v: u128, p: usize) -> Result<Self, Error> {
        const SZ: usize = core::mem::size_of::<u128>() * 8;

        if p < SZ {
            return Err(Error::InvalidArgument);
        }

        Self::p_assertion(p)?;

        if v == 0 {
            Self::new(p)
        } else {
            let mut shift = 0;
            while v <= (u128::MAX >> 1) {
                v <<= 1;
                shift += 1;
            }

            let mut words = [0; (SZ + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE];
            for w in &mut words {
                *w = v as Word;
                v >>= WORD_BIT_SIZE;
            }

            Ok(BigFloatNumber {
                m: Mantissa::from_words(p, &words)?,
                e: (SZ - shift) as Exponent,
                s: Sign::Pos,
                inexact: false,
            })
        }
    }

    // Add correction to x for flooring and ceiling rounding modes.
    pub(crate) fn add_correction(&self, inv_corr_sign: bool) -> Result<Self, Error> {
        let p = self.mantissa_max_bit_len() + 1;
        let mut corr = BigFloatNumber::min_positive(p)?;
        corr.set_exponent(self.exponent());
        corr.set_sign(if inv_corr_sign { self.sign().invert() } else { self.sign() });
        self.add(&corr, p, RoundingMode::None)
    }

    /// Divide `self` by 2.
    pub(crate) fn div_by_2(&mut self, rm: RoundingMode) {
        let e = self.exponent();
        if e == EXPONENT_MIN {
            self.subnormalize(e as isize - 1, rm);
        } else {
            self.set_exponent(e - 1);
        }
    }

    /// Returns true if self is `inexact`.
    #[inline]
    pub fn inexact(&self) -> bool {
        self.inexact
    }

    /// Marks self as inexact if `inexact` is true, or exact otherwise.
    #[inline]
    pub fn set_inexact(&mut self, inexact: bool) {
        self.inexact = inexact;
    }
}

macro_rules! impl_int_conv {
    ($s:ty, $u:ty, $from_s:ident, $from_u:ident) => {
        impl BigFloatNumber {
            /// Constructs BigFloatNumber with precision `p` from a signed integer value `i`.
            /// Precision is rounded upwards to the word size.
            ///
            /// ## Errors
            ///
            ///  - MemoryAllocation: failed to allocate memory for mantissa.
            ///  - InvalidArgument: the precision is incorrect.
            pub fn $from_s(i: $s, p: usize) -> Result<Self, Error> {
                let sign = if i < 0 { Sign::Neg } else { Sign::Pos };
                let mut ret = Self::$from_u(i.unsigned_abs(), p)?;
                ret.set_sign(sign);
                Ok(ret)
            }

            /// Constructs BigFloatNumber with precision `p` from an unsigned integer value `u`.
            /// Precision is rounded upwards to the word size.
            ///
            /// ## Errors
            ///
            ///  - MemoryAllocation: failed to allocate memory for mantissa.
            ///  - InvalidArgument: the precision is incorrect.
            pub fn $from_u(u: $u, p: usize) -> Result<Self, Error> {
                const SZ: usize = core::mem::size_of::<$u>() * 8;

                if p < SZ {
                    return Err(Error::InvalidArgument);
                }

                Self::from_u64_internal(u as u64, p)
            }
        }
    };
}

impl_int_conv!(i8, u8, from_i8, from_u8);
impl_int_conv!(i16, u16, from_i16, from_u16);
impl_int_conv!(i32, u32, from_i32, from_u32);
impl_int_conv!(i64, u64, from_i64, from_u64);

#[cfg(test)]
mod tests {

    use crate::{common::util::random_subnormal, defs::WORD_MAX, Consts};

    use super::*;
    use rand::random;

    #[cfg(not(feature = "std"))]
    use alloc::format;

    #[test]
    fn test_number() {
        let p_rng = 10;
        let p_min = 5;
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let rm = RoundingMode::ToEven;
        let mut cc = Consts::new().unwrap();

        let mut d1;
        let mut d2;
        let mut d3;
        let mut ref_num;
        let mut eps = ONE.clone().unwrap();

        // inf
        assert!(
            BigFloatNumber::from_f64(p, f64::INFINITY).unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        assert!(
            BigFloatNumber::from_f64(p, f64::NEG_INFINITY).unwrap_err()
                == Error::ExponentOverflow(Sign::Neg)
        );

        // cmp
        d1 = BigFloatNumber::from_raw_parts(
            &[1, WORD_MAX, WORD_SIGNIFICANT_BIT],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            123,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[1, WORD_SIGNIFICANT_BIT],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            123,
            false,
        )
        .unwrap();
        assert!(d1.cmp(&d1) == 0);
        assert!(d1.cmp(&d2) > 0);
        assert!(d2.cmp(&d1) < 0);
        d1.inv_sign();
        d2.inv_sign();
        assert!(d1.cmp(&d2) < 0);
        assert!(d2.cmp(&d1) > 0);
        d2.set_exponent(d2.exponent() + 1);
        assert!(d1.cmp(&d2) > 0);
        assert!(d2.cmp(&d1) < 0);
        d1.inv_sign();
        d2.inv_sign();
        assert!(d1.cmp(&d2) < 0);
        assert!(d2.cmp(&d1) > 0);

        d3 = d1.clone().unwrap();
        assert!(d3.cmp(&d1) == 0);
        d3.inv_sign();
        assert!(d3.cmp(&d1) < 0);

        // cmp subnormal
        d1 = BigFloatNumber::from_raw_parts(
            &[1, WORD_MAX, 1],
            WORD_BIT_SIZE * 2 + 1,
            Sign::Pos,
            EXPONENT_MIN,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX, 1, 2],
            WORD_BIT_SIZE * 2 + 2,
            Sign::Pos,
            EXPONENT_MIN,
            false,
        )
        .unwrap();
        assert!(d1.cmp(&d1) == 0);
        assert!(d1.cmp(&d2) < 0);
        assert!(d2.cmp(&d1) > 0);
        d1.inv_sign();
        d2.inv_sign();
        assert!(d1.cmp(&d2) > 0);
        assert!(d2.cmp(&d1) < 0);

        // abs cmp
        d1 = BigFloatNumber::from_raw_parts(
            &[2, WORD_SIGNIFICANT_BIT],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            123,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX, 1, WORD_SIGNIFICANT_BIT],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            123,
            false,
        )
        .unwrap();

        for (s1, s2) in [
            (Sign::Pos, Sign::Pos),
            (Sign::Pos, Sign::Neg),
            (Sign::Neg, Sign::Pos),
            (Sign::Neg, Sign::Neg),
        ] {
            d1.set_sign(s1);
            d2.set_sign(s2);

            d2.set_exponent(d1.exponent());
            assert!(d1.abs_cmp(&d2) > 0);
            assert!(d2.abs_cmp(&d1) < 0);
            d2.set_exponent(d1.exponent() + 123);
            assert!(d1.abs_cmp(&d2) < 0);
            assert!(d2.abs_cmp(&d1) > 0);
        }

        d3 = d1.clone().unwrap();
        assert!(d3.abs_cmp(&d1) == 0);
        d3.inv_sign();
        assert!(d3.abs_cmp(&d1) == 0);

        // abs cmp subnormal
        d1 = BigFloatNumber::from_raw_parts(
            &[1, WORD_MAX, 1],
            WORD_BIT_SIZE * 2 + 1,
            Sign::Pos,
            EXPONENT_MIN,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX, 1, 2],
            WORD_BIT_SIZE * 2 + 2,
            Sign::Neg,
            EXPONENT_MIN,
            false,
        )
        .unwrap();
        assert!(d1.abs_cmp(&d1) == 0);
        assert!(d1.abs_cmp(&d2) < 0);
        assert!(d2.abs_cmp(&d1) > 0);
        d1.inv_sign();
        d2.inv_sign();
        assert!(d1.abs_cmp(&d2) < 0);
        assert!(d2.abs_cmp(&d1) > 0);

        // nan
        assert!(BigFloatNumber::from_f64(p, f64::NAN).unwrap_err() == Error::InvalidArgument);

        // 0.0
        assert!(BigFloatNumber::from_f64(p, 0.0).unwrap().to_f64() == 0.0);

        // conversions
        for _ in 0..10000 {
            let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

            let f: f64 = random_f64();
            if f.is_finite() {
                d1 = BigFloatNumber::from_f64(p, f).unwrap();
                assert!(d1.to_f64() == f);
            }
        }

        for _ in 0..1000 {
            let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

            let i1: i8 = rand::random::<i8>();
            let i2: i16 = rand::random::<i16>();
            let i3: i32 = rand::random::<i32>();
            let i4: i64 = rand::random::<i64>();
            let i5: i128 = rand::random::<i128>();

            let n1 = BigFloatNumber::from_i8(i1, p).unwrap();
            let n2 = BigFloatNumber::from_i16(i2, p).unwrap();
            let n3 = BigFloatNumber::from_i32(i3, p).unwrap();
            let n4 = BigFloatNumber::from_i64(i4, p).unwrap();
            let n5 = BigFloatNumber::from_i128(i5, p).unwrap();

            let p1 = BigFloatNumber::parse(
                &format!("{}", i1),
                crate::Radix::Dec,
                p,
                RoundingMode::None,
                &mut cc,
            )
            .unwrap();
            let p2 = BigFloatNumber::parse(
                &format!("{}", i2),
                crate::Radix::Dec,
                p,
                RoundingMode::None,
                &mut cc,
            )
            .unwrap();
            let p3 = BigFloatNumber::parse(
                &format!("{}", i3),
                crate::Radix::Dec,
                p,
                RoundingMode::None,
                &mut cc,
            )
            .unwrap();
            let p4 = BigFloatNumber::parse(
                &format!("{}", i4),
                crate::Radix::Dec,
                p,
                RoundingMode::None,
                &mut cc,
            )
            .unwrap();
            let p5 = BigFloatNumber::parse(
                &format!("{}", i5),
                crate::Radix::Dec,
                p,
                RoundingMode::None,
                &mut cc,
            )
            .unwrap();

            assert!(p1.cmp(&n1) == 0);
            assert!(p2.cmp(&n2) == 0);
            assert!(p3.cmp(&n3) == 0);
            assert!(p4.cmp(&n4) == 0);
            assert!(p5.cmp(&n5) == 0);
        }

        // 0 * 0
        d1 = BigFloatNumber::new(p1).unwrap();
        d2 = BigFloatNumber::new(p2).unwrap();
        ref_num = BigFloatNumber::new(p).unwrap();
        d3 = d1.mul(&d2, p, rm).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0.99 * 0
        d1 = BigFloatNumber::from_f64(p1, 0.99).unwrap();
        d3 = d1.mul(&d2, p, rm).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 * 12349999
        d1 = BigFloatNumber::new(p1).unwrap();
        d2 = BigFloatNumber::from_f64(p2, 12349999.0).unwrap();
        d3 = d1.mul(&d2, p, rm).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * 1
        d1 = BigFloatNumber::from_f64(p1, 1.0).unwrap();
        d2 = BigFloatNumber::from_f64(p2, 1.0).unwrap();
        d3 = d1.mul(&d2, p, rm).unwrap();
        assert!(d3.cmp(&d1) == 0);

        // 1 * -1
        d1 = BigFloatNumber::from_f64(p1, 1.0).unwrap();
        d2 = BigFloatNumber::from_f64(p2, 1.0).unwrap().neg().unwrap();
        d3 = d1.mul(&d2, p, rm).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * 1
        d3 = d2.mul(&d1, p, rm).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * -1
        d1 = d1.neg().unwrap();
        d3 = d1.mul(&d2, p, rm).unwrap();
        ref_num = BigFloatNumber::from_f64(p, 1.0).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / 0
        d1 = BigFloatNumber::new(p1).unwrap();
        d2 = BigFloatNumber::new(p2).unwrap();
        assert!(d1.div(&d2, p, rm).unwrap_err() == Error::InvalidArgument);

        // d2 / 0
        d2 = BigFloatNumber::from_f64(p2, 123.0).unwrap();
        assert!(d2.div(&d1, p, rm).unwrap_err() == Error::DivisionByZero);

        // 0 / d2
        d3 = d1.div(&d2, p, rm).unwrap();
        ref_num = BigFloatNumber::new(p).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / -d2
        d2 = d2.neg().unwrap();
        d3 = d1.div(&d2, p, rm).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // add & sub & cmp
        for _ in 0..10000 {
            let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

            d1 = BigFloatNumber::random_normal(p1, -(p1 as Exponent) / 2, p1 as Exponent).unwrap();
            d2 = BigFloatNumber::random_normal(p2, -(p2 as Exponent) / 2, p2 as Exponent).unwrap();

            let d3 = d1.sub(&d2, p, RoundingMode::ToEven).unwrap();
            let d4 = d3.add(&d2, p, RoundingMode::ToEven).unwrap();

            eps.set_exponent(d1.exponent().max(d2.exponent()) - p as Exponent + 2);

            assert!(
                d1.sub(&d4, p, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&eps)
                    < 0
            );

            // subnormal
            d1 = random_subnormal(p1);
            d2 = random_subnormal(p2);

            let d3 = d1.sub(&d2, p, RoundingMode::ToEven).unwrap();
            let d4 = d3.add(&d2, p, RoundingMode::ToEven).unwrap();

            d1.set_precision(p, RoundingMode::ToEven).unwrap();

            assert!(
                d1.sub(&d4, p, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&BigFloatNumber::min_positive(p).unwrap())
                    <= 0
            );
        }

        // cancellation
        let w = WORD_MAX ^ 1 ^ 4 ^ 16;
        d1 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX, WORD_MAX],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            0,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[w, WORD_MAX, WORD_MAX],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            0,
            false,
        )
        .unwrap();

        d3 = d1.sub(&d2, WORD_BIT_SIZE, RoundingMode::None).unwrap();

        assert_eq!(w, d3.mantissa().digits()[0]);

        // increase precision
        d1 = BigFloatNumber::from_raw_parts(
            &[0, WORD_MAX - 10, WORD_MAX],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            0,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[0, WORD_MAX, WORD_MAX],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            -16,
            false,
        )
        .unwrap();

        d3 = d1
            .add(&d2, WORD_BIT_SIZE * 3, RoundingMode::ToEven)
            .unwrap();

        d1 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX - 10, WORD_MAX],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            0,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX, WORD_MAX],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            -16,
            false,
        )
        .unwrap();
        let d4 = d1
            .add(&d2, WORD_BIT_SIZE * 4, RoundingMode::ToEven)
            .unwrap();

        assert!(d4.mantissa_max_bit_len() == WORD_BIT_SIZE * 4);
        assert!(d3.cmp(&d4) == 0);

        d1 = BigFloatNumber::from_raw_parts(
            &[0, WORD_MAX - 10, WORD_MAX],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            0,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[0, WORD_MAX, WORD_MAX],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            -16,
            false,
        )
        .unwrap();

        d3 = d1
            .sub(&d2, WORD_BIT_SIZE * 3, RoundingMode::ToEven)
            .unwrap();

        d1 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX - 10, WORD_MAX],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            0,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX, WORD_MAX],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            -16,
            false,
        )
        .unwrap();
        let d4 = d1
            .sub(&d2, WORD_BIT_SIZE * 4, RoundingMode::ToEven)
            .unwrap();

        assert!(d4.mantissa_max_bit_len() == WORD_BIT_SIZE * 4);
        assert!(d3.cmp(&d4) == 0);

        // decrease precision
        d1 = BigFloatNumber::from_raw_parts(
            &[0, WORD_MAX - 10, WORD_MAX],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            0,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[0, WORD_MAX, WORD_MAX],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            -16,
            false,
        )
        .unwrap();
        d3 = d1.add(&d2, WORD_BIT_SIZE, RoundingMode::ToEven).unwrap();
        let mut d4 = d1
            .add(&d2, WORD_BIT_SIZE * 3, RoundingMode::ToEven)
            .unwrap();
        d4.set_precision(WORD_BIT_SIZE, RoundingMode::ToEven)
            .unwrap();

        assert!(d4.mantissa_max_bit_len() == WORD_BIT_SIZE);
        assert!(d3.cmp(&d4) == 0);

        d3 = d1.sub(&d2, WORD_BIT_SIZE, RoundingMode::ToEven).unwrap();
        let mut d4 = d1
            .sub(&d2, WORD_BIT_SIZE * 3, RoundingMode::ToEven)
            .unwrap();
        d4.set_precision(WORD_BIT_SIZE, RoundingMode::ToEven)
            .unwrap();

        assert!(d4.mantissa_max_bit_len() == WORD_BIT_SIZE);
        assert!(d3.cmp(&d4) == 0);

        // full prec
        for _ in 0..10000 {
            let p1 = (random::<usize>() % 3 + 1) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % 3 + 1) * WORD_BIT_SIZE;

            d1 = BigFloatNumber::random_normal(p1, -(p1 as Exponent) / 2, p1 as Exponent).unwrap();
            d2 = BigFloatNumber::random_normal(p2, -(p2 as Exponent) / 2, p2 as Exponent).unwrap();
            let d3 = d1.sub_full_prec(&d2).unwrap();
            let d4 = d3.add_full_prec(&d2).unwrap();
            //println!("\n=== res \n{:?} \n{:?} \n{:?} \n{:?} \n{:?} \n{:?}", d1, d2, d3, d4, d1.sub(&d4, RoundingMode::ToEven).unwrap().abs().unwrap(), eps);
            assert!(d1.cmp(&d4) == 0);
        }

        // mul & div
        for i in 0..10000 {
            let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

            d1 = BigFloatNumber::random_normal(
                p1,
                EXPONENT_MIN / 2 + p as Exponent,
                EXPONENT_MAX / 2,
            )
            .unwrap();
            d2 = BigFloatNumber::random_normal(p2, EXPONENT_MIN / 2, EXPONENT_MAX / 2).unwrap();

            if !d2.is_zero() {
                let d4 = if i & 1 == 0 {
                    let d3 = d1.div(&d2, p, RoundingMode::ToEven).unwrap();
                    d3.mul(&d2, p, RoundingMode::ToEven).unwrap()
                } else {
                    let d3 = d1.mul(&d2, p, RoundingMode::ToEven).unwrap();
                    d3.div(&d2, p, RoundingMode::ToEven).unwrap()
                };

                eps.set_exponent(d1.exponent() - p as Exponent + 2);

                //println!("\n{:?}\n{:?}\n{:?}\n{:?}", d1,d2,d3,d4);

                assert!(
                    d1.sub(&d4, p, RoundingMode::ToEven)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps)
                        < 0
                );
            }

            // subnormal
            d1 = random_subnormal(p1);
            d2 = random_subnormal(p2);

            let d3 = d1.div(&d2, p, RoundingMode::ToEven).unwrap();
            let d4 = d3.mul(&d2, p, RoundingMode::ToEven).unwrap();

            assert!(
                d1.sub(&d4, p, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&BigFloatNumber::min_positive(p).unwrap())
                    <= 0
            );
        }

        // full prec
        for _ in 0..10000 {
            let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

            d1 = BigFloatNumber::random_normal(
                p1,
                EXPONENT_MIN / 2 + p as Exponent, // avoid subnormal numbers
                EXPONENT_MAX / 2,
            )
            .unwrap();
            d2 = BigFloatNumber::random_normal(p2, EXPONENT_MIN / 2, EXPONENT_MAX / 2).unwrap();

            if !d2.is_zero() {
                let d3 = d1.mul_full_prec(&d2).unwrap();
                let d4 = d1.mul(&d2, p1 + p2, rm).unwrap();
                //println!("\n{:?}\n{:?}\n{:?}\n{:?}", d1,d2,d3,d4);
                assert!(d3.cmp(&d4) == 0);
            }
        }

        // large mantissa
        let pp = 32000;
        for i in 0..20 {
            let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE + pp;
            let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE + pp;
            let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE + pp;

            d1 = BigFloatNumber::random_normal(
                p1,
                EXPONENT_MIN / 2 + p as Exponent, // avoid subnormal numbers
                EXPONENT_MAX / 2,
            )
            .unwrap();
            d2 = BigFloatNumber::random_normal(p2, EXPONENT_MIN / 2, EXPONENT_MAX / 2).unwrap();

            if !d2.is_zero() {
                let d4 = if i & 1 == 0 {
                    let d3 = d1.div(&d2, p, RoundingMode::ToEven).unwrap();
                    d3.mul(&d2, p, RoundingMode::ToEven).unwrap()
                } else {
                    let d3 = d1.mul(&d2, p, RoundingMode::ToEven).unwrap();
                    d3.div(&d2, p, RoundingMode::ToEven).unwrap()
                };

                eps.set_exponent(d1.exponent() - p as Exponent + 2);

                assert!(
                    d1.sub(&d4, p, RoundingMode::ToEven)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps)
                        < 0
                );
            }
        }

        // variable precision
        d1 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX - 10, WORD_MAX],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            0,
            false,
        )
        .unwrap();
        d2 = BigFloatNumber::from_raw_parts(
            &[WORD_MAX, WORD_MAX - 10],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            -16,
            false,
        )
        .unwrap();

        d3 = d1.mul_full_prec(&d2).unwrap();

        let d4 = d1
            .mul(&d2, WORD_BIT_SIZE * 5, RoundingMode::ToEven)
            .unwrap();

        assert!(d4.mantissa_max_bit_len() == WORD_BIT_SIZE * 5);
        assert!(d3.cmp(&d4) == 0);

        let d4 = d1
            .mul(&d2, WORD_BIT_SIZE * 4, RoundingMode::ToEven)
            .unwrap();

        assert!(d4.mantissa_max_bit_len() == WORD_BIT_SIZE * 4);
        assert!(d3.cmp(&d4) == 0);

        d3.set_precision(WORD_BIT_SIZE * 3, RoundingMode::ToEven)
            .unwrap();
        let d4 = d1
            .mul(&d2, WORD_BIT_SIZE * 3, RoundingMode::ToEven)
            .unwrap();

        assert!(d4.mantissa_max_bit_len() == WORD_BIT_SIZE * 3);
        assert!(d3.cmp(&d4) == 0);

        d3.set_precision(WORD_BIT_SIZE, RoundingMode::ToEven)
            .unwrap();
        let d4 = d1.mul(&d2, WORD_BIT_SIZE, RoundingMode::ToEven).unwrap();

        assert!(d4.mantissa_max_bit_len() == WORD_BIT_SIZE);
        assert!(d3.cmp(&d4) == 0);

        d1 = BigFloatNumber::from_i8(2, WORD_BIT_SIZE * 2).unwrap();
        d2 = BigFloatNumber::from_i8(3, WORD_BIT_SIZE * 2).unwrap();

        d3 = d1
            .div(&d2, WORD_BIT_SIZE * 5, RoundingMode::ToEven)
            .unwrap();

        let words = {
            #[cfg(not(target_arch = "x86"))]
            {
                [
                    12297829382473034411,
                    12297829382473034410,
                    12297829382473034410,
                    12297829382473034410,
                    12297829382473034410,
                ]
            }
            #[cfg(target_arch = "x86")]
            {
                [2863311531, 2863311530, 2863311530, 2863311530, 2863311530]
            }
        };

        assert!(d3.mantissa_max_bit_len() == WORD_BIT_SIZE * 5);
        assert!(d3.mantissa().digits() == words);

        d3 = d1
            .div(&d2, WORD_BIT_SIZE * 3, RoundingMode::ToEven)
            .unwrap();

        let words = {
            #[cfg(not(target_arch = "x86"))]
            {
                [12297829382473034411, 12297829382473034410, 12297829382473034410]
            }
            #[cfg(target_arch = "x86")]
            {
                [2863311531, 2863311530, 2863311530]
            }
        };

        assert!(d3.mantissa_max_bit_len() == WORD_BIT_SIZE * 3);
        assert!(d3.mantissa().digits() == words);

        d3 = d1.div(&d2, WORD_BIT_SIZE, RoundingMode::ToEven).unwrap();

        let words = {
            #[cfg(not(target_arch = "x86"))]
            {
                [12297829382473034411]
            }
            #[cfg(target_arch = "x86")]
            {
                [2863311531]
            }
        };

        assert!(d3.mantissa_max_bit_len() == WORD_BIT_SIZE);
        assert!(d3.mantissa().digits() == words);

        // reciprocal
        for _ in 0..1000 {
            let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

            d1 = BigFloatNumber::random_normal(
                p1,
                EXPONENT_MIN + p as Exponent, // avoid exponent overflow error
                EXPONENT_MAX,
            )
            .unwrap();

            if !d1.is_zero() {
                let d3 = d1.reciprocal(p, rm).unwrap();
                let d4 = ONE.div(&d3, p, rm).unwrap();

                eps.set_exponent(d1.exponent() - p as Exponent + 2);

                //println!("\n{:?}\n{:?}\n{:?}", d1, d3, d4);

                assert!(d1.sub(&d4, p, rm).unwrap().abs().unwrap().cmp(&eps) < 0);
            }
        }

        // reciprocal near 1
        d1 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            320,
            RoundingMode::None,
            &mut cc,
        )
        .unwrap();

        d2 = d1.reciprocal(320, RoundingMode::ToEven).unwrap();
        d3 = BigFloatNumber::parse("1.00000000000000000000000000000000000000000000000000000000000000000D237A0818813B7A_e+0", crate::Radix::Hex, 320, RoundingMode::None, &mut cc).unwrap();

        //println!("{:?}", d2.format(crate::Radix::Hex, rm).unwrap());

        assert!(d2.cmp(&d3) == 0);

        // MAX
        d1 = BigFloatNumber::max_value(p1).unwrap();
        d2 = d1.reciprocal(p, rm).unwrap();
        d3 = ONE.div(&d1, p, rm).unwrap();
        let mut eps2 = BigFloatNumber::min_positive(p).unwrap();
        eps2.set_exponent(d3.exponent());
        // TODO: reciprocal is not precise, because does not take into account remainder.
        assert!(
            d3.sub(&d2, p, RoundingMode::None)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps2)
                <= 0
        );

        // variable precision
        d1 = BigFloatNumber::from_i8(3, WORD_BIT_SIZE * 2).unwrap();
        d2 = d1
            .reciprocal(WORD_BIT_SIZE * 5, RoundingMode::ToEven)
            .unwrap();

        let words = {
            #[cfg(not(target_arch = "x86"))]
            {
                [
                    12297829382473034411,
                    12297829382473034410,
                    12297829382473034410,
                    12297829382473034410,
                    12297829382473034410,
                ]
            }
            #[cfg(target_arch = "x86")]
            {
                [2863311531, 2863311530, 2863311530, 2863311530, 2863311530]
            }
        };

        assert!(d2.mantissa().digits() == words);

        d2 = d1.reciprocal(WORD_BIT_SIZE, RoundingMode::ToEven).unwrap();

        let words = {
            #[cfg(not(target_arch = "x86"))]
            {
                [12297829382473034411]
            }
            #[cfg(target_arch = "x86")]
            {
                [2863311531]
            }
        };

        assert!(d2.mantissa().digits() == words);

        // subnormal numbers basic sanity
        d1 = BigFloatNumber::min_positive(p).unwrap();
        d2 = BigFloatNumber::min_positive(p).unwrap();
        ref_num = BigFloatNumber::min_positive(p).unwrap();
        let one = BigFloatNumber::from_word(1, p).unwrap();
        ref_num = ref_num.mul(&one.add(&one, p, rm).unwrap(), p, rm).unwrap();

        // min_positive + min_positive = 2*min_positive
        assert!(d1.add(&d2, p, rm).unwrap().cmp(&ref_num) == 0);
        assert!(d1.add(&d2, p, rm).unwrap().cmp(&d1) > 0);
        assert!(d1.cmp(&d1.add(&d2, p, rm).unwrap()) < 0);

        // min_positive - min_positive = 0
        ref_num = BigFloatNumber::new(p).unwrap();
        assert!(d1.sub(&d2, p, rm).unwrap().cmp(&ref_num) == 0);

        // 1 * min_positive = min_positive
        assert!(one.mul(&d2, p, rm).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&one, p, rm).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&one, p, rm).unwrap().cmp(&d2) == 0);

        // normal -> subnormal -> normal
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MIN;
        d2 = BigFloatNumber::min_positive(p).unwrap();
        assert!(!d1.is_subnormal());
        assert!(d1.sub(&d2, p, rm).unwrap().cmp(&d1) < 0);
        assert!(d1.cmp(&d1.sub(&d2, p, rm).unwrap()) > 0);
        d1 = d1.sub(&d2, p, rm).unwrap();
        assert!(d1.is_subnormal());
        d1 = d1.add(&d2, p, rm).unwrap();
        assert!(!d1.is_subnormal());

        // overflow basic sanity
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MAX - (d1.m.max_bit_len() - 1) as Exponent;
        assert!(
            BigFloatNumber::max_value(p)
                .unwrap()
                .add(&d1, p, rm)
                .unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        assert!(
            BigFloatNumber::min_value(p)
                .unwrap()
                .sub(&d1, p, rm)
                .unwrap_err()
                == Error::ExponentOverflow(Sign::Neg)
        );
        assert!(
            BigFloatNumber::max_value(p)
                .unwrap()
                .mul(&BigFloatNumber::max_value(p).unwrap(), p, rm)
                .unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MIN;
        assert!(
            BigFloatNumber::max_value(p)
                .unwrap()
                .div(&d1, p, rm)
                .unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );

        // decompose and compose
        let f1 = random_f64_exp(50, 25);
        d1 = BigFloatNumber::from_f64(p, f1).unwrap();
        let (m, n, s, e, inexact) = d1.as_raw_parts();
        d2 = BigFloatNumber::from_raw_parts(m, n, s, e, inexact).unwrap();
        assert!(d1.cmp(&d2) == 0);
        assert!(BigFloatNumber::from_raw_parts(
            &[1, WORD_SIGNIFICANT_BIT],
            WORD_BIT_SIZE * 3,
            Sign::Pos,
            123,
            false,
        )
        .is_err());
        assert!(BigFloatNumber::from_raw_parts(
            &[1, WORD_SIGNIFICANT_BIT],
            WORD_BIT_SIZE * 2,
            Sign::Pos,
            123,
            false,
        )
        .is_ok());
        assert!(BigFloatNumber::from_raw_parts(
            &[1, WORD_SIGNIFICANT_BIT],
            WORD_BIT_SIZE,
            Sign::Pos,
            123,
            false,
        )
        .is_err());
        assert!(BigFloatNumber::from_raw_parts(&[0, 0], 0, Sign::Pos, 0, false).is_ok());
        assert!(BigFloatNumber::from_raw_parts(&[1, 0], 0, Sign::Pos, 0, false).is_err());
        assert!(BigFloatNumber::from_raw_parts(
            &[1, 2],
            WORD_BIT_SIZE,
            Sign::Pos,
            EXPONENT_MIN,
            false
        )
        .is_err());
        assert!(
            BigFloatNumber::from_raw_parts(&[1, 2], WORD_BIT_SIZE + 2, Sign::Pos, 123, false)
                .is_err()
        );
        assert!(BigFloatNumber::from_raw_parts(
            &[1, 2],
            WORD_BIT_SIZE + 2,
            Sign::Pos,
            EXPONENT_MIN,
            false
        )
        .is_ok());

        // sign and exponent
        d1 = one.clone().unwrap();
        assert!(d1.sign() == Sign::Pos);
        assert!(d1.is_positive());
        d1 = d1.neg().unwrap();
        assert!(d1.sign() == Sign::Neg);
        assert!(d1.is_negative());
        assert!(d1.exponent() == 1);

        // fract & int
        let f1 = 12345.6789;
        d1 = BigFloatNumber::from_f64(p, f1).unwrap();
        assert!(d1.fract().unwrap().to_f64() == f1.fract());
        assert!(d1.int().unwrap().to_f64() == (f1 as u64) as f64);

        let f1 = -0.006789;
        d1 = BigFloatNumber::from_f64(p, f1).unwrap();
        assert!(d1.fract().unwrap().cmp(&d1) == 0);
        assert!(d1.int().unwrap().is_zero());

        let f1 = -1234567890.0;
        d1 = BigFloatNumber::from_f64(p, f1).unwrap();
        assert!(d1.fract().unwrap().is_zero());
        assert!(d1.int().unwrap().cmp(&d1) == 0);

        assert!(
            BigFloatNumber::min_positive(p)
                .unwrap()
                .fract()
                .unwrap()
                .cmp(&BigFloatNumber::min_positive(p).unwrap())
                == 0
        );
        assert!(BigFloatNumber::min_positive(p)
            .unwrap()
            .int()
            .unwrap()
            .is_zero());

        d1 = BigFloatNumber::new(p).unwrap();
        assert!(d1.fract().unwrap().is_zero());
        assert!(d1.int().unwrap().is_zero());

        // ceil & floor
        d1 = BigFloatNumber::from_f64(p, 12.3).unwrap();
        assert!(d1.floor().unwrap().to_f64() == 12.0);
        assert!(d1.ceil().unwrap().to_f64() == 13.0);
        d1 = BigFloatNumber::from_f64(p, 12.0).unwrap();
        assert!(d1.floor().unwrap().to_f64() == 12.0);
        assert!(d1.ceil().unwrap().to_f64() == 12.0);

        d1 = BigFloatNumber::from_f64(p, -12.3).unwrap();
        assert!(d1.floor().unwrap().to_f64() == -13.0);
        assert!(d1.ceil().unwrap().to_f64() == -12.0);
        d1 = BigFloatNumber::from_f64(p, -12.0).unwrap();
        assert!(d1.floor().unwrap().to_f64() == -12.0);
        assert!(d1.ceil().unwrap().to_f64() == -12.0);

        // abs
        d1 = BigFloatNumber::from_f64(p, 12.3).unwrap();
        assert!(d1.abs().unwrap().to_f64() == 12.3);
        d1 = BigFloatNumber::from_f64(p, -12.3).unwrap();
        assert!(d1.abs().unwrap().to_f64() == 12.3);

        // rem
        for (prec1, prec2) in [(128, 128), (128, 320), (320, 128)] {
            for sign_inv in [false, true] {
                for (s1, s2) in [
                    ("9.2", "1.2"),
                    ("2.0", "4.0"),
                    ("7.0", "4.0"),
                    ("8.0", "4.0"),
                    ("9.0", "4.0"),
                    ("14", "15"),
                    ("15", "15"),
                    ("16", "15"),
                    ("33", "15"),
                    ("44", "15"),
                    ("0.000000007", "0.000000004"),
                    ("0.00000000000000009", "0.000000000000000004"),
                ] {
                    d1 = BigFloatNumber::parse(
                        s1,
                        crate::Radix::Dec,
                        prec1,
                        RoundingMode::None,
                        &mut cc,
                    )
                    .unwrap();
                    d2 = BigFloatNumber::parse(
                        s2,
                        crate::Radix::Dec,
                        prec2,
                        RoundingMode::None,
                        &mut cc,
                    )
                    .unwrap();

                    let p = prec1.max(prec2);

                    d3 = d1
                        .sub(
                            &d1.div(&d2, p + 1, RoundingMode::ToEven)
                                .unwrap()
                                .floor()
                                .unwrap()
                                .mul(&d2, p + 1, RoundingMode::ToEven)
                                .unwrap(),
                            p + 1,
                            RoundingMode::ToEven,
                        )
                        .unwrap();

                    if sign_inv {
                        d1.inv_sign();
                        d3.inv_sign();
                    }

                    let ret = d1.rem(&d2).unwrap();

                    // println!("\n{:?}", d1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
                    // println!("{:?}", d2.format(crate::Radix::Dec, RoundingMode::None).unwrap());
                    // println!("{:?}", ret.format(crate::Radix::Dec, RoundingMode::None).unwrap());
                    // println!("{:?}", d3.format(crate::Radix::Dec, RoundingMode::None).unwrap());

                    assert!(ret.sub(&d3, p, RoundingMode::ToEven).unwrap().is_zero());
                }
            }
        }

        for _ in 0..1000 {
            let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
            let p = p1.max(p2);
            let e_rng = (p_rng * WORD_BIT_SIZE) as Exponent;

            d1 = BigFloatNumber::random_normal(
                p1,
                EXPONENT_MIN / 2 - p1 as Exponent,
                EXPONENT_MAX / 2,
            )
            .unwrap()
            .abs()
            .unwrap();
            d2 = BigFloatNumber::random_normal(p2, d1.exponent() - e_rng, d1.exponent() + e_rng)
                .unwrap()
                .abs()
                .unwrap();

            let ret = d1.rem(&d2).unwrap();

            d3 = d1
                .sub(
                    &d1.div(&d2, p + p_rng * WORD_BIT_SIZE, RoundingMode::None)
                        .unwrap()
                        .floor()
                        .unwrap()
                        .mul(&d2, p + p_rng * WORD_BIT_SIZE, RoundingMode::None)
                        .unwrap(),
                    ret.mantissa_max_bit_len(),
                    RoundingMode::ToEven,
                )
                .unwrap();

            //println!("\n{:?}", d1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
            //println!("{:?}", d2.format(crate::Radix::Dec, RoundingMode::None).unwrap());
            //println!("{:?}", ret.format(crate::Radix::Dec, RoundingMode::None).unwrap());
            //println!("{:?}", d3.format(crate::Radix::Dec, RoundingMode::None).unwrap());

            assert!(ret.sub(&d3, p, RoundingMode::ToEven).unwrap().is_zero());

            // subnormal
            d1 = random_subnormal(p1);
            d2 = random_subnormal(p2);

            let mut ret = d1.rem(&d2).unwrap();

            // check with normalized numbers.
            d1.set_exponent(0);
            d2.set_exponent(0);

            let mut d3 = d1.rem(&d2).unwrap();

            if !ret.is_zero() {
                // check exponent
                assert!(ret.exponent() == EXPONENT_MIN);
            }

            eps.set_exponent(1 - (ret.precision() as Exponent));

            // compare mantissas
            ret.set_exponent((ret.mantissa_max_bit_len() - ret.precision()) as Exponent);
            d3.set_exponent(0);

            assert!(
                ret.sub(&d3, p, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&eps)
                    <= 0
            );
        }

        // special case rem
        let d1 = BigFloatNumber::from_words(&[WORD_SIGNIFICANT_BIT], Sign::Pos, 2).unwrap();
        let d2 = BigFloatNumber::from_words(&[WORD_SIGNIFICANT_BIT], Sign::Pos, 65).unwrap();

        let d3 = d2.rem(&d1).unwrap();
        assert!(d3.is_zero());

        // is_odd_int
        let d1 =
            BigFloatNumber::parse("3.0", crate::Radix::Dec, 128, RoundingMode::ToEven, &mut cc)
                .unwrap();
        assert!(d1.is_odd_int());
        let d1 = BigFloatNumber::parse(
            "3.01",
            crate::Radix::Dec,
            128,
            RoundingMode::ToEven,
            &mut cc,
        )
        .unwrap();
        assert!(!d1.is_odd_int());
        let d1 = BigFloatNumber::parse(
            "32.0",
            crate::Radix::Dec,
            128,
            RoundingMode::ToEven,
            &mut cc,
        )
        .unwrap();
        assert!(!d1.is_odd_int());
        let d1 = BigFloatNumber::parse(
            "32.01",
            crate::Radix::Dec,
            128,
            RoundingMode::ToEven,
            &mut cc,
        )
        .unwrap();
        assert!(!d1.is_odd_int());
        let d1 = BigFloatNumber::parse(
            "0.00000000000000000000001",
            crate::Radix::Dec,
            256,
            RoundingMode::ToEven,
            &mut cc,
        )
        .unwrap();
        assert!(!d1.is_odd_int());
        let d1 = BigFloatNumber::parse(
            "5.00000000000000000000001",
            crate::Radix::Dec,
            256,
            RoundingMode::ToEven,
            &mut cc,
        )
        .unwrap();
        assert!(!d1.is_odd_int());
        let d1 = BigFloatNumber::parse(
            "10000000000000000000001.0",
            crate::Radix::Dec,
            256,
            RoundingMode::ToEven,
            &mut cc,
        )
        .unwrap();
        assert!(d1.is_odd_int());
        let d1 = BigFloatNumber::parse(
            "10000000000000000000001.0000000000000000001",
            crate::Radix::Dec,
            256,
            RoundingMode::ToEven,
            &mut cc,
        )
        .unwrap();
        assert!(!d1.is_odd_int());
        let d1 = BigFloatNumber::parse("1.1", crate::Radix::Bin, 256, RoundingMode::None, &mut cc)
            .unwrap();
        assert!(!d1.is_odd_int());

        // build from words
        let d1 = BigFloatNumber::from_words(&[], Sign::Pos, EXPONENT_MAX).unwrap();
        assert!(d1.is_zero());
        assert_eq!(d1.exponent(), 0);
        assert_eq!(d1.precision(), 0);
        assert_eq!(d1.mantissa_max_bit_len(), 0);
        assert_eq!(d1.sign(), Sign::Pos);

        let d1 = BigFloatNumber::from_words(&[0, 0], Sign::Neg, EXPONENT_MIN).unwrap();
        assert!(d1.is_zero());
        assert_eq!(d1.exponent(), 0);
        assert_eq!(d1.precision(), 0);
        assert_eq!(d1.mantissa_max_bit_len(), WORD_BIT_SIZE * 2);
        assert_eq!(d1.sign(), Sign::Neg);

        let d1 = BigFloatNumber::from_words(&[3, 1], Sign::Pos, EXPONENT_MAX).unwrap();
        #[cfg(not(target_arch = "x86"))]
        {
            assert_eq!(
                d1.mantissa().digits(),
                [0x8000000000000000u64, 0x8000000000000001u64]
            );
        }
        #[cfg(target_arch = "x86")]
        {
            assert_eq!(d1.mantissa().digits(), [0x80000000u32, 0x80000001u32]);
        }
        assert_eq!(d1.exponent(), EXPONENT_MAX - WORD_BIT_SIZE as Exponent + 1);
        assert_eq!(d1.precision(), WORD_BIT_SIZE * 2);
        assert_eq!(d1.mantissa_max_bit_len(), WORD_BIT_SIZE * 2);
        assert_eq!(d1.sign(), Sign::Pos);

        let d1 = BigFloatNumber::from_words(&[3, 1], Sign::Neg, EXPONENT_MIN).unwrap();
        assert_eq!(d1.mantissa().digits(), [3, 1]);
        assert_eq!(d1.exponent(), EXPONENT_MIN);
        assert_eq!(d1.precision(), WORD_BIT_SIZE + 1);
        assert_eq!(d1.mantissa_max_bit_len(), WORD_BIT_SIZE * 2);
        assert_eq!(d1.sign(), Sign::Neg);

        let d1 = BigFloatNumber::from_words(&[3, 1], Sign::Pos, EXPONENT_MIN + 5).unwrap();
        assert_eq!(d1.mantissa().digits(), [3 << 5, 1 << 5]);
        assert_eq!(d1.exponent(), EXPONENT_MIN);
        assert_eq!(d1.precision(), WORD_BIT_SIZE + 6);
        assert_eq!(d1.mantissa_max_bit_len(), WORD_BIT_SIZE * 2);
        assert_eq!(d1.sign(), Sign::Pos);

        let words = {
            #[cfg(not(target_arch = "x86"))]
            {
                [3, 0x8000000000000000u64]
            }
            #[cfg(target_arch = "x86")]
            {
                [3, 0x80000000u32]
            }
        };
        let d1 = BigFloatNumber::from_words(&words, Sign::Pos, EXPONENT_MIN + 5).unwrap();
        assert_eq!(d1.mantissa().digits(), words);
        assert_eq!(d1.exponent(), EXPONENT_MIN + 5);
        assert_eq!(d1.precision(), WORD_BIT_SIZE * 2);
        assert_eq!(d1.mantissa_max_bit_len(), WORD_BIT_SIZE * 2);
        assert_eq!(d1.sign(), Sign::Pos);
    }

    fn random_f64() -> f64 {
        random_f64_exp(f64::MAX_10_EXP, f64::MIN_10_EXP)
    }

    fn random_f64_exp(max_exp: i32, min_exp: i32) -> f64 {
        let mut f: f64 = random();
        f = f.powi(random::<i32>().abs() % max_exp - min_exp);
        if random::<i8>() & 1 == 0 {
            f = -f;
        }
        f
    }

    #[test]
    fn test_rounding() {
        // trailing bits
        // 0 0000
        // 0 0001
        // 0 1000
        // 0 1001
        // 1 1000
        // 1 1001

        let mantissas = {
            #[cfg(not(target_arch = "x86"))]
            {
                [
                    [0x8000000000000000u64, 0x8000000000000000u64],
                    [0x8000000000000001u64, 0x8000000000000000u64],
                    [0x8000000000000008u64, 0x8000000000000000u64],
                    [0x8000000000000009u64, 0x8000000000000000u64],
                    [0x8000000000000018u64, 0x8000000000000000u64],
                    [0x8000000000000019u64, 0x8000000000000000u64],
                ]
            }
            #[cfg(target_arch = "x86")]
            {
                [
                    [0x80000000u32, 0x80000000u32],
                    [0x80000001u32, 0x80000000u32],
                    [0x80000008u32, 0x80000000u32],
                    [0x80000009u32, 0x80000000u32],
                    [0x80000018u32, 0x80000000u32],
                    [0x80000019u32, 0x80000000u32],
                ]
            }
        };

        let rounding_results_posnum = {
            #[cfg(not(target_arch = "x86"))]
            {
                [
                    (RoundingMode::None, mantissas),
                    (
                        RoundingMode::Down,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::Up,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::FromZero,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::ToZero,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::ToEven,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::ToOdd,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                        ],
                    ),
                ]
            }
            #[cfg(target_arch = "x86")]
            {
                [
                    (RoundingMode::None, mantissas),
                    (
                        RoundingMode::Down,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::Up,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::FromZero,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::ToZero,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::ToEven,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::ToOdd,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                        ],
                    ),
                ]
            }
        };

        let rounding_results_negnum = {
            #[cfg(not(target_arch = "x86"))]
            {
                [
                    (RoundingMode::None, mantissas),
                    (
                        RoundingMode::Down,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::Up,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::FromZero,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::ToZero,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::ToEven,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                        ],
                    ),
                    (
                        RoundingMode::ToOdd,
                        [
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000000u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000010u64, 0x8000000000000000u64],
                            [0x8000000000000020u64, 0x8000000000000000u64],
                        ],
                    ),
                ]
            }
            #[cfg(target_arch = "x86")]
            {
                [
                    (RoundingMode::None, mantissas),
                    (
                        RoundingMode::Down,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::Up,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::FromZero,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::ToZero,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::ToEven,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                        ],
                    ),
                    (
                        RoundingMode::ToOdd,
                        [
                            [0x80000000u32, 0x80000000u32],
                            [0x80000000u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000010u32, 0x80000000u32],
                            [0x80000020u32, 0x80000000u32],
                        ],
                    ),
                ]
            }
        };

        for (sign, rr) in
            [(Sign::Pos, rounding_results_posnum), (Sign::Neg, rounding_results_negnum)]
        {
            for (rm, expected_mantissas) in rr.iter() {
                for (m1, m2) in mantissas.iter().zip(expected_mantissas.iter()) {
                    // rounding
                    let d1 = BigFloatNumber::from_raw_parts(
                        m1,
                        WORD_BIT_SIZE * 2,
                        sign,
                        WORD_BIT_SIZE as Exponent,
                        false,
                    )
                    .unwrap();
                    let d2 = d1.round(WORD_BIT_SIZE - 4, *rm).unwrap();
                    let d3 = BigFloatNumber::from_raw_parts(
                        m2,
                        WORD_BIT_SIZE * 2,
                        sign,
                        WORD_BIT_SIZE as Exponent,
                        false,
                    )
                    .unwrap();

                    //println!("\n{:?} {:?}\n{:?}\nresult {:?}\nexpect {:?}", sign, rm, d1.m, d2.m, d3.m);

                    assert!(d2.cmp(&d3) == 0);
                }
            }
        }

        // special cases
        let testset = [
            (
                [0, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -99,
                99,
                RoundingMode::None,
                [0, 0],
                0,
            ),
            (
                [0, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -99,
                99,
                RoundingMode::Up,
                [0, WORD_SIGNIFICANT_BIT],
                -98,
            ),
            (
                [0, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -99,
                99,
                RoundingMode::ToOdd,
                [0, WORD_SIGNIFICANT_BIT],
                -98,
            ),
            (
                [0, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -99,
                99,
                RoundingMode::ToEven,
                [0, 0],
                0,
            ),
            (
                [1, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -99,
                99,
                RoundingMode::ToEven,
                [0, WORD_SIGNIFICANT_BIT],
                -98,
            ),
            (
                [1, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -99,
                99,
                RoundingMode::Down,
                [0, 0],
                0,
            ),
            (
                [0, WORD_SIGNIFICANT_BIT],
                Sign::Neg,
                -99,
                99,
                RoundingMode::Down,
                [0, WORD_SIGNIFICANT_BIT],
                -98,
            ),
            (
                [1, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -100,
                99,
                RoundingMode::ToEven,
                [0, 0],
                0,
            ),
            (
                [1, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -100,
                99,
                RoundingMode::ToOdd,
                [0, 0],
                0,
            ),
            (
                [1, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -100,
                99,
                RoundingMode::Down,
                [0, 0],
                0,
            ),
            (
                [0, WORD_SIGNIFICANT_BIT],
                Sign::Pos,
                -100,
                99,
                RoundingMode::Up,
                [0, WORD_SIGNIFICANT_BIT],
                -98,
            ),
            (
                [1, 1],
                Sign::Pos,
                EXPONENT_MIN,
                EXPONENT_MIN.unsigned_abs() as usize + WORD_BIT_SIZE - 1,
                RoundingMode::Up,
                [0, 2],
                EXPONENT_MIN,
            ),
            (
                [1, 1],
                Sign::Pos,
                EXPONENT_MIN,
                EXPONENT_MIN.unsigned_abs() as usize + WORD_BIT_SIZE - 1,
                RoundingMode::Down,
                [0, 0],
                0,
            ),
            (
                [1, 1],
                Sign::Pos,
                EXPONENT_MIN,
                EXPONENT_MIN.unsigned_abs() as usize + WORD_BIT_SIZE - 1,
                RoundingMode::ToEven,
                [0, 2],
                EXPONENT_MIN,
            ),
            (
                [0, 1],
                Sign::Pos,
                EXPONENT_MIN,
                EXPONENT_MIN.unsigned_abs() as usize + WORD_BIT_SIZE - 1,
                RoundingMode::ToEven,
                [0, 0],
                0,
            ),
            (
                [1, 1],
                Sign::Pos,
                EXPONENT_MIN,
                EXPONENT_MIN.unsigned_abs() as usize + WORD_BIT_SIZE - 1,
                RoundingMode::ToOdd,
                [0, 2],
                EXPONENT_MIN,
            ),
            (
                [0, 1],
                Sign::Pos,
                EXPONENT_MIN,
                EXPONENT_MIN.unsigned_abs() as usize + WORD_BIT_SIZE - 1,
                RoundingMode::ToOdd,
                [0, 2],
                EXPONENT_MIN,
            ),
        ];
        for (m1, s, e1, n, rm, m2, e2) in testset {
            //println!("{:?}", (m1, s, e1, n, rm, m2, e2));
            let d1 = BigFloatNumber::from_words(&m1, s, e1).unwrap();
            let d2 = d1.round(n, rm).unwrap();
            assert_eq!(d2.mantissa().digits(), m2);
            assert_eq!(d2.sign(), s);
            assert_eq!(d2.exponent(), e2);
            assert!(!d1.inexact());
            assert!(d2.inexact());
        }
    }

    #[test]
    fn test_inexact() {
        // any arg is inexact
        let mut d1 =
            BigFloatNumber::from_words(&[0, 18 << (WORD_BIT_SIZE - 5)], Sign::Pos, 5).unwrap();
        let mut d2 =
            BigFloatNumber::from_words(&[0, 6 << (WORD_BIT_SIZE - 3)], Sign::Pos, 3).unwrap();

        for op in [
            BigFloatNumber::add,
            BigFloatNumber::sub,
            BigFloatNumber::mul,
            BigFloatNumber::div,
        ] {
            let d3 = op(&d1, &d2, 256, RoundingMode::None).unwrap();
            assert!(!d3.inexact());

            d1.set_inexact(true);
            let d3 = op(&d1, &d2, 256, RoundingMode::None).unwrap();
            assert!(d3.inexact());

            d2.set_inexact(true);
            let d3 = op(&d1, &d2, 256, RoundingMode::None).unwrap();
            assert!(d3.inexact());

            d1.set_inexact(false);
            let d3 = op(&d1, &d2, 256, RoundingMode::None).unwrap();
            assert!(d3.inexact());

            d2.set_inexact(false);
        }

        let d3 = d1.rem(&d2).unwrap();
        assert!(!d3.inexact());

        d1.set_inexact(true);
        let d3 = d1.rem(&d2).unwrap();
        assert!(d3.inexact());

        d2.set_inexact(true);
        let d3 = d1.rem(&d2).unwrap();
        assert!(d3.inexact());

        d1.set_inexact(false);
        let d3 = d1.rem(&d2).unwrap();
        assert!(d3.inexact());

        // inexact because of rounding
        let d1 = BigFloatNumber::from_words(&[2, 18 << (WORD_BIT_SIZE - 5)], Sign::Pos, 5).unwrap();
        let d2 = BigFloatNumber::from_words(&[1, 6 << (WORD_BIT_SIZE - 3)], Sign::Pos, 3).unwrap();

        assert!(!d1.inexact());
        assert!(!d2.inexact());

        for op in [
            BigFloatNumber::add,
            BigFloatNumber::sub,
            BigFloatNumber::mul,
            BigFloatNumber::div,
        ] {
            let d3 = op(&d1, &d2, WORD_BIT_SIZE * 2, RoundingMode::None).unwrap();
            assert!(d3.inexact());
            let d3 = op(&d2, &d1, WORD_BIT_SIZE * 2, RoundingMode::None).unwrap();
            assert!(d3.inexact());
        }

        // inexact because of subnormalization
        let d1 =
            BigFloatNumber::from_words(&[1, WORD_SIGNIFICANT_BIT], Sign::Pos, EXPONENT_MIN / 2 - 1)
                .unwrap();
        let d2 =
            BigFloatNumber::from_words(&[1, WORD_SIGNIFICANT_BIT], Sign::Pos, EXPONENT_MIN / 2)
                .unwrap();

        assert!(!d1.inexact());
        assert!(!d2.inexact());

        let d3 = d1.mul(&d2, WORD_BIT_SIZE * 4, RoundingMode::None).unwrap();
        assert!(d3.inexact());

        let d1 = BigFloatNumber::from_words(&[1, WORD_SIGNIFICANT_BIT], Sign::Pos, EXPONENT_MIN)
            .unwrap();
        let d2 = BigFloatNumber::from_words(&[1, WORD_SIGNIFICANT_BIT], Sign::Pos, EXPONENT_MIN)
            .unwrap();

        assert!(!d1.inexact());
        assert!(!d2.inexact());

        let d3 = d1.mul(&d2, 256, RoundingMode::Up).unwrap();
        assert!(d3.inexact());

        let d3 = d1.mul(&d2, 256, RoundingMode::None).unwrap();
        assert!(d3.inexact());

        // set precision
        let mut d1 = BigFloatNumber::from_words(&[0, WORD_MAX], Sign::Pos, 0).unwrap();
        assert!(!d1.inexact());
        d1.set_precision(WORD_BIT_SIZE, RoundingMode::ToEven)
            .unwrap();
        assert!(!d1.inexact());

        let mut d1 = BigFloatNumber::from_words(&[0, WORD_MAX], Sign::Pos, 0).unwrap();
        d1.set_inexact(true);
        assert!(d1.inexact());
        d1.set_precision(WORD_BIT_SIZE, RoundingMode::ToEven)
            .unwrap();
        assert!(d1.inexact());

        let mut d1 =
            BigFloatNumber::from_words(&[WORD_SIGNIFICANT_BIT, WORD_MAX], Sign::Pos, 0).unwrap();
        assert!(!d1.inexact());
        d1.set_precision(WORD_BIT_SIZE, RoundingMode::ToEven)
            .unwrap();
        assert!(d1.inexact());

        // round
        let d1 = BigFloatNumber::from_words(&[0, WORD_MAX], Sign::Pos, 0).unwrap();
        assert!(!d1.inexact());
        let d2 = d1.round(WORD_BIT_SIZE, RoundingMode::ToEven).unwrap();
        assert!(!d2.inexact());

        let mut d1 = BigFloatNumber::from_words(&[0, WORD_MAX], Sign::Pos, 0).unwrap();
        d1.set_inexact(true);
        assert!(d1.inexact());
        let d2 = d1.round(WORD_BIT_SIZE, RoundingMode::ToEven).unwrap();
        assert!(d2.inexact());

        let d1 =
            BigFloatNumber::from_words(&[WORD_SIGNIFICANT_BIT, WORD_MAX], Sign::Pos, 0).unwrap();
        assert!(!d1.inexact());
        let d2 = d1.round(WORD_BIT_SIZE, RoundingMode::None).unwrap();
        assert!(d2.inexact());

        let d1 = BigFloatNumber::from_words(&[0, WORD_MAX], Sign::Pos, -2).unwrap();
        assert!(!d1.inexact());
        let d2 = d1.round(1, RoundingMode::None).unwrap();
        assert!(d2.inexact());
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn add_sub_perf() {
        let p = 132;
        let mut n = vec![];
        for _ in 0..1000000 {
            n.push(BigFloatNumber::random_normal(p, -20, 20).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            let mut f = n[0].clone().unwrap();

            for (i, ni) in n.iter().enumerate().skip(1) {
                if i & 1 == 0 {
                    f = f.add(ni, p, RoundingMode::ToEven).unwrap();
                } else {
                    f = f.sub(ni, p, RoundingMode::ToEven).unwrap();
                }
            }

            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn recip_perf() {
        for _ in 0..5 {
            let p = 32 * 450;
            let mut n = vec![];
            for _ in 0..1000 {
                n.push(BigFloatNumber::random_normal(p, -20, 20).unwrap());
            }

            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ONE.div(ni, p, RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("div {}", time.as_millis());

            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.reciprocal(p, RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("recip {}", time.as_millis());
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn recip_mul_perf() {
        for _ in 0..5 {
            let p = 1000 * 32;
            let mut n = vec![];
            for _ in 0..1000 {
                n.push(BigFloatNumber::random_normal(p, -20, 20).unwrap());
            }

            let f1 = n[0].clone().unwrap();

            let start_time = std::time::Instant::now();
            for ni in n.iter().skip(1) {
                let f = f1.reciprocal(p, RoundingMode::None).unwrap();
                let _f = f.mul(ni, p, RoundingMode::None).unwrap();
            }
            let time = start_time.elapsed();
            println!("recip {}", time.as_millis());

            let start_time = std::time::Instant::now();
            for ni in n.iter().skip(1) {
                let _f = ni.div(&f1, p, RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("div {}", time.as_millis());
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn rem_perf() {
        for _ in 0..5 {
            let mut d1 = vec![];
            let mut d2 = vec![];
            let p_rng = 10;
            let p_min = 100;
            for _ in 0..1000 {
                let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
                let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

                let d = BigFloatNumber::random_normal(
                    p1,
                    EXPONENT_MIN / 2 - p1 as Exponent,
                    EXPONENT_MAX / 2,
                )
                .unwrap()
                .abs()
                .unwrap();
                let de = d.exponent();
                d1.push(d);
                d2.push(
                    BigFloatNumber::random_normal(
                        p2,
                        de - (WORD_BIT_SIZE * p_rng) as Exponent,
                        de + (WORD_BIT_SIZE * p_rng) as Exponent,
                    )
                    .unwrap()
                    .abs()
                    .unwrap(),
                );
            }

            let start_time = std::time::Instant::now();
            for (d1, d2) in d1.iter().zip(d2.iter()) {
                let _ = d1.rem(d2);
            }
            let time = start_time.elapsed();
            println!("rem {}", time.as_millis());
        }
    }
}
