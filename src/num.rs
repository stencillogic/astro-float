//! BigFloatNumber definition and basic arithmetic, comparison, and number manipulation operations.

use crate::defs::SignedWord;
use crate::defs::Exponent;
use crate::defs::Sign;
use crate::defs::Word;
use crate::defs::Error;
use crate::defs::EXPONENT_MAX;
use crate::defs::EXPONENT_MIN;
use crate::defs::WORD_SIGNIFICANT_BIT;
use crate::defs::RoundingMode;
use crate::defs::WORD_BIT_SIZE;
use crate::mantissa::Mantissa;
use crate::common::consts::ONE;


/// BigFloatNumber represents floating point number with mantissa of an arbitrary size, and exponent.
#[derive(Debug)]
pub struct BigFloatNumber {
    pub(super) e: Exponent,
    pub(super) s: Sign,
    pub(super) m: Mantissa,
}

impl BigFloatNumber {

    // Check the precision so it does not cause arithmetic overflows anywhere.
    fn p_assertion(p: usize) -> Result<(), Error> {
        if p >= (isize::MAX/2 + EXPONENT_MIN as isize) as usize {
            Err(Error::InvalidArgument)
        } else {
            Ok(())
        }
    }

    /// Returns a new number with value of 0 and precision of `p` bits. Precision is rounded upwards to the word size.
    /// 
    /// ## Errors
    /// 
    ///  - InvalidArgument - precision is incorrect.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn new(p: usize) -> Result<Self, Error>  {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::new(p)?,
            e: 0,
            s: Sign::Pos,
        })
    }

    /// Returns the maximum value for the specified precision `p`: all bits of the mantissa are set to 1, the exponent has the maximum possible value, and the sign is positive. Precision is rounded upwards to the word size.
    /// 
    /// ## Errors
    /// 
    ///  - InvalidArgument - precision is incorrect.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn max(p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::oned_mantissa(p)?,
            e: EXPONENT_MAX,
            s: Sign::Pos,
        })
    }

    /// Returns the minimum value for the specified precision `p`: all bits of the mantissa are set to 1, the exponent has the maximum possible value, and the sign is negative. Precision is rounded upwards to the word size.
    /// 
    /// ## Errors
    /// 
    ///  - InvalidArgument - precision is incorrect.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn min(p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::oned_mantissa(p)?,
            e: EXPONENT_MAX,
            s: Sign::Neg,
        })
    }

    /// Returns the minimum positive subnormal value for the specified precision `p`: only the least significant bit of the mantissa is set to 1, the exponent has the minimum possible value, and the sign is positive. Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    /// 
    ///  - InvalidArgument - precision is incorrect.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn min_positive(p: usize) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        Ok(BigFloatNumber {
            m: Mantissa::min(p)?,
            e: EXPONENT_MIN,
            s: Sign::Pos,
        })
    }

    /// Returns a new number with value `d` and the precision `p`. Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    /// 
    ///  - InvalidArgument - precision is incorrect.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
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
            })
        }
    }

    /// Returns a copy of the number with the sign reversed.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn neg(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        ret.s = ret.s.invert();
        Ok(ret)
    }

    /// Adds `d2` to `self` and returns the result of the operation rounded according to `rm`. The resulting precision is equal to the highest precision of the two operands.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow - the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    #[inline]
    pub fn add(&self, d2: &Self, rm: RoundingMode) -> Result<Self, Error> {
        self.add_sub(d2, 1, rm, false)
    }

    /// Subtracts `d2` from `self` and returns the result of the operation rounded according to `rm`. The resulting precision is equal to the highest precision of the two operands.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow - the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    #[inline]
    pub fn sub(&self, d2: &Self, rm: RoundingMode) -> Result<Self, Error> {
        self.add_sub(d2, -1, rm, false)
    }

    /// Adds `d2` to `self` and returns the result of the operation. The resulting precision is equal to the full precision of the result. This operation can be used to emulate integer addition.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow - the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    #[inline]
    pub fn add_full_prec(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, 1, RoundingMode::None, true)
    }

    /// Subtracts `d2` from `self` and returns the result of the operation. The resulting precision is equal to the full precision of the result. This operation can be used to emulate integer subtraction.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow - the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    #[inline]
    pub fn sub_full_prec(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, -1, RoundingMode::None, true)
    }

    /// Multiplies `d2` by `self` and returns the result of the operation rounded according to `rm`. The resulting precision is equal to the highest precision of the two operands.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow - the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    #[inline]
    pub fn mul(&self, d2: &Self, rm: RoundingMode) -> Result<Self, Error> {
        self.mul_general_case(d2, rm, false)
    }

    /// Multiplies `d2` by `self` and returns the result of the operation. The resulting precision is equal to the full precision of the result. This operation can be used to emulate integer multiplication.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow - the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    #[inline]
    pub fn mul_full_prec(&self, d2: &Self) -> Result<Self, Error> {
        self.mul_general_case(d2, RoundingMode::None, true)
    }

    fn mul_general_case(&self, d2: &Self, rm: RoundingMode, full_prec: bool) -> Result<Self, Error> {

        // TODO: consider short multiplication for full_prec = false.

        if self.m.is_zero() || d2.m.is_zero() {
            return Self::new(self.m.max_bit_len().max(d2.m.max_bit_len()));
        }

        let s = if self.s == d2.s { Sign::Pos } else { Sign::Neg };

        let (e1, m1_opt) = self.normalize()?;
        let m1_normalized = m1_opt.as_ref().unwrap_or(&self.m);
        let (e2, m2_opt) = d2.normalize()?;
        let m2_normalized = m2_opt.as_ref().unwrap_or(&d2.m);

        let (e_shift, mut m3) = m1_normalized.mul(m2_normalized, rm, s == Sign::Pos, full_prec)?;

        let mut e = e1 + e2 - e_shift as isize;
        if e > EXPONENT_MAX as isize {
            return Err(Error::ExponentOverflow(s));
        }
        if e < EXPONENT_MIN as isize {
            if !Self::process_subnormal(&mut m3, &mut e, rm, s == Sign::Pos) {
                return Self::new(self.m.max_bit_len());
            }
        }

        let ret = BigFloatNumber {
            m: m3,
            s,
            e: e as Exponent,
        };

        Ok(ret)
    }

    /// Divides `self` by `d2` and returns the result of the operation rounded according to `rm`. The resulting precision is equal to the highest precision of the two operands.
    /// 
    /// ## Errors
    /// 
    ///  - DivisionByZero - `d2` is zero.
    ///  - ExponentOverflow - the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn div(&self, d2: &Self, rm: RoundingMode) -> Result<Self, Error> {

        if d2.m.is_zero() {
            return Err(Error::DivisionByZero);
        }

        if self.m.is_zero() {
            return Self::new(self.m.max_bit_len().max(d2.m.max_bit_len())); // self / d2 = 0
        }

        let s = if self.s == d2.s { Sign::Pos } else { Sign::Neg };

        let (e1, m1_opt) = self.normalize()?;
        let m1_normalized = m1_opt.as_ref().unwrap_or(&self.m);
        let (e2, m2_opt) = d2.normalize()?;
        let m2_normalized = m2_opt.as_ref().unwrap_or(&d2.m);

        let (e_shift, mut m3) = m1_normalized.div(m2_normalized, rm, s == Sign::Pos)?;

        let mut e = e1 - e2 + e_shift as isize;
        if e > EXPONENT_MAX as isize {
            return Err(Error::ExponentOverflow(s));
        }
        if e < EXPONENT_MIN as isize {
            if !Self::process_subnormal(&mut m3, &mut e, rm, s == Sign::Pos) {
                return Self::new(self.m.max_bit_len());
            }
        }

        let ret = BigFloatNumber {
            m: m3,
            s,
            e: e as Exponent,
        };

        Ok(ret)
    }

    // Return normilized mantissa and exponent with corresponding shift.
    fn normalize(&self) -> Result<(isize, Option<Mantissa>), Error> {

        if self.is_subnormal() {

            let (shift, mantissa) = self.m.normilize()?;

            debug_assert!(shift < (isize::MAX/2 + EXPONENT_MIN as isize) as usize);

            if (self.e as isize) - shift as isize <= isize::MIN/2 {
                return Err(Error::ExponentOverflow(self.s));
            }

            Ok((self.e as isize - shift as isize, Some(mantissa)))

        } else {

            Ok((self.e as isize, None))
        }
    }


    // Combined add and sub operations.
    fn add_sub(&self, d2: &Self, op: i8, rm: RoundingMode, full_prec: bool) -> Result<Self, Error> {

        let mut d3 = Self::new(0)?;

        // one of the args is zero
        if self.m.is_zero() {

            let mut ret = if op < 0 {
                d2.neg()
            } else {
                d2.clone()
            }?;

            ret.set_precision(self.m.max_bit_len().max(d2.m.max_bit_len()), RoundingMode::None)?;

            return Ok(ret);
        }

        if d2.m.is_zero() {

            let mut ret = self.clone()?;

            ret.set_precision(self.m.max_bit_len().max(d2.m.max_bit_len()), RoundingMode::None)?;

            return Ok(ret);
        }

        let (e1, m1_opt) = self.normalize()?;
        let m1 = m1_opt.as_ref().unwrap_or(&self.m);
        let (e2, m2_opt) = d2.normalize()?;
        let m2 = m2_opt.as_ref().unwrap_or(&d2.m);

        let mut e;
        if (self.s != d2.s && op >= 0) || (op < 0 && self.s == d2.s) {
            // subtract
            let cmp = self.abs_cmp(d2);
            let (shift, mut m3) = if cmp > 0 {
                d3.s = self.s;
                e = e1;
                m1.abs_sub(m2, (e1 - e2) as usize, rm, self.is_positive(), full_prec)?
            } else if cmp < 0 {
                d3.s = if op >= 0 { d2.s } else { d2.s.invert() };
                e = e2;
                m2.abs_sub(m1, (e2 - e1) as usize, rm, self.is_positive(), full_prec)?
            } else {
                return Self::new(self.m.max_bit_len());
            };

            debug_assert!(shift as isize <= isize::MAX/2 && e >= isize::MIN/2);
            e -= shift as isize;

            if e < EXPONENT_MIN as isize {
                if !Self::process_subnormal(&mut m3, &mut e, rm, d2.is_positive()) {
                    return Self::new(self.m.max_bit_len());
                }
            }
            d3.e = e as Exponent;
            d3.m = m3;
        } else {
            // add
            d3.s = self.s;
            let (c, mut m3) = if e1 >= e2 {
                e = e1;
                m1.abs_add(m2, (e1 - e2) as usize, rm, d3.is_positive(), full_prec)
            } else {
                e = e2;
                m2.abs_add(m1, (e2 - e1) as usize, rm, d3.is_positive(), full_prec)
            }?;
            if c {
                if e == EXPONENT_MAX as isize {
                    return Err(Error::ExponentOverflow(self.s));
                }
                e += 1;
            }
            if e < EXPONENT_MIN as isize {
                if !Self::process_subnormal(&mut m3, &mut e, rm, d2.is_positive()) {
                    return Self::new(self.m.max_bit_len());
                }
            }
            d3.e = e as Exponent;
            d3.m = m3;
        }
        Ok(d3)
    }

    /// If exponent is too small try to present number in subnormal form.
    /// If sucessful return true.
    pub(super) fn process_subnormal(m3: &mut Mantissa, e: &mut isize, rm: RoundingMode, is_positive: bool) -> bool {

        debug_assert!(*e < 0);

        if (m3.max_bit_len() as isize) + *e > EXPONENT_MIN as isize {
            // subnormal

            let mut shift = (EXPONENT_MIN as isize - *e) as usize;

            if m3.round_mantissa(shift, rm, is_positive) {
                shift -= 1;
            }

            if shift > 0 {
                m3.shift_right(shift);
                m3.dec_len(shift);
            }

            *e = EXPONENT_MIN as isize;

            true

        } else {
            false
        }
    }

    /// Compares `self` to `d2`.
    /// Returns positive if `self` is greater than `d2`, negative if `self` is smaller than `d2`, 0 otherwise.
    pub fn cmp(&self, d2: &Self) -> SignedWord {
        if self.s != d2.s {
            return self.s as SignedWord;
        }

        if self.m.is_zero() || d2.m.is_zero() {
            if !d2.m.is_zero() {
                return d2.s.invert() as SignedWord;
            } else if !self.m.is_zero() {
                return self.s as SignedWord;
            } else {
                return 0;
            }
        }

        let e: isize = self.e as isize - d2.e as isize;
        if e > 0 {
            return 1*self.s as SignedWord;
        }
        if e < 0 {
            return -1*self.s as SignedWord;
        }

        self.m.abs_cmp(&d2.m) as SignedWord * self.s as SignedWord
    }

    // Compare absolute values of two numbers.
    fn abs_cmp(&self, d2: &Self) -> SignedWord {
        if self.m.is_zero() || d2.m.is_zero() {
            if !d2.m.is_zero() {
                return -1;
            } else if !self.m.is_zero() {
                return 1;
            } else {
                return 0;
            }
        }

        let e: isize = self.e as isize - d2.e as isize;
        if e > 0 {
            return 1;
        }
        if e < 0 {
            return -1;
        }

        self.m.abs_cmp(&d2.m)
    }

    /// Returns the absolute value of a number.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn abs(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        ret.s = Sign::Pos;
        Ok(ret)
    }

    /// Constructs a number with precision `p` from f64 value.
    /// 
    /// ## Errors
    /// 
    ///  - InvalidArgument - precision is incorrect or `f` is NaN.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    ///  - ExponentOverflow - `f` is Inf.
    pub fn from_f64(p: usize, mut f: f64) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        let mut ret = BigFloatNumber::new(0)?;
        if f == 0.0f64 {
            return Ok(ret);
        }
        if f.is_infinite() {
            return Err(Error::ExponentOverflow(if f.is_sign_negative() {Sign::Neg} else {Sign::Pos}));
        }
        if f.is_nan() {
            return Err(Error::InvalidArgument);
        }
        if f < 0.0f64 {
            ret.s = Sign::Neg;
            f = -f;
        }

        let ptr: * const f64 = &f;
        let u = unsafe {*(ptr as *const u64)};
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

        Ok(ret)
    }

    /// Converts a number to f64 value.
    #[allow(dead_code)] // TODO: add rounding.
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
                let p: * const u64 = &ret;
                unsafe { *(p as * const f64) }
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
            let p: * const u64 = &ret;
            unsafe { *(p as * const f64) }
        }
    }

    /// Constructs a number with precision `p` from f32 value.
    /// 
    /// ## Errors
    /// 
    ///  - InvalidArgument - precision is incorrect or `f` is NaN.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    ///  - ExponentOverflow - `f` is Inf.
    #[inline]
    pub fn from_f32(p: usize, f: f32) -> Result<Self, Error> {
        Self::from_f64(p, f as f64)
    }

    /// Convert to f32.
    #[inline]
    #[allow(dead_code)] // TODO: add rounding.
    pub(crate) fn to_f32(&self) -> f32 {
        self.to_f64() as f32
    }

    /// Returns true if `self` is subnormal. A number is subnormal if the most significant bit of the mantissa is not equal to 1.
    #[inline]
    pub fn is_subnormal(&self) -> bool {
        self.m.is_subnormal()
    }

    /// Decomposes `self` into raw parts. The function returns a reference to a slice of words representing mantissa, numbers of significant bits in the mantissa, sign, and exponent. 
    #[inline]
    pub fn to_raw_parts(&self) -> (&[Word], usize, Sign, Exponent) {
        let (m, n) = self.m.to_raw_parts();
        (m, n, self.s, self.e)
    }

    /// Constructs a number from the raw parts:
    /// 
    ///  - `m` is the mantisaa.
    ///  - `n` is the number of significant bits in mantissa.
    ///  - `s` is the sign.
    ///  - `e` is the exponent.
    pub fn from_raw_parts(m: &[Word], n: usize, s: Sign, e: Exponent) -> Result<Self, Error> {
        if m.len()*WORD_BIT_SIZE >= isize::MAX as usize/2 || n > m.len()*WORD_BIT_SIZE {
            return Err(Error::InvalidArgument);
        }
        Ok(BigFloatNumber { e, s, m: Mantissa::from_raw_parts(m, n)? })
    }

    /// Returns sign of a number.
    #[inline]
    pub fn get_sign(&self) -> Sign {
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
    pub fn get_exponent(&self) -> Exponent {
        self.e
    }

    // Return true if `self` is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.m.is_zero()
    }

    /// Returns the largest integer less than or equal to `self`.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn floor(&self) -> Result<Self, Error> {
        let int = self.int()?;
        if self.is_negative() {
            if !self.fract()?.m.is_zero() {
                return int.sub(&ONE, RoundingMode::ToZero);
            }
        }
        Ok(int)
    }

    /// Returns the smallest integer greater than or equal to `self`.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn ceil(&self) -> Result<Self, Error> {
        let int = self.int()?;
        if self.is_positive() {
            if !self.fract()?.m.is_zero() {
                return int.add(&ONE, RoundingMode::ToZero);
            }
        }
        Ok(int)
    }

    /// Returns fractional part of a number.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn fract(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        if self.e > 0 {
            if (self.e as usize) < self.m.max_bit_len() {
                // remove integer part of mantissa & normalize at the same time
                if let Some(shift) = self.m.find_one_from(self.e as usize) {
                    ret.m.shift_left(shift);
                    ret.e = -((shift - self.e as usize) as Exponent);
                } else {
                    return Self::new(self.m.max_bit_len())
                }
            } else {
                return Self::new(self.m.max_bit_len())
            }
        }
        Ok(ret)
    }

    /// Returns integer part of a number.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn int(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        if self.e > 0 {
            if (self.e as usize) < self.m.max_bit_len() {
                ret.m.mask_bits(self.m.max_bit_len() - self.e as usize)
            }
            return Ok(ret);
        }
        Self::new(self.m.max_bit_len())
    }

    /// Returns integer part as a word.
    pub(crate) fn get_int_as_word(&self) -> Word {
        if self.e > 0 && WORD_BIT_SIZE > self.e as usize {
            let d = self.m.get_most_significant_word();
            let shift = WORD_BIT_SIZE - self.e as usize;
            d >> shift
        } else {
            0
        }
    }

    /// Returns integer part of a number as built-in integer.
    pub(super) fn get_int_as_usize(&self) -> Result<usize, Error> {
        if self.e > 0 {
            debug_assert!(core::mem::size_of::<usize>() >= core::mem::size_of::<Word>());
            if (self.e as usize) <= WORD_BIT_SIZE {
                let shift = WORD_BIT_SIZE - self.e as usize;
                let ret = self.m.get_most_significant_word() as usize;
                Ok(ret >> shift)
            } else {
                Err(Error::InvalidArgument)
            }
        } else {
            Ok(0)
        }
    }

    /// Sets the exponent of `self`.
    #[inline]
    pub fn set_exponent(&mut self, e: Exponent) {
        self.e = e;
    }

    /// Returns the maximum mantissa length of `self` in bits.
    #[inline]
    pub fn get_mantissa_max_bit_len(&self) -> usize {
        self.m.max_bit_len()
    }

    /// Returns the rounded number with `n` binary positions in the fractional part of the number using rounding mode `rm`.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    ///  - ExponentOverflow - rounding causes exponent overflow.
    pub fn round(&mut self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        let e = (-self.e) as usize;
        if self.e < 0 && e > n {
            let m = e - n;
            if m > self.m.max_bit_len() {
                return Self::new(self.m.max_bit_len());
            } else {
                if self.m.round_mantissa(m, rm, self.is_positive()) {
                    if ret.e == EXPONENT_MAX {
                        return Err(Error::ExponentOverflow(ret.s));
                    }
                    ret.e += 1;
                }
                if ret.m.is_all_zero() {
                    return Self::new(self.m.max_bit_len());
                }
            }
        }
        Ok(ret)
    }

    #[cfg(feature="random")]
    /// Generates a random normal number with precision `p` and an exponent within the range from `exp_from` to `exp_to`.
    /// 
    /// ## Errors
    /// 
    ///  - InvalidArgument - precision is incorrect.
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn random_normal(p: usize, exp_from: Exponent, exp_to: Exponent) -> Result<Self, Error> {
        Self::p_assertion(p)?;
        let m = Mantissa::random_normal(p)?;
        let e = if exp_from < exp_to {
            (rand::random::<isize>().abs() % (exp_to as isize - exp_from as isize) 
                + exp_from as isize) as Exponent
        } else {
            exp_from
        };
        let s = if rand::random::<u8>() & 1 == 0 {Sign::Pos} else {Sign::Neg};
        Ok(BigFloatNumber { e, s, m })
    }

    /// Clones the number.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    pub fn clone(&self) -> Result<Self, Error> {
        Ok(BigFloatNumber {
            e: self.e, 
            s: self.s, 
            m: self.m.clone()? 
        })
    }

    /// Sets the precision of `self` to `p`.
    /// If the new precision is smaller than the existing, the number is rounded using specified rounding mode `rm`; the precision is not decreased.
    pub fn set_precision(&mut self, p: usize, rm: RoundingMode) -> Result<(), Error> {
        if self.get_mantissa_max_bit_len() > p {
            self.m.round_mantissa(self.get_mantissa_max_bit_len() - p, rm, self.is_positive());
            if self.m.is_all_zero() {
                self.m.set_zero();
                self.e = 0;
            }
        }
        self.m.set_length(p)
    }

    /// Computes the reciprocal of a number. The result is rounded using rounding mode `rm`.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation - failed to allocate memory for mantissa.
    ///  - ExponentOverflow - rounding causes exponent overflow.
    pub fn reciprocal(&self, rm: RoundingMode) -> Result<Self, Error> {
        let mut p = self.get_mantissa_max_bit_len();
        let mut err = 1;
        while p > 500 {
            p >>= 1;
            err += 5;
        }

        let e = self.get_exponent();
        let mut x = self.clone()?;
        x.set_exponent(0);
        x.set_precision(x.get_mantissa_max_bit_len() + err, RoundingMode::None)?;
        let mut ret= x.recip_iter()?;
        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;
        if ret.get_exponent() as isize - e as isize > EXPONENT_MAX as isize || 
            (ret.get_exponent() as isize - e as isize) < EXPONENT_MIN as isize {
            return Err(Error::ExponentOverflow(ret.s));
        }
        ret.set_exponent(ret.get_exponent()-e);
        Ok(ret)
    }

    // reciprocal computation.
    fn recip_iter(&self) -> Result<Self, Error> {

        if self.m.len() <= 500 {

            ONE.div(self, RoundingMode::None)

        } else {
            
            //  Newton's method: x(n+1) = 2*x(n) - self*x(n)*x(n)
            let prec = self.get_mantissa_max_bit_len();
            let mut x = self.clone()?;
            x.set_precision(prec / 2, RoundingMode::None)?;
            let mut ret= x.recip_iter()?;
            ret.set_precision(prec, RoundingMode::None)?;

            // one iteration
            let d = ret.mul(self, RoundingMode::None)?;
            let dx = d.mul(&ret, RoundingMode::None)?;
            if ret.get_exponent() == EXPONENT_MAX {
                return Err(Error::ExponentOverflow(ret.s));
            }
            ret.set_exponent(ret.get_exponent() + 1);
            ret = ret.sub(&dx, RoundingMode::None)?;

            Ok(ret)
        }
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
        })
    }

    /// Returns the raw mantissa words of a number.
    pub fn get_mantissa_digits(&self) -> &[Word] {
        self.m.get_digits()
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use rand::random;

    #[test]
    fn test_number() {

        let p = 160; // 10 of words
        let rm = RoundingMode::ToEven;

        let mut d1;
        let mut d2;
        let mut d3;
        let mut ref_num;
        let mut eps = ONE.clone().unwrap();

        //let n1 = BigFloatNumber::from_raw_parts(&[4165624164, 2129500405, 2551748857, 998953334, 3485534795, 1427512576, 426727679, 2298894833, 2107497530, 385370716, 2626967463, 2694802314, 2373730166], 416, Sign::Neg, 301499356).unwrap();

        // inf
        assert!(BigFloatNumber::from_f64(p, f64::INFINITY).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        assert!(BigFloatNumber::from_f64(p, f64::NEG_INFINITY).unwrap_err() == Error::ExponentOverflow(Sign::Neg));

        // nan
        assert!(BigFloatNumber::from_f64(p, f64::NAN).unwrap_err() == Error::InvalidArgument);

        // 0.0
        assert!(BigFloatNumber::from_f64(p, 0.0).unwrap().to_f64() == 0.0);

        // conversions
        for _ in 0..10000 {
            let f: f64 = random_f64();
            if f.is_finite() {
                d1 = BigFloatNumber::from_f64(p, f).unwrap();
                assert!(d1.to_f64() == f);
                d1 = BigFloatNumber::from_f32(p, f as f32).unwrap();
                assert!(d1.to_f32() == f as f32);
            }
        }

        // 0 * 0
        d1 = BigFloatNumber::new(p).unwrap();
        d2 = BigFloatNumber::new(p).unwrap();
        ref_num = BigFloatNumber::new(p).unwrap();
        d3 = d1.mul(&d2, rm).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0.99 * 0
        d1 = BigFloatNumber::from_f64(p, 0.99).unwrap();
        d3 = d1.mul(&d2, rm).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 * 12349999
        d1 = BigFloatNumber::new(p).unwrap();
        d2 = BigFloatNumber::from_f64(p, 12349999.0).unwrap();
        d3 = d1.mul(&d2, rm).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * 1
        d1 = BigFloatNumber::from_f64(p, 1.0).unwrap();
        d2 = BigFloatNumber::from_f64(p, 1.0).unwrap();
        d3 = d1.mul(&d2, rm).unwrap();
        assert!(d3.cmp(&d1) == 0);

        // 1 * -1
        d1 = BigFloatNumber::from_f64(p, 1.0).unwrap();
        d2 = BigFloatNumber::from_f64(p, 1.0).unwrap().neg().unwrap();
        d3 = d1.mul(&d2, rm).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * 1
        d3 = d2.mul(&d1, rm).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * -1
        d1 = d1.neg().unwrap();
        d3 = d1.mul(&d2, rm).unwrap();
        ref_num = BigFloatNumber::from_f64(p, 1.0).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / 0 
        d1 = BigFloatNumber::new(p).unwrap();
        d2 = BigFloatNumber::new(p).unwrap();
        assert!(d1.div(&d2, rm).unwrap_err() == Error::DivisionByZero);

        // d2 / 0
        d2 = BigFloatNumber::from_f64(p, 123.0).unwrap();
        assert!(d2.div(&d1, rm).unwrap_err() == Error::DivisionByZero);

        // 0 / d2
        d3 = d1.div(&d2, rm).unwrap();
        ref_num = BigFloatNumber::new(p).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / -d2
        d2 = d2.neg().unwrap();
        d3 = d1.div(&d2, rm).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // add & sub & cmp
        for _ in 0..10000 {
            // avoid subnormal numbers
            d1 = BigFloatNumber::random_normal(160, -80, 80).unwrap();
            d2 = BigFloatNumber::random_normal(160, -80, 80).unwrap();
            let d3 = d1.sub(&d2, RoundingMode::ToEven).unwrap();
            let d4 = d3.add(&d2, RoundingMode::ToEven).unwrap();
            eps.set_exponent(d1.get_exponent().max(d2.get_exponent()) - 158);
            //println!("\n=== res \n{:?} \n{:?} \n{:?} \n{:?} \n{:?} \n{:?}", d1, d2, d3, d4, d1.sub(&d4, RoundingMode::ToEven).unwrap().abs().unwrap(), eps);
            assert!(d1.sub(&d4, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);
        }

        for _ in 0..1000 {
            d1 = BigFloatNumber::random_normal(160, -80, 80).unwrap();
            d2 = BigFloatNumber::random_normal(160, -80, 80).unwrap();
            let d3 = d1.sub_full_prec(&d2).unwrap();
            let d4 = d3.add_full_prec(&d2).unwrap();
            //println!("\n=== res \n{:?} \n{:?} \n{:?} \n{:?} \n{:?} \n{:?}", d1, d2, d3, d4, d1.sub(&d4, RoundingMode::ToEven).unwrap().abs().unwrap(), eps);
            assert!(d1.cmp(&d4) == 0);
        }

        // mul & div
        for _ in 0..10000 {
            // avoid subnormal numbers
            d1 = BigFloatNumber::random_normal(160, EXPONENT_MIN/2+160, EXPONENT_MAX/2).unwrap();
            d2 = BigFloatNumber::random_normal(160, EXPONENT_MIN/2, EXPONENT_MAX/2).unwrap();
            if !d2.is_zero() {
                let d3 = d1.div(&d2, RoundingMode::ToEven).unwrap();
                let d4 = d3.mul(&d2, RoundingMode::ToEven).unwrap();
                eps.set_exponent(d1.get_exponent() - 158);
                //println!("\n{:?}\n{:?}\n{:?}\n{:?}", d1,d2,d3,d4);
                assert!(d1.sub(&d4, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);
            }
        }

        for _ in 0..10000 {
            // avoid subnormal numbers
            d1 = BigFloatNumber::random_normal(128, EXPONENT_MIN/2+128, EXPONENT_MAX/2).unwrap();
            d2 = BigFloatNumber::random_normal(128, EXPONENT_MIN/2, EXPONENT_MAX/2).unwrap();
            if !d2.is_zero() {
                let d3 = d1.mul_full_prec(&d2).unwrap();
                d1.set_precision(256, rm).unwrap();
                let d4 = d1.mul(&d2, rm).unwrap();
                eps.set_exponent(d1.get_exponent() - 126);
                //println!("\n{:?}\n{:?}\n{:?}\n{:?}", d1,d2,d3,d4);
                assert!(d3.cmp(&d4) == 0);
            }
        }

        // large mantissa
        for _ in 0..20 {
            // avoid subnormal numbers
            d1 = BigFloatNumber::random_normal(32000, EXPONENT_MIN/2+32000, EXPONENT_MAX/2).unwrap();
            d2 = BigFloatNumber::random_normal(32000, EXPONENT_MIN/2, EXPONENT_MAX/2).unwrap();
            if !d2.is_zero() {
                let d3 = d1.div(&d2, RoundingMode::ToEven).unwrap();
                let d4 = d3.mul(&d2, RoundingMode::ToEven).unwrap();
                eps.set_exponent(d1.get_exponent() - 31998);
                assert!(d1.sub(&d4, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);
            }
        }

        // reciprocal
        for _ in 0..100 {
            // avoid subnormal numbers
            d1 = BigFloatNumber::random_normal(3200, EXPONENT_MIN/2+3200, EXPONENT_MAX/2).unwrap();
            if !d1.is_zero() {
                let d3 = d1.reciprocal(rm).unwrap();
                let d4 = ONE.div(&d3, rm).unwrap();
                eps.set_exponent(d1.get_exponent() - 3200 + 2);
                //println!("{:?} {:?} {:?}", d1, d3, d4);
                assert!(d1.sub(&d4, rm).unwrap().abs().unwrap().cmp(&eps) < 0);
            }
        }

        // subnormal numbers
        d1 = BigFloatNumber::min_positive(p).unwrap();
        d2 = BigFloatNumber::min_positive(p).unwrap();
        ref_num = BigFloatNumber::min_positive(p).unwrap();
        let one  = BigFloatNumber::from_word(1, p).unwrap();
        ref_num = ref_num.mul(&one.add(&one, rm).unwrap(), rm).unwrap();

        // min_positive + min_positive = 2*min_positive
        assert!(d1.add(&d2, rm).unwrap().cmp(&ref_num) == 0);
        assert!(d1.add(&d2, rm).unwrap().cmp(&d1) > 0);
        assert!(d1.cmp(&d1.add(&d2, rm).unwrap()) < 0);

        // min_positive - min_positive = 0
        ref_num = BigFloatNumber::new(p).unwrap();
        assert!(d1.sub(&d2, rm).unwrap().cmp(&ref_num) == 0);

        // 1 * min_positive = min_positive
        assert!(one.mul(&d2, rm).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&one, rm).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&one, rm).unwrap().cmp(&d2) == 0);

        // normal -> subnormal -> normal
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MIN;
        d2 = BigFloatNumber::min_positive(p).unwrap();
        assert!(!d1.is_subnormal());
        assert!(d1.sub(&d2, rm).unwrap().cmp(&d1) < 0);
        assert!(d1.cmp(&d1.sub(&d2, rm).unwrap()) > 0);
        d1 = d1.sub(&d2, rm).unwrap();
        assert!(d1.is_subnormal());
        d1 = d1.add(&d2, rm).unwrap();
        assert!(!d1.is_subnormal());

        // overflow
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MAX - (d1.m.max_bit_len() - 1) as Exponent;
        assert!(BigFloatNumber::max(p).unwrap().add(&d1, rm).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        assert!(BigFloatNumber::min(p).unwrap().sub(&d1, rm).unwrap_err() == Error::ExponentOverflow(Sign::Neg));
        assert!(BigFloatNumber::max(p).unwrap().mul(&BigFloatNumber::max(p).unwrap(), rm)
            .unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MIN;
        assert!(BigFloatNumber::max(p).unwrap().div(&d1, rm).unwrap_err() == Error::ExponentOverflow(Sign::Pos));

        // decompose and compose
        let f1 = random_f64_exp(50, 25);
        d1 = BigFloatNumber::from_f64(p, f1).unwrap();
        let (m,n,s,e) = d1.to_raw_parts();
        d2 = BigFloatNumber::from_raw_parts(m, n, s, e).unwrap();
        assert!(d1.cmp(&d2) == 0);

        // sign and exponent
        d1 = one.clone().unwrap();
        assert!(d1.get_sign() == Sign::Pos);
        assert!(d1.is_positive());
        d1 = d1.neg().unwrap();
        assert!(d1.get_sign() == Sign::Neg);
        assert!(d1.is_negative());
        assert!(d1.get_exponent() == 1);

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

        assert!(BigFloatNumber::min_positive(p).unwrap().fract().unwrap().cmp(&BigFloatNumber::min_positive(p).unwrap()) == 0);
        assert!(BigFloatNumber::min_positive(p).unwrap().int().unwrap().is_zero());

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

    #[ignore]
    #[test]
    fn add_sub_perf() {
        let mut n = vec![];
        for _ in 0..1000000 {
            n.push(BigFloatNumber::random_normal(132, -20, 20).unwrap());
        }

        for _ in 0..5 {

            let start_time = std::time::Instant::now();
            let mut f = n[0].clone().unwrap();

            for (i, ni) in n.iter().enumerate().skip(1) {
                if i & 1 == 0 {
                    f = f.add(ni, RoundingMode::ToEven).unwrap();
                } else {
                    f = f.sub(ni, RoundingMode::ToEven).unwrap();
                }
            }

            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }

    }

    #[ignore]
    #[test]
    fn recip_perf() {

        for _ in 0..5 {    

            let mut n = vec![];
            for _ in 0..1000 {
                n.push(BigFloatNumber::random_normal(32*450, -20, 20).unwrap());
            }

            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ONE.div(ni, RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("div {}", time.as_millis());

            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.reciprocal(RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("recip {}", time.as_millis());
        }
    }

    #[ignore]
    #[test]
    fn recip_mul_perf() {

        for _ in 0..5 {

            let mut n = vec![];
            for _ in 0..1000 {
                n.push(BigFloatNumber::random_normal(1000*32, -20, 20).unwrap());
            }

            let f1 = n[0].clone().unwrap();

            let start_time = std::time::Instant::now();
            for ni in n.iter().skip(1) {
                let f = f1.reciprocal(RoundingMode::None).unwrap();
                let _f = f.mul(ni, RoundingMode::None).unwrap();
            }
            let time = start_time.elapsed();
            println!("recip {}", time.as_millis());

            let start_time = std::time::Instant::now();
            for ni in n.iter().skip(1) {
                let _f = ni.div(&f1, RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("div {}", time.as_millis());
        }
    }
}