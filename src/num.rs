//! BigFloatNumber definition and basic arithmetic, comparison, and number manipulation operations.

use crate::defs::Exponent;
use crate::defs::Sign;
use crate::defs::Digit;
use crate::defs::Error;
use crate::defs::DoubleExponent;
use crate::defs::EXPONENT_MAX;
use crate::defs::EXPONENT_MIN;
use crate::defs::RoundingMode;
use crate::defs::DIGIT_BIT_SIZE;
use crate::mantissa::Mantissa;


/// BigFloatNumber represents floating point number with mantissa of a fixed size, and exponent.
#[derive(Debug)]
pub struct BigFloatNumber {
    e: Exponent,
    s: Sign,
    m: Mantissa,
}

/// Low-level operations on a number.
impl BigFloatNumber {

    /// Returns new number with value of 0.
    pub fn new(p: usize) -> Result<Self, Error>  {
        Ok(BigFloatNumber {
            m: Mantissa::new(p)?,
            e: 0,
            s: Sign::Pos,
        })
    }

    /// Returns maximum value.
    pub fn max(p: usize) -> Result<Self, Error> {
        Ok(BigFloatNumber {
            m: Mantissa::oned_mantissa(p)?,
            e: EXPONENT_MAX,
            s: Sign::Pos,
        })
    }

    /// Returns minimum value.
    pub fn min(p: usize) -> Result<Self, Error> {
        Ok(BigFloatNumber {
            m: Mantissa::oned_mantissa(p)?,
            e: EXPONENT_MAX,
            s: Sign::Neg,
        })
    }

    /// Returns minimum positive subnormal value.
    pub fn min_positive(p: usize) -> Result<Self, Error> {
        Ok(BigFloatNumber {
            m: Mantissa::min(p)?,
            e: EXPONENT_MIN,
            s: Sign::Pos,
        })
    }

    /// Returns new number with value of 1.
    pub fn one(p: usize) -> Result<Self, Error> {
        Ok(BigFloatNumber {
            m: Mantissa::one(p)?,
            e: 1,
            s: Sign::Pos,
        })
    }

    /// Returns new number with value of 10.
    pub fn ten(p: usize) -> Result<Self, Error> {
        Ok(BigFloatNumber {
            m: Mantissa::ten(p)?,
            e: 4,
            s: Sign::Pos,
        })
    }

    /// Summation operation.
    pub fn add(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, 1)
    }

    /// Negation operation.
    pub fn neg(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        ret.s = ret.s.invert();
        Ok(ret)
    }

    /// Subtraction operation.
    pub fn sub(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, -1)
    }

    /// Multiplication operation.
    pub fn mul(&self, d2: &Self) -> Result<Self, Error> {
        if self.m.is_zero() || d2.m.is_zero() {
            return Self::new(self.m.max_bit_len())
        }

        let (e1, m1_normalized) = self.normalized()?;
        let (e2, m2_normalized) = d2.normalized()?;

        let (e_shift, mut m3) = m1_normalized.mul(&m2_normalized)?;

        let s = if self.s == d2.s { Sign::Pos } else {Sign::Neg};
        let mut e = e1 + e2 - e_shift as DoubleExponent;
        if e > EXPONENT_MAX as DoubleExponent {
            return Err(Error::ExponentOverflow(s));
        }

        if e < EXPONENT_MIN as DoubleExponent {
            if !Self::process_subnormal(&mut m3, &mut e) {
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

    /// Return reciprocal.
    pub fn recip(&self) -> Result<Self, Error> {
        Self::one(self.m.max_bit_len())?.div(self)
    }

    /// division operation.
    pub fn div(&self, d2: &Self) -> Result<Self, Error> {

        if d2.m.is_zero() {
            return Err(Error::DivisionByZero);
        }

        if self.m.is_zero() {
            return Self::new(self.m.max_bit_len()); // self / d2 = 0
        }

        let (e1, m1_normalized) = self.normalized()?;
        let (e2, m2_normalized) = d2.normalized()?;

        let mut m3 = m1_normalized.div(&m2_normalized)?;

        let cmp = m1_normalized.abs_cmp(&m2_normalized);
        let shift= if cmp >= 0 {
            1
        } else {
            0
        };

        let s = if self.s == d2.s { Sign::Pos } else {Sign::Neg};
        let mut e = e1 - e2 + shift as DoubleExponent;

        if e > EXPONENT_MAX as DoubleExponent {
            return Err(Error::ExponentOverflow(s));
        }
        if e < EXPONENT_MIN as DoubleExponent {
            if !Self::process_subnormal(&mut m3, &mut e) {
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

    /// Fast division by 2.
    pub fn div_by_2(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        if self.m.is_zero() {
            return Ok(ret);
        }
        if ret.e > EXPONENT_MIN {
            ret.e -= 1;
        } else {
            ret.m.shift_right(1);
            ret.m.dec_len(1);
        }
        Ok(ret)
    }

    /// Return normilized mantissa and exponent with corresponding shift.
    fn normalized(&self) -> Result<(DoubleExponent, Mantissa), Error> {
        Ok(if self.m.is_subnormal() {
            let (shift, mantissa) = self.m.normilize()?;
            (self.e as DoubleExponent - shift as DoubleExponent, mantissa)
        } else {
            (self.e as DoubleExponent, self.m.clone()?)
        })
    }

    /// Combined add and sub operations.
    fn add_sub(&self, d2: &Self, op: i8) -> Result<Self, Error> {
        let mut d3 = Self::new(self.m.max_bit_len())?;

        // one of the numbers is zero
        if self.m.is_zero() {
            if op < 0 {
                return d2.neg();
            } else {
                return d2.clone()
            }
        }
        if d2.m.is_zero() {
            return self.clone();
        }

        let (e1, mut m1) = self.normalized()?;
        let (e2, mut m2) = d2.normalized()?;

        // shift manitissa of the smaller number.
        let mut e = if e1 >= e2 {
            m2.shift_right((e1 - e2) as usize);
            e1
        } else {
            m1.shift_right((e2 - e1) as usize);
            e2
        };

        if (self.s != d2.s && op >= 0) || (op < 0 && self.s == d2.s) {
            // subtract
            let cmp = m1.abs_cmp(&m2);
            let (shift, mut m3) = if cmp > 0 {
                d3.s = self.s;
                m1.abs_sub(&m2)?
            } else if cmp < 0 {
                d3.s = if op >= 0 { d2.s } else { d2.s.invert() };
                m2.abs_sub(&m1)?
            } else {
                return Self::new(self.m.max_bit_len());
            };
            e -= shift as DoubleExponent;
            if e < EXPONENT_MIN as DoubleExponent {
                if !Self::process_subnormal(&mut m3, &mut e) {
                    return Self::new(self.m.max_bit_len());
                }
            }
            d3.e = e as Exponent;
            d3.m = m3;
        } else {
            // add
            d3.s = self.s;
            let (c, mut m3) = m1.abs_add(&m2)?;
            if c {
                if e == EXPONENT_MAX as DoubleExponent {
                    return Err(Error::ExponentOverflow(self.s));
                }
                e += 1;
            }
            if e < EXPONENT_MIN as DoubleExponent {
                if !Self::process_subnormal(&mut m3, &mut e) {
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
    fn process_subnormal(m3: &mut Mantissa, e: &mut DoubleExponent) -> bool {
        if (m3.max_bit_len() as DoubleExponent) + *e > EXPONENT_MIN as DoubleExponent {
            // subnormal
            let shift = EXPONENT_MIN as DoubleExponent - *e;
            m3.shift_right(shift as usize);
            m3.dec_len(shift as usize);
            *e = EXPONENT_MIN as DoubleExponent;
            true
        } else {
            false
        }
    }

    /// Compare to d2.
    /// Returns positive if self > d2, negative if self < d2, 0 otherwise.
    pub fn cmp(&self, d2: &Self) -> i32 {
        if self.s != d2.s {
            return self.s as i32;
        }

        if self.m.is_zero() || d2.m.is_zero() {
            if !d2.m.is_zero() {
                return d2.s.invert() as i32;
            } else if !self.m.is_zero() {
                return self.s as i32;
            } else {
                return 0;
            }
        }

        let e: DoubleExponent = self.e as DoubleExponent - d2.e as DoubleExponent;
        if e > 0 {
            return 1*self.s as i32;
        }
        if e < 0 {
            return -1*self.s as i32;
        }

        self.m.abs_cmp(&d2.m) as i32 * self.s as i32
    }

    /// Return absolute value of a number.
    pub fn abs(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        ret.s = Sign::Pos;
        Ok(ret)
    }

    /// Construct from f64.
    pub fn from_f64(p: usize, mut f: f64) -> Result<Self, Error> {
        let mut ret = BigFloatNumber::new(p)?;
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
        ret.e = exponent - 0b1111111111 - shift;

        Ok(ret)
    }

    /// Convert to f64.
    pub fn to_f64(&self) -> f64 {
        if self.m.is_zero() {
            return 0.0;
        }
        let mantissa = self.m.to_u64();
        let mut e: DoubleExponent = self.e as DoubleExponent + 0b1111111111;
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

    /// Construct from f32.
    pub fn from_f32(p: usize, f: f32) -> Result<Self, Error> {
        Self::from_f64(p, f as f64)
    }

    /// Convert to f32.
    pub fn to_f32(&self) -> f32 {
        self.to_f64() as f32
    }

    /// Return true if number is subnormal.
    pub fn is_subnormal(&self) -> bool {
        self.m.is_subnormal()
    }

    /// Decompose to raw parts.
    pub fn to_raw_parts(&self) -> (&[Digit], usize, Sign, Exponent) {
        let (m, n) = self.m.to_raw_parts();
        (m, n, self.s, self.e)
    }

    /// Construct from raw parts.
    pub fn from_raw_parts(m: &[Digit], n: usize, s: Sign, e: Exponent) -> Result<Self, Error> {
        Ok(BigFloatNumber { e, s, m: Mantissa::from_raw_parts(m, n)? })
    }

    /// Returns sign of a number.
    pub fn get_sign(&self) -> Sign {
        self.s
    }

    /// Returns true if number is positive.
    pub fn is_positive(&self) -> bool {
        self.s == Sign::Pos
    }

    /// Returns true if number is negative.
    pub fn is_negative(&self) -> bool {
        self.s == Sign::Neg
    }

    /// Returns exponent of a number.
    pub fn get_exponent(&self) -> Exponent {
        self.e
    }

    // Return true if number is zero.
    pub fn is_zero(&self) -> bool {
        self.m.is_zero()
    }

    /// Returns the largest integer less than or equal to a number.
    pub fn floor(&self) -> Result<Self, Error> {
        let int = self.int()?;
        if self.is_negative() {
            if !self.fract()?.m.is_zero() {
                let one = Self::one(self.m.max_bit_len())?;
                return int.sub(&one);
            }
        }
        Ok(int)
    }

    /// Returns the smallest integer greater than or equal to a number.
    pub fn ceil(&self) -> Result<Self, Error> {
        let int = self.int()?;
        if self.is_positive() {
            if !self.fract()?.m.is_zero() {
                let one = Self::one(self.m.max_bit_len())?;
                return int.add(&one);
            }
        }
        Ok(int)
    }

    /// Return fractional part of a number.
    pub fn fract(&self) -> Result<Self, Error> {
        let mut ret = self.clone()?;
        if self.e > 0 {
            if (self.e as usize) < self.m.max_bit_len() {
                // remove integer part of mantissa & normalize at the same time
                ret.m.shift_left(self.e as usize);
                if ret.m.is_all_zero() {
                    return Self::new(self.m.max_bit_len())
                }
                ret.e = 0;
            } else {
                return Self::new(self.m.max_bit_len())
            }
        }
        Ok(ret)
    }

    /// Return integer part of a number.
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

    /// Sets exponent part of the number.
    pub fn set_exponent(&mut self, e: Exponent) {
        self.e = e;
    }

    /// Returns maximum mantissa length in bits.
    pub fn get_mantissa_max_bit_len(&self) -> usize {
        self.m.max_bit_len()
    }

    // Returns integer part as a digit.
    pub fn get_int_as_digit(&self) -> Digit {
        if self.e > 0 && DIGIT_BIT_SIZE > self.e as usize {
            let d = self.m.get_most_significant_digit();
            let shift = DIGIT_BIT_SIZE - self.e as usize;
            d >> shift
        } else {
            0
        }
    }

    /// Returns the rounded number with `n` decimal positions in the fractional part of the number using rounding mode `rm`.
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
    /// Generate random normal float value with exponent being in the specified range.
    pub fn random_normal(p: usize, exp_from: Exponent, exp_to: Exponent) -> Result<Self, Error> {
        let m = Mantissa::random_normal(p)?;
        let e = if exp_from < exp_to {
            (rand::random::<DoubleExponent>().abs() % (exp_to as DoubleExponent - exp_from as DoubleExponent) 
                + exp_from as DoubleExponent) as Exponent
        } else {
            exp_from
        };
        let s = if rand::random::<u8>() & 1 == 0 {Sign::Pos} else {Sign::Neg};
        Ok(BigFloatNumber { e, s, m })
    }

    /// Clones the number.
    pub fn clone(&self) -> Result<Self, Error> {
        Ok(BigFloatNumber {
            e: self.e, 
            s: self.s, 
            m: self.m.clone()? 
        })
    }

    /// Assign `self` the value of `d2`. 
    /// If d2 has more precision than `self`, then d2 will be rounded according to the rounding mode `rm`.
    pub fn assign(&mut self, d2: &Self, rm: RoundingMode) -> Result<(), Error> {
        if self.m.len() < d2.m.len() {
            let mut r = d2.clone()?;
            r.round(self.m.len(), rm)?;
            self.m.copy_from(&r.m);
        } else {
            self.m.copy_from(&d2.m);
        }
        self.e = d2.e;
        self.s = d2.s;
        Ok(())
    }
}

/// Radix
pub enum Radix {
    Bin = 2,
    Oct = 8,
    Dec = 10,
    Hex = 16,
}


#[cfg(test)]
mod tests {

    use super::*;
    use rand::random;

    #[test]
    fn test_number() {

        let p = 160; // 10 of "Digit"

        let mut d1;
        let mut d2;
        let mut d3;
        let mut ref_num;

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
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0.99 * 0
        d1 = BigFloatNumber::from_f64(p, 0.99).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 * 12349999
        d1 = BigFloatNumber::new(p).unwrap();
        d2 = BigFloatNumber::from_f64(p, 12349999.0).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * 1
        d1 = BigFloatNumber::from_f64(p, 1.0).unwrap();
        d2 = BigFloatNumber::from_f64(p, 1.0).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&d1) == 0);

        // 1 * -1
        d1 = BigFloatNumber::from_f64(p, 1.0).unwrap();
        d2 = BigFloatNumber::from_f64(p, 1.0).unwrap().neg().unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * 1
        d3 = d2.mul(&d1).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * -1
        d1 = d1.neg().unwrap();
        d3 = d1.mul(&d2).unwrap();
        ref_num = BigFloatNumber::from_f64(p, 1.0).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / 0 
        d1 = BigFloatNumber::new(p).unwrap();
        d2 = BigFloatNumber::new(p).unwrap();
        assert!(d1.div(&d2).unwrap_err() == Error::DivisionByZero);

        // d2 / 0
        d2 = BigFloatNumber::from_f64(p, 123.0).unwrap();
        assert!(d2.div(&d1).unwrap_err() == Error::DivisionByZero);

        // 0 / d2
        d3 = d1.div(&d2).unwrap();
        ref_num = BigFloatNumber::new(p).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / -d2
        d2 = d2.neg().unwrap();
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // add & sub & cmp
        for _ in 0..10000 {
            // avoid subnormal numbers
            let f1 = random_f64_exp(50, 25);
            let f2 = random_f64_exp(50, 25);
            if f1.is_finite() && f2.is_finite() {
                let f3 = f1 + f2;
                let f4 = f1 - f2;
                d1 = BigFloatNumber::from_f64(p, f1).unwrap();
                d2 = BigFloatNumber::from_f64(p, f2).unwrap();
                if f3 == 0.0 {
                    assert!(d1.add(&d2).unwrap().to_f64().abs() <= f64::EPSILON);
                } else {
                    assert!((d1.add(&d2).unwrap().to_f64() / f3 - 1.0).abs() <= f64::EPSILON);
                }
                if f4 == 0.0 {
                    assert!(d1.sub(&d2).unwrap().to_f64().abs() <= f64::EPSILON);
                } else {
                    assert!((d1.sub(&d2).unwrap().to_f64() / f4 - 1.0).abs() <= f64::EPSILON);
                }
                if f1 > f2 {
                    assert!(d1.cmp(&d2) > 0);
                } else if f1 < f2 {
                    assert!(d1.cmp(&d2) < 0);
                } else {
                    assert!(d1.cmp(&d2) == 0);
                }
            }
        }

        // mul & div
        for _ in 0..10000 {
            // avoid subnormal numbers
            let f1 = random_f64_exp(100, 50);
            let f2 = random_f64_exp(100, 50);
            if f1.is_finite() && f2.is_finite() && f2 != 0.0 {
                let f3 = f1*f2;
                let f4 = f1/f2;
                d1 = BigFloatNumber::from_f64(p, f1).unwrap();
                d2 = BigFloatNumber::from_f64(p, f2).unwrap();
                assert!((d1.mul(&d2).unwrap().to_f64() / f3 - 1.0).abs() <= f64::EPSILON);
                assert!((d1.div(&d2).unwrap().to_f64() / f4 - 1.0).abs() <= f64::EPSILON);
            }
        }

        // reciprocal
        let f1 = random_f64_exp(50, 25);
        d1 = BigFloatNumber::from_f64(p, f1).unwrap();
        assert!((d1.recip().unwrap().to_f64() * f1 - 1.0).abs() <= f64::EPSILON);

        // subnormal numbers
        d1 = BigFloatNumber::min_positive(p).unwrap();
        d2 = BigFloatNumber::min_positive(p).unwrap();
        ref_num = BigFloatNumber::min_positive(p).unwrap();
        let one  = BigFloatNumber::one(p).unwrap();
        ref_num = ref_num.mul(&one.add(&one).unwrap()).unwrap();

        // min_positive + min_positive = 2*min_positive
        assert!(d1.add(&d2).unwrap().cmp(&ref_num) == 0);
        assert!(d1.add(&d2).unwrap().cmp(&d1) > 0);
        assert!(d1.cmp(&d1.add(&d2).unwrap()) < 0);

        // min_positive - min_positive = 0
        ref_num = BigFloatNumber::new(p).unwrap();
        assert!(d1.sub(&d2).unwrap().cmp(&ref_num) == 0);

        // 1 * min_positive = min_positive
        assert!(one.mul(&d2).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&one).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&one).unwrap().cmp(&d2) == 0);

        // normal -> subnormal -> normal
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MIN;
        d2 = BigFloatNumber::min_positive(p).unwrap();
        assert!(!d1.is_subnormal());
        assert!(d1.sub(&d2).unwrap().cmp(&d1) < 0);
        assert!(d1.cmp(&d1.sub(&d2).unwrap()) > 0);
        d1 = d1.sub(&d2).unwrap();
        assert!(d1.is_subnormal());
        d1 = d1.add(&d2).unwrap();
        assert!(!d1.is_subnormal());

        // overflow
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MAX - (d1.m.max_bit_len() - 1) as Exponent;
        assert!(BigFloatNumber::max(p).unwrap().add(&d1).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        assert!(BigFloatNumber::min(p).unwrap().sub(&d1).unwrap_err() == Error::ExponentOverflow(Sign::Neg));
        assert!(BigFloatNumber::max(p).unwrap().mul(&BigFloatNumber::max(p).unwrap()).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        d1 = one.clone().unwrap();
        d1.e = EXPONENT_MIN;
        assert!(BigFloatNumber::max(p).unwrap().div(&d1).unwrap_err() == Error::ExponentOverflow(Sign::Pos));

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
}
