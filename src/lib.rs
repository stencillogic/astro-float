//! Multiple precision floating point numbers implemented purely in Rust. 
//!
//! Characteristics:
//!
//! | Name                          | Value  |
//! |:------------------------------|-------:|
//! | Decimal positions in mantissa |     40 |
//! | Exponent minimum value        |   -128 |
//! | Exponent maximum value        |    127 |
//!
//! The implementation does not rely heavily on the capabilities of the standard library, and can be adapted for use without the standard library.


mod defs;
mod sqrt_const;
mod sin_const;
mod tan_const;
mod increased;

use crate::defs::DECIMAL_PARTS;
use crate::sqrt_const::SQRT_VALUES;
use crate::sin_const::SIN_VALUES1;
use crate::sin_const::SIN_VALUES2;
use crate::tan_const::TAN_VALUES;
use crate::increased::BigFloatInc;

pub use crate::defs::BigFloat;
pub use crate::defs::Error;


const DECIMAL_BASE_LOG10: usize = 4;    // number decimal positions in a digit = log10(DECIMAL_BASE)
const DECIMAL_POSITIONS: usize = DECIMAL_PARTS * DECIMAL_BASE_LOG10;
const DECIMAL_BASE: usize = 10000;      // 9999 is the maximum of a digit
const DECIMAL_SIGN_POS: i8 = 1;         // + sign
const DECIMAL_SIGN_NEG: i8 = -1;        // - sign
const DECIMAL_MIN_EXPONENT: i8 = -128;  // min exponent value
const DECIMAL_MAX_EXPONENT: i8 = 127;   // max exponent value
const DECIMAL_MAX_EXPONENT_POSITIONS: i16 = 3;  // max decimal positions in exponent
const SQRT_OF_10: BigFloatInc = BigFloatInc {
    m: [5551, 3719, 1853, 4327, 3544, 9889, 3319, 8379, 6016, 2776, 3162], 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};
const ZEROED_MANTISSA: [i16; DECIMAL_PARTS] = [0; DECIMAL_PARTS];
const LN_OF_10: BigFloatInc = BigFloatInc {
    m: [1015, 7601, 6420, 6843, 1454, 1799, 6840, 4045, 9299, 5850, 2302] , 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};
const LN_OF_2: BigFloatInc = BigFloatInc {
    m: [0013, 755, 6568, 5817, 1214, 7232, 941, 9453, 559, 4718, 6931],
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -44,
};
const HALF_PI: BigFloatInc = BigFloatInc {
    m: [5846, 2098, 5144, 6397, 1691, 3132, 6192, 4896, 2679, 7963, 1570],
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};
const PI2: BigFloatInc = BigFloatInc {
    m: [1694, 4197, 0288, 2795, 3383, 6264, 2384, 9793, 5358, 5926, 3141],
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

/// Eulers number.
pub const E: BigFloat = BigFloat {
    m: [7757, 6249, 3526, 7471, 6028, 2353, 9045, 2845, 2818, 2718],
    n: DECIMAL_POSITIONS as i16, 
    sign: DECIMAL_SIGN_POS, 
    e: 1 - (DECIMAL_POSITIONS as i8),
};

/// Pi number.
pub const PI: BigFloat = BigFloat {
    m: [4197, 0288, 2795, 3383, 6264, 2384, 9793, 5358, 5926, 3141],
    n: DECIMAL_POSITIONS as i16, 
    sign: DECIMAL_SIGN_POS, 
    e: 1 - (DECIMAL_POSITIONS as i8),
};


impl BigFloat {

    /// Return new BigFloat with value zero.
    pub fn new() -> Self {
        return BigFloat {
            sign: DECIMAL_SIGN_POS,
            e: 0,
            n: 0,
            m: ZEROED_MANTISSA,
        };
    }
    
    /// Return BigFloat with the value of 1.
    pub fn one() -> Self {
        let mut val = Self::new();
        val.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/10;
        val.n = DECIMAL_POSITIONS as i16;
        val.e = 1 - DECIMAL_POSITIONS as i8;
        return val;
    }

    /// Create a BigFloat value from a sequence of `bytes`. Each byte must represent a decimal digit.
    /// First byte is the most significant. The length of `bytes` can be any. If the length of
    /// `bytes` is greater than required, then the remaining part is ignored.
    /// If `sign` is negative, then the resulting BigFloat will be
    /// negative.
    pub fn from_bytes(bytes: &[u8], sign: i8, exponent: i8) -> BigFloat {
        let mut mantissa = ZEROED_MANTISSA;
        let mut n: usize = 0;
        let mut p: i16 = 1;
        let d = if bytes.len() > DECIMAL_POSITIONS { DECIMAL_POSITIONS } else { bytes.len() };
        for i in 1..d+1 {
            mantissa[n] += (bytes[d - i] % 10) as i16 * p;
            p *= 10;
            if p == DECIMAL_BASE as i16 {
                n += 1;
                p = 1;
            }
        }

        return BigFloat {
            sign: if sign >= 0 { DECIMAL_SIGN_POS } else { DECIMAL_SIGN_NEG },
            e: exponent,
            n: d as i16,
            m: mantissa,
        };
    }

    /// Construct BigFloat from f64.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn from_f64(mut f: f64) -> Result<Self, Error> {
        let mut e: i32 = 0;
        let mut ret = BigFloat::new();
        if f == 0f64 {
            return Ok(ret);
        }
        if f == f64::INFINITY || f == f64::NAN {
            return Err(Error::ExponentOverflow);
        } 
        if f < 0f64 {
            ret.sign = DECIMAL_SIGN_NEG;
            f = -f;
        }
        // bring to 0.xxxxxxxxx
        while f >= 1.0f64 {
            f /= 10f64;
            e += 1;
        }
        while f < 0.1f64 {
            f *= 10f64;
            e -= 1;
        }
        // fill-in mantissa
        ret.n = DECIMAL_POSITIONS as i16;
        let mut p = DECIMAL_PARTS - 1;
        loop {
            f *= DECIMAL_BASE as f64;
            let d = f as i16;
            f = f - d as f64;
            ret.m[p] = d;
            p -= 1;
            if f == 0f64 || p == 0 {
                break;
            }
        }
        
        e -= DECIMAL_POSITIONS as i32;
        if e < DECIMAL_MIN_EXPONENT as i32 || e > DECIMAL_MAX_EXPONENT as i32 {
            return Err(Error::ExponentOverflow);
        }
        ret.e = e as i8;

        return Ok(ret);
    }

    /// Convert BigFloat to f64.
    pub fn to_f64(&self) -> f64 {
        let mut f: f64 = 0f64;
        for i in 0..DECIMAL_PARTS {
            f += self.m[i] as f64;
            f /= DECIMAL_BASE as f64;
        }
        let mut e = self.n + self.e as i16;
        while e < 0 {
            f /= 10f64;
            e += 1;
        }
        while e > 0 {
            f *= 10f64;
            e -= 1;
        }
        if self.sign == DECIMAL_SIGN_NEG {
            f = -f;
        }
        return f;
    }

    /// Construct BigFloat from f32. Wrapper for from_f64.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn from_f32(f: f32) -> Result<Self, Error> {
        Self::from_f64(f as f64)
    }

    /// Convert BigFloat to f32. Wrapper for to_f64
    pub fn to_f32(&self) -> f32 {
        self.to_f64() as f32
    }

    /// Get BigFloat's mantissa as bytes. Each byte represents a decimal digit.
    /// First byte is the most significant. The length of `bytes` can be any. If the length of
    /// `bytes` is smaller than required, then remaining part of mantissa will be omitted.
    ///
    /// The length of mantissa can be determined using `get_mantissa_len`.
    pub fn get_mantissa_bytes(&self, bytes: &mut [u8]) {
        let mut n: usize = 0;
        let mut p: i16 = 1;
        let d = if bytes.len() < self.n as usize { bytes.len() } else { self.n as usize };
        for i in 1..d+1 {
            bytes[d - i] = ((self.m[n] / p) % 10) as u8;
            p *= 10;
            if p == DECIMAL_BASE as i16 {
                n += 1;
                p = 1;
            }
        }
    }

    /// Return the number of decimal positions filled in the mantissa.
    pub fn get_mantissa_len(&self) -> usize {
        self.n as usize
    }

    /// Return 1 if BigFloat is positive, -1 otherwise.
    pub fn get_sign(&self) -> i8 {
        self.sign
    }

    /// Return exponent part.
    pub fn get_exponent(&self) -> i8 {
        self.e
    }

    /// Return absolute value. 
    pub fn abs(&self) -> BigFloat {
        let mut ret = *self;
        if ret.sign == DECIMAL_SIGN_NEG {
            ret.sign = DECIMAL_SIGN_POS;
        }
        return ret;
    }


    /// Add d2 and return result of addition.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn add(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        return self.add_sub(d2, 1);
    }

    /// Subtract d2 and return result of subtraction.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn sub(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        return self.add_sub(d2, -1);
    }

    /// Multiply by d2 and return result of multiplication.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn mul(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        let mut d3 = Self::new();
        let mut m: i32;
        let mut k: i32;
        let mut n: i32;
        let mut nd: i32;
        let mut e: i32 = self.e as i32 + d2.e as i32;
        let mut d1mi: i32;
        let mut m3 = [0i16; DECIMAL_PARTS * 2 + 1];

        for i in 0..DECIMAL_PARTS {
            d1mi = self.m[i] as i32;
            if d1mi == 0 {
                continue;
            }

            k = 0;
            let mut j = 0;
            while j < DECIMAL_PARTS {
                m = d1mi * (d2.m[j] as i32) + m3[i + j] as i32 + k;

                m3[i + j] = (m % DECIMAL_BASE as i32) as i16;
                k = m / DECIMAL_BASE as i32;
                j += 1;
            }
            m3[i + j] += k as i16;
        }

        n = Self::num_digits(&m3[DECIMAL_PARTS..]) as i32;
        if n > 0 {
            n += DECIMAL_POSITIONS as i32;
        } else {
            n = Self::num_digits(&m3) as i32;
        }

        // take care if result is not fitting in d3.m without truncating
        if n > DECIMAL_POSITIONS as i32 {
            // save as much digits as we can
            e += n - DECIMAL_POSITIONS as i32;
            nd = n % DECIMAL_BASE_LOG10 as i32;
            n = n / DECIMAL_BASE_LOG10 as i32 - DECIMAL_PARTS as i32 + 1;

            Self::shift_left(&mut m3[n as usize..], DECIMAL_BASE_LOG10 - nd as usize);

            k = DECIMAL_BASE as i32;
            nd = DECIMAL_BASE_LOG10 as i32 - nd;
            while nd > 0 {
                k /= 10;
                nd -= 1;
            }
            m3[n as usize] += m3[n as usize - 1] / k as i16;

            d3.n = DECIMAL_POSITIONS as i16;
        } else {
            d3.n = n as i16;
            n = 0;
        }

        if e > DECIMAL_MAX_EXPONENT as i32 || e < DECIMAL_MIN_EXPONENT as i32 {
            return Err(Error::ExponentOverflow);
        }

        for i in 0..d3.m.len() {
            d3.m[i] = m3[n as usize + i];
        }
        d3.e = e as i8;
        d3.sign = if self.sign == d2.sign || self.n == 0 {
            DECIMAL_SIGN_POS
        } else {
            DECIMAL_SIGN_NEG
        };

        return Ok(d3);
    }

    /// Divide by d2 and return result of division.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    /// DivisionByZero - in case of d2 equal to zero.
    pub fn div(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        // Knuth's division
        let mut d3 = Self::new();
        let mut d: i32;
        let mut c: i16;
        let mut i: i32;
        let mut j: i32;
        let n: i32;
        let m: i32;
        let e: i32;
        let mut qh: i32;
        let mut k: i32;
        let mut rh: i32;
        let mut p: i32;
        let mut buf = [0i16; DECIMAL_PARTS * 3 + 4];
        let v1: i32;
        let v2: i32;
        let n1: usize = 2 + DECIMAL_PARTS;
        let n2: usize = DECIMAL_PARTS * 2 + 3;
        let mut n1j: usize;

        if d2.n == 0 {
            return Err(Error::DivisionByZero);
        }
        n = (d2.n as i32 - 1) / DECIMAL_BASE_LOG10 as i32;

        if self.n == 0 {
            return Ok(d3); // d1 / d2 = 0
        }
        m = (self.n as i32 - 1) / DECIMAL_BASE_LOG10 as i32;

        i = DECIMAL_PARTS as i32 - 1;
        p = 1;

        if n == 0 {
            // division by single digit
            d = d2.m[0] as i32;
            rh = 0;
            j = m;
            if (self.m[j as usize] as i32) < d {
                rh = self.m[j as usize] as i32;
                j -= 1;
                p -= 1;
            }

            while i >= 0 {
                qh = rh * DECIMAL_BASE as i32 + if j >= 0 { self.m[j as usize] as i32 } else { 0 };
                rh = qh % d;
                d3.m[i as usize] = (qh / d) as i16;

                if rh == 0 && j <= 0 {
                    break;
                }

                j -= 1;
                i -= 1;
            }

            while i > 0 {
                i -= 1;
                d3.m[i as usize] = 0;
            }
        } else {
            // normalize: n1 = d1 * d, n2 = d2 * d
            d = DECIMAL_BASE as i32 / (d2.m[n as usize] as i32 + 1); // factor d: d * d2[most significant] is close to DECIMAL_BASE

            if d == 1 {
                for w in 0..self.m.len() {
                    buf[n1 + w] = self.m[w];
                }
                for w in 0..d2.m.len() {
                    buf[n2 + w] = d2.m[w];
                }
            } else {
                Self::mul_by_digit(&self.m, d, &mut buf[n1..]);
                Self::mul_by_digit(&d2.m, d, &mut buf[n2..]);
            }

            v1 = buf[n2 + n as usize] as i32;
            v2 = buf[n2 + n as usize - 1] as i32;

            j = m - n;
            loop {
                n1j = (n1 as i32 + j) as usize;
                qh = buf[n1j + n as usize + 1] as i32 * DECIMAL_BASE as i32
                    + buf[n1j + n as usize] as i32;
                rh = qh % v1;
                qh /= v1;

                if qh >= DECIMAL_BASE as i32
                    || (qh * v2 > DECIMAL_BASE as i32 * rh + buf[n1j + n as usize - 1] as i32)
                {
                    qh -= 1;
                    rh += v1;
                    if rh < DECIMAL_BASE as i32 {
                        if qh >= DECIMAL_BASE as i32
                            || (qh * v2
                                > DECIMAL_BASE as i32 * rh + buf[n1j + n as usize - 1] as i32)
                        {
                            qh -= 1;
                        }
                    }
                }

                // n1_j = n1_j - n2 * qh
                c = 0;
                k = 0;
                for l in 0..n + 2 {
                    k = buf[n2 + l as usize] as i32 * qh + k / DECIMAL_BASE as i32;
                    buf[n1j + l as usize] -= (k % DECIMAL_BASE as i32) as i16 + c;
                    if buf[n1j + l as usize] < 0 {
                        buf[n1j + l as usize] += DECIMAL_BASE as i16;
                        c = 1;
                    } else {
                        c = 0;
                    }
                }

                if c > 0 {
                    // compensate
                    qh -= 1;
                    c = 0;
                    for l in 0..n + 2 {
                        buf[n1j + l as usize] += buf[n2 + l as usize] + c;
                        if buf[n1j + l as usize] >= DECIMAL_BASE as i16 {
                            buf[n1j + l as usize] -= DECIMAL_BASE as i16;
                            c = 1;
                        } else {
                            c = 0;
                        }
                    }
                    assert!(c > 0);
                }

                if i < DECIMAL_PARTS as i32 - 1 || qh > 0 {
                    d3.m[i as usize] = qh as i16;
                    i -= 1;
                } else {
                    p -= 1;
                }

                j -= 1;
                if i < 0 || n1 as i32 + j < 0 {
                    break;
                }
            }
        }

        // exponent
        j = 0;
        d = d3.m[DECIMAL_PARTS - 1] as i32;
        while d > 0 {
            d /= 10;
            j += 1;
        }

        e = self.e as i32
            - d2.e as i32
            - (DECIMAL_PARTS as i32 - m + n - p) * DECIMAL_BASE_LOG10 as i32;

        if e > DECIMAL_MAX_EXPONENT as i32 || e < DECIMAL_MIN_EXPONENT as i32 {
            return Err(Error::ExponentOverflow);
        }

        d3.e = e as i8;

        d3.n = DECIMAL_POSITIONS as i16 - DECIMAL_BASE_LOG10 as i16 + j as i16;

        d3.sign = if self.sign == d2.sign {
            DECIMAL_SIGN_POS
        } else {
            DECIMAL_SIGN_NEG
        };

        return Ok(d3);
    }

    /// Return square root of a number.
    ///
    /// # Errors
    ///
    /// Returns ArgumentIsNegative if `self` is less than 0.
    pub fn sqrt(&self) -> Result<BigFloat, Error> {
        if self.sign == DECIMAL_SIGN_NEG {
            return Err(Error::ArgumentIsNegative);
        }

        if self.n == 0 || self.m == ZEROED_MANTISSA {
            return Ok(*self);
        }

        let mut int_num = Self::to_big_float_inc(self);
        int_num.e = 0;
        let mut sq = Self::sqrt_int(&int_num)?;

        if self.e & 1 != 0 {
            if self.e < 0 {
                sq = sq.div(&SQRT_OF_10)?;
            } else {
                sq = sq.mul(&SQRT_OF_10)?;
            }
        }
        let mut ret = Self::from_big_float_inc(&mut sq);
        ret.e += self.e/2;
        return Ok(ret);
    }

    /// Return BigFloat to the power of `d1`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    ///
    /// ArgumentIsNegative - when `d1` has fractional part and `self` is negative.
    pub fn pow(&self, d1: &BigFloat) -> Result<BigFloat, Error> {
        if self.n == 0 {
            return Ok(*self);
        }

        if d1.n == 0 {
            return Ok(Self::one());
        }

        if d1.n + d1.e as i16 > DECIMAL_MAX_EXPONENT_POSITIONS {
            return Err(Error::ExponentOverflow);
        }

        // fractional part of d1 
        let mut fractional = Self::new();
        let mut i = -(d1.e as i32);
        if i > 0 && i < (DECIMAL_POSITIONS*2) as i32 {
            fractional.m = d1.m;
            if i < DECIMAL_POSITIONS as i32 {
                Self::shift_left(&mut fractional.m, DECIMAL_POSITIONS - i as usize);
            } else if i > DECIMAL_POSITIONS as i32 {
                Self::shift_right(&mut fractional.m, i as usize - DECIMAL_POSITIONS);
            }
            fractional.n = Self::num_digits(&fractional.m);
        }

        // integer part of d1
        let mut int = Self::new();
        let mut t = Self::get_div_factor(-(d1.e as i16));
        if i < 0 {
            i = 0;
        }
        let mut t2 = 1;
        while i < d1.n as i32 {
            int.m[int.n as usize / DECIMAL_BASE_LOG10] += (d1.m[i as usize / DECIMAL_BASE_LOG10 as usize] / t % 10) * t2;
            int.n += 1;
            i += 1;
            t *= 10;
            if t == DECIMAL_BASE as i16 {
                t = 1;
            }
            t2 *= 10;
            if t2 == DECIMAL_BASE as i16 {
                t2 = 1;
            }
        }

        let mut ret = Self::one();
        let one = ret;
        let mut ml = *self;
        while int.n > 0 {
            if int.m[0] & 1 != 0 {
                ret = ret.mul(&ml)?;
            }
            ml = ml.mul(&ml)?;
            Self::divide_by_two_int(&mut int);
        }
        let mut m = [0; DECIMAL_PARTS + 1];
        let mut sq = self.sqrt()?;
        let mut err = sq;
        if fractional.m != ZEROED_MANTISSA {
            loop {
                Self::mul_by_digit(&fractional.m, 2, &mut m);
                if m[DECIMAL_PARTS] != 0 {
                    ret = ret.mul(&sq)?;
                    m[DECIMAL_PARTS] = 0;
                }
                fractional.m.as_mut_slice().copy_from_slice(&m[0..DECIMAL_PARTS]);
                let sq2 = sq.sqrt()?;
                let err2 = sq.sub(&sq2)?.abs();
                if fractional.m == ZEROED_MANTISSA || err2.cmp(&err) >= 0 {
                    break;
                }
                sq = sq2;
                err = err2;
            }
        }

        if d1.sign == DECIMAL_SIGN_NEG {
            ret = one.div(&ret)?;
        }

        return Ok(ret);
    }

    /// Returns natural logarithm of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    ///
    /// InvalidArgument - when `self` is negative or zero.
    pub fn ln(&self) -> Result<BigFloat, Error> {
        if self.sign == DECIMAL_SIGN_NEG || self.n == 0 {
            return Err(Error::InvalidArgument);
        }

        // factoring: ln(d) = ln(d.m ^ (1 - d.n)) + (d.e - 1 + d.n) * ln(10)
        let mut add = BigFloatInc::new();
        let mut s = self.e as i16 - 1 + self.n;
        if s != 0 {
            // check if s fits in single "digit"
            assert!(DECIMAL_MAX_EXPONENT as i16 + 1 + (DECIMAL_POSITIONS as i16) < DECIMAL_BASE as i16 && 
               DECIMAL_POSITIONS as i16 + 1 - (DECIMAL_MIN_EXPONENT as i16) < DECIMAL_BASE as i16);
            if s > 0 {
                add.m[0] = s;
            } else {
                add.m[0] = -s;
                add.sign = DECIMAL_SIGN_NEG;
            }
            while s != 0 {
                add.n += 1;
                s /= 10;
            }
            add = add.mul(&LN_OF_10)?;
        }

        let one = BigFloatInc::one();
        let two = BigFloatInc::two();
        let mut ml = Self::to_big_float_inc(self);
        ml.e = 1 - ml.n as i8;

        // additional factoring
        while ml.cmp(&two) >= 0 {
            add = add.add(&LN_OF_2)?;
            ml = ml.div(&two)?;
        }

        // artanh series
        ml = ml.sub(&one)?.div(&ml.add(&one)?)?;    // (x-1)/(x+1)
        let mut ret = ml;
        let mlq = ml.mul(&ml)?;
        let mut d = one;
        loop {
            d = d.add(&two)?;
            ml = ml.mul(&mlq)?;
            let p = ml.div(&d)?;
            let val = ret.add(&p)?;
            if val.cmp(&ret) == 0 {
                break;
            }
            ret = val;
        }
        ret = ret.mul(&two)?.add(&add)?;

        return Ok(Self::from_big_float_inc(&mut ret));
    }

    /// Returns sine of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn sin(&self) -> Result<BigFloat, Error> {
        self.sin_cos(0)
    }

    /// Returns cosine of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn cos(&self) -> Result<BigFloat, Error> {
        self.sin_cos(1)
    }

    /// Returns tangent of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    /// DivisionByZero - in case of number is equal to PI/2.
    pub fn tan(&self) -> Result<BigFloat, Error> {
        // tan(x) = tan(s + dx) = tan(s) + tan(dx) / (1 - tan(s)*tan(dx));
        // tan(s) = sin(s)/cos(s)
        // tan(dx) = x + 1/3*x^3 + 2/15*x^5 + ... (tailor series)
        // do calculation only for angles [0, pi/2)
        let mut x = Self::to_big_float_inc(self);

        // determine quadrant
        let mut quadrant = 0;
        x = x.div(&PI2)?;
        let fractional = x.get_fractional_part()?;
        x = PI2.mul(&fractional)?;
        while x.cmp(&HALF_PI) > 0 {
            x = PI2.sub(&x)?;
            quadrant = 1;
        }
        x.maximize_mantissa();
        let mut i = 1 - (x.n as i32 + x.e as i32);
        let mut idx = 0;
        let mut dx = x;

        // x = s + dx
        if i < DECIMAL_BASE_LOG10 as i32 {
            idx = x.m[DECIMAL_PARTS] as usize;
            let mut m = 1;
            while i > 0 {
                idx /= 10;
                i -= 1;
                m *= 10;
            }
            dx.m[DECIMAL_PARTS] = x.m[DECIMAL_PARTS] % m;
        }

        // sin(s) / cos(s) = sin(s) / sin(s + pi/2)
        let tan_s = SIN_VALUES1[idx].div(&SIN_VALUES2[idx])?;

        // tailor series
        let mut tan_dx = dx;
        let dxq = dx.mul(&dx)?;
        let mut i = 0;
        while i < TAN_VALUES.len() {
            dx = dx.mul(&dxq)?;
            let p = dx.mul(&TAN_VALUES[i])?;
            let val = tan_dx.add(&p)?;
            if val.cmp(&tan_dx) == 0 {
                break;
            }
            tan_dx = val;
            i += 1;
        }

        // tan(x)
        let d = BigFloatInc::one().sub(&tan_s.mul(&tan_dx)?)?;
        let mut ret = tan_s.add(&tan_dx)?.div(&d)?;
        if (quadrant == 1 && self.sign == DECIMAL_SIGN_POS) || (quadrant == 0 && self.sign == DECIMAL_SIGN_NEG) {
            ret.sign = DECIMAL_SIGN_NEG;
        }
        return Ok(Self::from_big_float_inc(&mut ret));
    }

    /// Compare to d2.
    /// Returns positive if self > d2, negative if self < d2, 0 otherwise.
    pub fn cmp(&self, d2: &BigFloat) -> i16 {
        if self.sign != d2.sign {
            return self.sign as i16;
        }

        if self.n == 0 || d2.n == 0 {
            if d2.n != 0 {
                return -d2.sign as i16;
            } else if self.n != 0 {
                return self.sign as i16;
            } else {
                return 0;
            }
        }

        let diff: i32 = self.e as i32 + self.n as i32 - d2.e as i32 - d2.n as i32;
        if diff > 0 {
            return 1;
        }
        if diff < 0 {
            return -1;
        }

        if self.n != d2.n {
            return Self::abs_cmp_with_shift(&self.m, self.n, &d2.m, d2.n) * self.sign as i16;
        }

        return Self::abs_cmp(&self.m, &d2.m) * self.sign as i16;
    }

    /// Return raw parts of BigFloat: mantissa, number of decimal positions in mantissa, sing, and
    /// exponent.
    pub fn to_raw_parts(&self) -> ([i16; DECIMAL_PARTS], i16, i8, i8) {
        (self.m, self.n, self.sign, self.e)
    }

    /// Construct BigFloat from raw parts.
    pub fn from_raw_parts(mantissa: [i16; DECIMAL_PARTS], mantissa_len: i16, sign: i8, exponent: i8) -> Self {
        return BigFloat {
            sign: sign,
            e: exponent,
            n: mantissa_len,
            m: mantissa,
        };
    }


    // auxiliary functions

    // compare absolute values of two big floats
    // return positive if d1 > d2, negative if d1 < d2, 0 otherwise
    fn abs_cmp(d1: &[i16], d2: &[i16]) -> i16 {
        let mut i: i32 = DECIMAL_PARTS as i32 - 1;
        while i >= 0 {
            if d1[i as usize] != d2[i as usize] {
                return d1[i as usize] - d2[i as usize];
            }
            i -= 1;
        }
        return 0;
    }

    // compare absolute values of two floats with shifts n1, n2
    // return positive if d1 > d2, negative if d1 < d2, 0 otherwise
    fn abs_cmp_with_shift(d1: &[i16], mut n1: i16, d2: &[i16], mut n2: i16) -> i16 {
        let mut t1: i16 = DECIMAL_BASE as i16 / 10;
        let mut t2: i16 = DECIMAL_BASE as i16 / 10;
        let mut s: i16;
        let mut v1: i16;
        let mut v2: i16;

        s = DECIMAL_BASE_LOG10 as i16 - n1 % DECIMAL_BASE_LOG10 as i16;
        while s > 0 {
            s -= 1;
            t1 /= 10;
            if t1 == 0 {
                t1 = DECIMAL_BASE as i16 / 10;
            };
        }
        s = DECIMAL_BASE_LOG10 as i16 - n2 % DECIMAL_BASE_LOG10 as i16;
        while s > 0 {
            s -= 1;
            t2 /= 10;
            if t2 == 0 {
                t2 = DECIMAL_BASE as i16 / 10;
            };
        }

        n1 -= 1;
        n2 -= 1;
        while n1 >= 0 && n2 >= 0 {
            v1 = (d1[n1 as usize / DECIMAL_BASE_LOG10] / t1) % 10;
            v2 = (d2[n2 as usize / DECIMAL_BASE_LOG10] / t2) % 10;
            if v1 != v2 {
                return v1 - v2;
            }
            t1 /= 10;
            if t1 == 0 {
                t1 = DECIMAL_BASE as i16 / 10;
            }
            t2 /= 10;
            if t2 == 0 {
                t2 = DECIMAL_BASE as i16 / 10;
            }
            n1 -= 1;
            n2 -= 1;
        }
        while n1 >=0 {
            v1 = (d1[n1 as usize / DECIMAL_BASE_LOG10] / t1) % 10;
            if v1 != 0 {
                return 1;
            }
            n1 -= 1;
        }
        while n2 >=0 {
            v2 = (d2[n2 as usize / DECIMAL_BASE_LOG10] / t2) % 10;
            if v2 != 0 {
                return -1;
            }
            n2 -= 1;
        }
        return 0;
    }

    // add if op >= 0 subtract if op < 0
    fn add_sub(&self, d2: &BigFloat, op: i8) -> Result<BigFloat, Error> {
        let mut d3 = Self::new();
        let shift: i32;
        let free: i32;
        let mut e: i32;
        let cmp: i16;
        let mut n1: &BigFloat;
        let mut n2: &BigFloat;
        let mut s1: BigFloat;
        let mut s2: BigFloat;

        // one of the numbers is zero
        if 0 == self.n {
            d3 = *d2;
            if op < 0
            // 0 - d2
            {
                d3.sign = -d3.sign;
            }
            return Ok(d3);
        }
        if 0 == d2.n {
            d3 = *self;
            return Ok(d3);
        }

        // assign d1 and d2 to n1 and n2 such that n1 has more significant digits than n2
        // (we want to save more digits while not sacrificing any significant digits)
        if self.e as i32 + (self.n as i32) < d2.e as i32 + d2.n as i32 {
            n1 = d2;
            n2 = self;
        } else {
            n1 = self;
            n2 = d2;
        }
        shift = n1.e as i32 - n2.e as i32;
        e = n1.e as i32;

        // bring n1 and n2 to having common exponent
        if shift > 0 {
            s1 = *n1;
            s2 = *n2;

            free = DECIMAL_POSITIONS as i32 - s1.n as i32;

            if shift > free {
                if shift - free > s2.n as i32 {
                    // n2 is too small
                    d3 = *n1;
                    return Ok(d3);
                } else {
                    if free > 0 {
                        Self::shift_left(&mut s1.m, free as usize);
                    }
                    Self::shift_right(&mut s2.m, (shift - free) as usize);
                    e -= free;
                }
            } else {
                Self::shift_left(&mut s1.m, shift as usize);
                e -= shift;
            }
            n1 = &s1;
            n2 = &s2;
        } else if shift < 0 {
            s2 = *n2;
            Self::shift_left(&mut s2.m, (-shift) as usize);
            n2 = &s2;
        }

        if (n1.sign != n2.sign && op >= 0) || (op < 0 && n1.sign == n2.sign) {
            // subtract
            cmp = Self::abs_cmp(&n1.m, &n2.m);
            if cmp > 0 {
                d3.sign = n1.sign;
                d3.e = e as i8;
                Self::abs_sub(&n1.m, &n2.m, &mut d3.m);
                d3.n = Self::num_digits(&d3.m);
            } else if cmp < 0 {
                d3.sign = n2.sign;
                d3.e = e as i8;
                Self::abs_sub(&n2.m, &n1.m, &mut d3.m);
                d3.n = Self::num_digits(&d3.m);
            } else {
                d3.sign = DECIMAL_SIGN_POS;
                d3.e = 0;
                d3.n = 0;
                d3.m.iter_mut().for_each(|x| *x = 0);
            }
        } else {
            // add
            d3.sign = self.sign;
            d3.e = e as i8;
            if Self::abs_add(&n1.m, &n2.m, &mut d3.m) > 0 {
                if e == DECIMAL_MAX_EXPONENT as i32 {
                    return Err(Error::ExponentOverflow);
                }
                d3.e += 1;
                Self::shift_right(&mut d3.m, 1);
                d3.m[DECIMAL_PARTS - 1] += DECIMAL_BASE as i16 / 10;
                d3.n = DECIMAL_POSITIONS as i16;
            } else {
                d3.n = Self::num_digits(&d3.m);
            }
        }
        return Ok(d3);
    }

    fn abs_add(d1: &[i16], d2: &[i16], d3: &mut [i16]) -> u32 {
        let mut s: u32;
        let mut c: u32 = 0;

        let mut i: usize = 0;
        while i < DECIMAL_PARTS {
            s = d1[i] as u32 + d2[i] as u32 + c;
            if s >= DECIMAL_BASE as u32 {
                s -= DECIMAL_BASE as u32;
                c = 1;
            } else {
                c = 0;
            }
            d3[i] = s as i16;
            i += 1;
        }

        return c;
    }

    // subtract absolute value of d2 from d1
    // d1 is supposed to be > d2
    fn abs_sub(d1: &[i16], d2: &[i16], d3: &mut [i16]) {
        let mut c: i16 = 0;
        let mut i: usize = 0;
        while i < DECIMAL_PARTS {
            if d1[i] < d2[i] + c {
                d3[i] = d1[i] + DECIMAL_BASE as i16 - d2[i] - c;
                c = 1;
            } else {
                d3[i] = d1[i] - d2[i] - c;
                c = 0;
            }
            i += 1;
        }
        assert!(0 == c);
    }

    // shift m to the right by n digits
    fn shift_right(m: &mut [i16], mut n: usize) {
        assert!(n > 0 && n <= DECIMAL_POSITIONS);

        let mut s: i16;
        let mut t: i16;
        let mut x: i32 = (n % DECIMAL_BASE_LOG10) as i32;
        n = n / DECIMAL_BASE_LOG10;
        if x == 0 {
            if n > 0 {
                for i in 0..DECIMAL_PARTS - n {
                    m[i] = m[i + n];
                }
            }
        } else {
            s = 10;
            t = DECIMAL_BASE as i16 / 10;
            x -= 1;
            while x > 0 {
                s *= 10;
                t /= 10;
                x -= 1;
            }

            let mut i = 0;
            while i < DECIMAL_PARTS - n - 1 {
                m[i] = (m[i + n + 1] % s) * t + m[i + n] / s;
                i += 1;
            }
            m[i] = m[i + n] / s;
        }
        for i in 0..n {
            m[i + DECIMAL_PARTS - n] = 0;
        }
    }

    // shift m to the left by n digits
    fn shift_left(m: &mut [i16], mut n: usize) {
        assert!(n > 0 && n <= DECIMAL_POSITIONS);

        let mut i: usize;
        let mut s: i16;
        let mut t: i16;
        let mut x: i32 = (n % DECIMAL_BASE_LOG10) as i32;
        n = n / DECIMAL_BASE_LOG10;
        if x == 0 {
            if n > 0 {
                i = DECIMAL_PARTS - 1;
                while i >= n {
                    m[i] = m[i - n];
                    i -= 1;
                }
            }
        } else {
            s = 10;
            t = DECIMAL_BASE as i16 / 10;
            x -= 1;
            while x > 0 {
                s *= 10;
                t /= 10;
                x -= 1;
            }

            i = DECIMAL_PARTS - 1;
            while i > n {
                m[i] = (m[i - n] % t) * s + m[i - n - 1] / t;
                i -= 1;
            }
            m[i] = (m[i - n] % t) * s;
        }
        for k in 0..n {
            m[k] = 0;
        }
    }

    // return number of digits taken in mantissa
    fn num_digits(m: &[i16]) -> i16 {
        let mut n: i16 = DECIMAL_POSITIONS as i16;
        let mut t: i16;
        let mut p: i16 = DECIMAL_PARTS as i16 - 1;

        while p >= 0 && 0 == m[p as usize] {
            p -= 1;
            n -= DECIMAL_BASE_LOG10 as i16;
        }

        if n > 0 {
            t = m[p as usize];
            n -= DECIMAL_BASE_LOG10 as i16;
            loop {
                n += 1;
                t /= 10;
                if t == 0 {
                    break;
                }
            }
        }

        return n;
    }

    // multiply d1 by digit d and put result to d3 with overflow
    fn mul_by_digit(d1: &[i16], d: i32, d3: &mut [i16]) {
        let mut m: i32 = 0;
        for i in 0..DECIMAL_PARTS {
            m = d1[i] as i32 * d + m / DECIMAL_BASE as i32;
            d3[i] = (m % DECIMAL_BASE as i32) as i16;
        }
        d3[DECIMAL_PARTS] = (m / DECIMAL_BASE as i32) as i16;
    }

    // sqrt of integer
    fn sqrt_int(d1: &BigFloatInc) -> Result<BigFloatInc, Error> {

        // choose initial value
        let mut i = DECIMAL_PARTS - 1;
        while d1.m[i] == 0 && i > 0 {
            i -= 1;
        }
        let j = d1.m[i] / 100;
        let mut n = Self::to_big_float_inc(&SQRT_VALUES[i*99 + j as usize]);

        // Newton's method
        let mut two = BigFloatInc::new();
        two.m[0] = 2;
        two.n = 1;
        let mut err = *d1;
        loop {
            let nsq = n.mul(&n)?;
            let nd = n.mul(&two)?;
            let n2 = d1.add(&nsq)?.div(&nd)?;
            let err2 = n.sub(&n2)?;
            if err2.cmp(&err) >= 0 {
                break;
            }
            err = err2;
            n = n2;
        }
        return Ok(n);
    }

    // divide BigFloat by two as integer
    fn divide_by_two_int(d1: &mut BigFloat) {
        d1.m[0] >>= 1;
        for i in 1..(d1.n as usize + DECIMAL_BASE_LOG10 - 1) / DECIMAL_BASE_LOG10 {
            if d1.m[i] & 1 != 0 {
                d1.m[i - 1] += DECIMAL_BASE as i16 / 2;
            }
            d1.m[i] >>= 1;
        }
        d1.n = Self::num_digits(&d1.m);
    }

    // factor to divide by to get a digit at position n
    fn get_div_factor(n: i16) -> i16 {
        let mut x = n % DECIMAL_BASE_LOG10 as i16;
        let mut t = 1;
        while x > 0 {
            t *= 10;
            x -= 1;
        }
        return t;
    }

    // Convert to BigFloatInc.
    fn to_big_float_inc(d1: &BigFloat) -> BigFloatInc {
        let mut ret = BigFloatInc::new();
        (&mut ret.m[0..DECIMAL_PARTS]).copy_from_slice(&d1.m);
        ret.n = d1.n;
        ret.e = d1.e;
        ret.sign = d1.sign;
        return ret;
    }

    // Convert from BigFloatInc.
    fn from_big_float_inc(d1: &mut BigFloatInc) -> BigFloat {
        let mut ret = BigFloat::new();
        d1.maximize_mantissa();
        d1.round();
        (&mut ret.m).copy_from_slice(&d1.m[1..]);
        ret.n = if d1.n > DECIMAL_PARTS as i16 { d1.n - DECIMAL_BASE_LOG10 as i16 } else { 0 };
        ret.e = d1.e + DECIMAL_BASE_LOG10 as i8;
        ret.sign = d1.sign;
        return ret;
    }

    // sin: q=0, cos: q=1; 
    fn sin_cos(&self, q: usize) -> Result<BigFloat, Error> {
        // calculation:
        // x = s + dx, x is in [0, pi/2)
        // use series: sin(x) = sin(s) + sum( der(sin(s), n) * (dx)^n / n! )
        // where: der(sin(s), n) = sin(s + n*pi/2) - n'th derivative of sin
        // use precalculated values: sin(s), sin(s + pi/2), sin(s + pi) = -sin(s), sin(s + 3*pi/2)
        //   = -sin(s + pi/2)
        // do calculation only for angles [0, pi/2)
        let mut x = Self::to_big_float_inc(self);

        // determine quadrant
        let mut quadrant = q;
        x = x.div(&PI2)?;
        let fractional = x.get_fractional_part()?;
        x = PI2.mul(&fractional)?;
        while x.cmp(&HALF_PI) > 0 {
            x = x.sub(&HALF_PI)?;
            quadrant += 1;
        }
        if quadrant >= 4 {
            quadrant -= 4;
        }
        if x.sign == DECIMAL_SIGN_NEG {
            quadrant = 3 - quadrant;
        }
        x.maximize_mantissa();
        let mut i = 1 - (x.n as i32 + x.e as i32);
        let mut idx = 0;
        let mut dx = x;

        // x = s + dx
        if i < DECIMAL_BASE_LOG10 as i32 {
            idx = x.m[DECIMAL_PARTS] as usize;
            let mut m = 1;
            while i > 0 {
                idx /= 10;
                i -= 1;
                m *= 10;
            }
            dx.m[DECIMAL_PARTS] = x.m[DECIMAL_PARTS] % m;
        }

        // determine closest precomputed values of derivatives
        let mut s = [BigFloatInc::new(), BigFloatInc::new(), BigFloatInc::new(), BigFloatInc::new(),];
        s[0] = SIN_VALUES1[idx];
        s[1] = SIN_VALUES2[idx];
        s[2] = s[0];
        s[2].sign = DECIMAL_SIGN_NEG;
        s[3] = s[1];
        s[3].sign = DECIMAL_SIGN_NEG;

        let mut ret = s[quadrant];
        let mut dxn = dx;
        let one = BigFloatInc::one();
        let mut fct = one;
        let mut inc = one;
        let mut der_n = (quadrant + 1) % 4;
        loop {
            let p = dxn.div(&fct)?;
            let der = s[der_n];
            if der.n != 0 {
                let add = der.mul(&p)?;
                let val = ret.add(&add)?;
                if val.cmp(&ret) == 0 {
                    break;
                }
                ret = val;
            }
            dxn = dxn.mul(&dx)?;
            inc = inc.add(&one)?;
            fct = fct.mul(&inc)?;
            der_n += 1;
            if der_n > 3 {
                der_n = 0;
            }
        }
        if q == 0 {
            ret.sign = self.sign;
        }
        return Ok(Self::from_big_float_inc(&mut ret));
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use rand::random;

    #[test]
    fn test_bigfloat() {


        println!("Testing creation and deconstruction");

        let mut d1 = BigFloat::new(); 
        let mut d2 = BigFloat::new(); 
        let mut d3: BigFloat; 
        let mut ref_num = BigFloat::new();
        let one = BigFloat::one();

        assert!(DECIMAL_PARTS >= 10);

        // regular buf
        let bytes1: [u8; 20] = [1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20];
        let expected1: [u8; 30] = [1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,0,0,0,0,0,0,0,0,0,0];
        let exp1 = 123;
        let d4 = BigFloat::from_bytes(&bytes1, 1, exp1);

        let mut mantissa_buf1 = [0; 30];
        d4.get_mantissa_bytes(&mut mantissa_buf1);
        assert!(mantissa_buf1 == expected1);
        assert!(d4.get_mantissa_len() == bytes1.len());
        assert!(d4.get_sign() == 1);
        assert!(d4.get_exponent() == exp1);

        // too long buf
        let bytes2: [u8; 45] = [1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20,1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20,21,22,3,4,5];
        let expected2: [u8; 42] = [1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,0,0];
        let exp2 = -128;
        let d4 = BigFloat::from_bytes(&bytes2, -2, exp2);

        let mut mantissa_buf2 = [0; 42];
        d4.get_mantissa_bytes(&mut mantissa_buf2);
        assert!(mantissa_buf2 == expected2);
        assert!(d4.get_mantissa_len() == 40);
        assert!(d4.get_sign() == -1);
        assert!(d4.get_exponent() == exp2);

        // raw parts
        let (m,n,s,e) = d4.to_raw_parts();
        let d5 = BigFloat::from_raw_parts(m,n,s,e);
        assert!(d5.cmp(&d4) == 0);


        println!("Testing comparisons");

        assert!(d1.cmp(&d2) == 0);

        d1.m[0] = 1;    // 1, 0
        d1.n = 1;
        assert!(d1.cmp(&d2) > 0);

        d2.m[0] = 2;    // 1, 2
        d2.n = 1;
        assert!(d1.cmp(&d2) < 0);

        d1.sign = DECIMAL_SIGN_NEG; // -1, 2
        assert!(d1.cmp(&d2) < 0);

        d2.sign = DECIMAL_SIGN_NEG; // -1, -2
        assert!(d1.cmp(&d2) > 0);

        d1.sign = DECIMAL_SIGN_POS; // 1, -2
        assert!(d1.cmp(&d2) > 0);

        d1.m[0] = 3;    // 3, -2
        assert!(d1.cmp(&d2) > 0);

        d2.sign = DECIMAL_SIGN_POS;    // 3, 2
        assert!(d1.cmp(&d2) > 0);

        d2.m[1] = 9;    // 3, 90002
        d2.n = 5;
        assert!(d1.cmp(&d2) < 0);

        d1.m[1] = 9;    // 90003, 90002
        d1.n = 5;
        assert!(d1.cmp(&d2) > 0);

        d2.m[0] = 3;    // 90003, 90003
        assert!(d1.cmp(&d2) == 0);

        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;    // -90003, -90003
        assert!(d1.cmp(&d2) == 0);


        println!("Testing additions");

        d2.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        for i in 0..DECIMAL_PARTS
        {
            d1.m[i] = 9999;
            d2.m[i] = 0;
        }
        d1.m[0] = 9990;
        d2.m[0] = 10;
        d1.n = DECIMAL_POSITIONS as i16;
        d2.n = 2;
        d2.e = DECIMAL_MAX_EXPONENT;
        d1.e = DECIMAL_MAX_EXPONENT;

        assert!(d1.add(&d2).unwrap_err() == Error::ExponentOverflow);

        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.add(&d2).unwrap_err() == Error::ExponentOverflow);

        d2.e = 0;
        d1.e = 0;
        ref_num.m.iter_mut().for_each(|x| *x = 0);
        ref_num.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 10;
        ref_num.sign = DECIMAL_SIGN_NEG;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = 1;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d2.sign = DECIMAL_SIGN_POS;
        ref_num.sign = DECIMAL_SIGN_NEG;
        for i in 0..DECIMAL_PARTS {
            ref_num.m[i] = 9999;
        }
        ref_num.m[0] = 9980;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = 0;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        ref_num.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_NEG;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        d1.m[1] = 9999;
        d2.m[1] = 9999;
        ref_num.m[1] = 9998;
        ref_num.m[2] = 1;
        d1.n = 8;
        d2.n = 8;
        ref_num.n = 9;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 + d2
        d1.m[1] = 0;
        d1.n = 0;
        d2.e = 3;
        ref_num = d2;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // d1 + 0
        d2.m[1] = 0;
        d2.n = 0;
        d2.e = 0;
        d1.m[1] = 11;
        d1.n = 6;
        d1.e = 123;
        ref_num = d1;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // different exponents and precisions
        d1 = BigFloat::new();
        d2 = BigFloat::new();

        for i in 0..DECIMAL_PARTS
        {
            d1.m[i] = 9999;
        }
        d1.n = DECIMAL_POSITIONS as i16;
        d1.e = 5;
        d2.m[0] = 11;
        d2.n = 2;
        d2.e = 3;
        ref_num = d1;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.e = 4;
        d2.m[0] = 11;
        d2.n = 2;
        d2.e = 3;
        ref_num.m.iter_mut().for_each(|x| *x = 0);
        ref_num.e = 5;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 10;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.e = 5;   // 0000 0022 2..2 2211 0000e+5 + 1122 3346e+3
        for i in 0..DECIMAL_PARTS
        {
            ref_num.m[i] = 2222;
            d1.m[i] = 2222;
        }
        d1.m[0] = 0;
        d1.m[1] = 2211;
        d1.m[DECIMAL_PARTS - 1] = 0;
        d1.m[DECIMAL_PARTS - 2] = 22;
        d1.n = DECIMAL_POSITIONS as i16 - 6;
        d2.m[0] = 3346;
        d2.m[1] = 1122;
        d2.n = 8;
        d2.e = 3;
        ref_num.e = 3;
        ref_num.m[0] = 3346;
        ref_num.m[DECIMAL_PARTS - 1] = 0;
        ref_num.n = DECIMAL_POSITIONS as i16 - 4;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.m[DECIMAL_PARTS - 1] = 222;  // 0222 2..2 2211 0000e+5 + 1122 3346e+3
        d1.m[DECIMAL_PARTS - 2] = 2222;
        d1.n = DECIMAL_POSITIONS as i16 - 1;
        ref_num.e = 4;
        ref_num.m[0] = 2334;
        ref_num.m[DECIMAL_PARTS - 1] = 2222;
        ref_num.n = DECIMAL_POSITIONS as i16;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);


        println!("Testing subtraction");

        d2.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_NEG;
        for i in 0..DECIMAL_PARTS {
            d1.m[i] = 9999;
            d2.m[i] = 0;
        }
        d1.m[0] = 9990;
        d2.m[0] = 10;
        d1.n = DECIMAL_POSITIONS as i16;
        d2.n = 2;
        d1.e = DECIMAL_MAX_EXPONENT;
        d2.e = DECIMAL_MAX_EXPONENT;
        assert!(d1.sub(&d2).unwrap_err() == Error::ExponentOverflow);

        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_POS;
        assert!(d1.sub(&d2).unwrap_err() == Error::ExponentOverflow);

        d1.e -= 1;
        ref_num.m.iter_mut().for_each(|x| *x = 0);
        ref_num.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 10;
        ref_num.m[0] = 9;
        ref_num.sign = DECIMAL_SIGN_POS;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = DECIMAL_MAX_EXPONENT;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;
        d1.e += 1;
        ref_num.sign = DECIMAL_SIGN_POS;
        for i in 0..DECIMAL_PARTS {
            ref_num.m[i] = 9999;
        }
        ref_num.m[0] = 9980;
        ref_num.n = DECIMAL_POSITIONS as i16;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        ref_num.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        d1.m[1] = 9998;
        d1.m[2] = 1;
        d1.n = 9;
        d2.m[1] = 9999;
        d2.n = 8;
        ref_num.m[1] = 9999;
        ref_num.n = 8;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // d1 - 0
        d2.m[1] = 0;
        d2.n = 0;
        d2.e = -5;
        d1.e = 5;
        ref_num = d1;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 - d2
        d1.m[1] = 0;
        d1.m[2] = 0;
        d1.n = 0;
        d2.m[3] = 345;
        d2.n = 15;
        ref_num = d2;
        ref_num.sign = -ref_num.sign;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);


        println!("Testing multiplication");

        // 0 * 0
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 99 0000 * 0
        d1.m[1] = 99;
        d1.n = 6;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 * 1234 9999
        d2.m[0] = 9999;
        d2.m[1] = 1234;
        d2.n = 8;
        d1.m[0] = 0;
        d1.m[1] = 0;
        d1.n = 0;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * 1
        d1.m[1] = 0;
        d2.m[1] = 0;
        d2.m[0] = 1;
        d1.m[0] = 1;
        ref_num.m[0] = 1;
        d1.n = 1;
        d2.n = 1;
        ref_num.n = 1;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * -1
        d2.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_NEG;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // -1 * 1
        d2.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_NEG;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // -1 * -1
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_POS;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 9999 * 9999
        d2.m[0] = 9999;
        d1.m[0] = 9999;
        d1.n = 4;
        d2.n = 4;
        ref_num.m[0] = 1;
        ref_num.m[1] = 9998;
        ref_num.n = 8;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 2 0000 9999 * 9999
        d1.m[2] = 2;
        d1.n = 9;
        ref_num.m[0] = 1;
        ref_num.m[1] = 9998;
        ref_num.m[2] = 9998;
        ref_num.m[3] = 1;
        ref_num.n = 13;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 2 0000 9999 * 5000 0000 9999
        d2.m[2] = 5000;
        d2.n = 12;
        ref_num.m[0] = 1;
        ref_num.m[1] = 9998;
        ref_num.m[2] = 4998;
        ref_num.m[3] = 5001;
        ref_num.m[4] = 0;
        ref_num.m[5] = 1;
        ref_num.n = 21;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // exponent modificaton and overflows
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();

        // 5000..0 * 2
        d1.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 2;
        d1.n = DECIMAL_POSITIONS as i16;
        d2.m[0] = 2;
        d2.n = 1;
        ref_num.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 10;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = 1;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // overflow
        d2.e = 123;
        d1.e = DECIMAL_MAX_EXPONENT - d2.e;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow);

        // no overflow
        d1.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/2-1;
        assert!(d1.mul(&d2).is_ok());

        // no overflow with negative e
        d1.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/2;
        d2.e = -123;
        d1.e = DECIMAL_MIN_EXPONENT + 122;  // d1.e + d2.e = min_exp - 1
        assert!(d1.mul(&d2).is_ok());

        // overflow with negative e
        d1.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/2-1;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow);

        // overflow
        d2.e = 123;
        d1.e = DECIMAL_MAX_EXPONENT - d2.e;
        d2.m[0] = 0;
        d1.m[DECIMAL_PARTS-1] = 0;
        d1.m[5] = 1;
        d2.m[5] = 1;
        d1.n = 21;
        d2.n = 21;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow);

        // no overflow
        d1.m[5] = 0;
        d1.m[0] = 9999;
        d1.m[1] = 9999;
        d1.m[2] = 9999;
        d1.m[3] = 9999;
        d1.m[4] = 9999;
        d1.n = 20;
        assert!(d1.mul(&d2).is_ok());

        // overflow
        for i in 0..DECIMAL_PARTS {
            d1.m[i] = 9999;
            d2.m[i] = 9999;
        }
        d1.n = DECIMAL_POSITIONS as i16;
        d2.n = DECIMAL_POSITIONS as i16;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow);


        println!("Testing division");

        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();

        // division by zero
        assert!(d1.div(&d2).unwrap_err() == Error::DivisionByZero);

        // 0 / d2
        d2.m[0] = 1;
        d2.n = 1;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d2.sign = DECIMAL_SIGN_NEG;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // division by single digit
        // 9998 / 3
        ref_num.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;
        d2.m[0] = 3;
        d2.n = 1;
        d1.m[0] = 9998;
        d1.n = 4;
        for i in 0..DECIMAL_PARTS-1 {
            ref_num.m[i] = 6666;
        }
        ref_num.m[DECIMAL_PARTS - 1] = 3332;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = -36;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1998 / 3
        ref_num.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;
        d2.m[0] = 3;
        d2.n = 1;
        d1.m[0] = 1998;
        d1.n = 1;
        for i in 0..DECIMAL_PARTS-1 {
            ref_num.m[i] = 0;
        }
        ref_num.m[DECIMAL_PARTS - 1] = 666;
        ref_num.n = DECIMAL_POSITIONS as i16 - 1;
        ref_num.e = -36;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 91998 / 33
        d1.m[1] = 9;
        d1.n = 5;
        d2.m[0] = 33;
        d2.n = 1;
        for i in 0..DECIMAL_PARTS-1 {
            ref_num.m[i] = 8181;
        }
        ref_num.m[DECIMAL_PARTS - 1] = 2787;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = -36;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 9999 9..9 9999 / 3
        for i in 0..DECIMAL_PARTS {
            d1.m[i] = 9999;
            ref_num.m[i] = 3333;
        }
        ref_num.e = 0;
        d1.n = DECIMAL_POSITIONS as i16;
        ref_num.n = DECIMAL_POSITIONS as i16;
        d2.m[0] = 3;
        d2.n = 1;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 3333 3..3 3333 / 9999
        for i in 0..DECIMAL_PARTS {
            d1.m[i] = 3333;
            ref_num.m[i] = if i%3 == 1 { 0 } else { 
                if i%3 == 2 { 6667 } else { 3333 }
            };
        }
        d2.m[0] = 9999;
        d2.n = 4;
        ref_num.e = -4;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // signs again but with non zero quotinent
        ref_num.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        ref_num.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_POS;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_POS;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);


        // division by divisor with two or more digits
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();

        // 1111 9999 9999 9999 / 3333 3333
        d1.m[3] = 1111;
        d1.m[2] = 9999;
        d1.m[1] = 9999;
        d1.m[0] = 9999;
        d1.n = 16;
        d2.m[1] = 3333;
        d2.m[0] = 3333;
        d2.n = 8;
        for i in 0..DECIMAL_PARTS-2 {
            ref_num.m[i] = if i % 2 > 0 { 3335 } else { 9997 };
        }
        ref_num.m[DECIMAL_PARTS - 2] = 0;
        ref_num.m[DECIMAL_PARTS - 1] = 3336;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = -32;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 9999 9999. 9999 9999 / 3333 3333
        ref_num.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;
        d1.e = -8;
        d2.e = 0;
        d1.m[3] = 9999;
        d1.m[2] = 9999;
        d1.m[1] = 9999;
        d1.m[0] = 9999;
        d1.n = 16;
        d2.m[1] = 3333;
        d2.m[0] = 3333;
        d2.n = 8;
        ref_num.m.iter_mut().for_each(|x| *x = 0);
        ref_num.m[DECIMAL_PARTS - 1] = 3;
        ref_num.m[DECIMAL_PARTS - 3] = 3;
        ref_num.m[DECIMAL_PARTS - 2] = 0;
        ref_num.n = 37;
        ref_num.e = -36;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 9999 9999. 9999 9999 / 6666 6666
        ref_num.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_POS;
        d2.m[1] = 6666;
        d2.m[0] = 6666;
        ref_num.m[DECIMAL_PARTS-1] = 1;
        ref_num.m[DECIMAL_PARTS-3] = 1;
        ref_num.m[DECIMAL_PARTS-2] = 5000;
        ref_num.m[DECIMAL_PARTS-4] = 5000;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 6666 6665 / 6666 6666
        ref_num.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_POS;
        d1.m[3] = 0;
        d1.m[2] = 0;
        d1.m[0] = 6665;
        d1.m[1] = 6666;
        d2.m[1] = 6666;
        d2.m[0] = 6666;
        d1.e = DECIMAL_MAX_EXPONENT;
        d2.e = DECIMAL_MAX_EXPONENT;
        d1.n = 8;
        d2.n = 8;
        for i in 0..DECIMAL_PARTS - 1 {
            ref_num.m[i] = if i % 2 == 0 { 9998 } else { 4999 };
        }
        ref_num.m[DECIMAL_PARTS - 1] = 9999;
        ref_num.n = 40;
        ref_num.e = -40;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // special cases for 100% coverage of Knuth's div
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_POS;
        d1.e = DECIMAL_MIN_EXPONENT;
        d2.e = DECIMAL_MIN_EXPONENT;
        d1.m[4] = 6666;
        d1.m[3] = 6666;
        d1.m[2] = 0;
        d1.m[1] = 0;
        d1.m[0] = 0;
        d1.n = 20;
        d2.m[2] = 6666;
        d2.m[1] = 6666;
        d2.m[0] = 9999;
        d2.n = 12;
        ref_num.m[9] = 9999;
        ref_num.m[8] = 9998;
        ref_num.m[7] = 5001;
        ref_num.m[6] = 5000;
        ref_num.m[5] = 7497;
        ref_num.m[4] = 1;
        ref_num.m[3] = 8752;
        ref_num.m[2] = 6244;
        ref_num.m[1] = 5626;
        ref_num.m[0] = 5006;
        ref_num.n = 40;
        ref_num.e = -32;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.m[4] = 0;
        d1.m[3] = 0;
        d1.m[2] = 4999;
        d1.m[1] = 9997;
        d1.m[0] = 0;
        d1.n = 12;
        d1.e = -4;
        d2.m[2] = 0;
        d2.m[1] = 5003;
        d2.m[0] = 9999;
        d2.n = 8;
        d2.e = 3;
        ref_num.m[9] = 9992;
        ref_num.m[8] = 59;
        ref_num.m[7] = 9504;
        ref_num.m[6] = 4084;
        ref_num.m[5] = 6331;
        ref_num.m[4] = 7515;
        ref_num.m[3] = 2541;
        ref_num.m[2] = 4698;
        ref_num.m[1] = 7492;
        ref_num.m[0] = 9453;
        ref_num.n = 40;
        ref_num.e = -43;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // overflow
        d2.e = -35;
        d1.e = DECIMAL_MIN_EXPONENT;
        assert!(d1.div(&d2).unwrap_err() == Error::ExponentOverflow);

        d2.e = -37;
        d1.e = DECIMAL_MAX_EXPONENT;
        assert!(d1.div(&d2).unwrap_err() == Error::ExponentOverflow);


        println!("Testing abs");

        d1 = BigFloat::new();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.abs().sign == DECIMAL_SIGN_POS);
        d1.sign = DECIMAL_SIGN_POS;
        assert!(d1.abs().sign == DECIMAL_SIGN_POS);


        println!("Testing sqrt");

        let mut epsilon = BigFloat::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);

        d1 = BigFloat::new();
        d1.m[0] = 10;
        d1.n = 2;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) < 0);


        // sqrt(1234567890.1234567 = 1.2345...+10^9)
        d1 = BigFloat::new();
        d1.m[0] = 4567;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 1;
        d1.n = 17;
        d1.e = -7;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        epsilon.e = -69;    // 1*10^(-30)
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);

        // positive exponent
        d1 = BigFloat::new();
        d1.m[0] = 4567;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 1;
        d1.n = 17;
        d1.e = 7;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        epsilon.e = -55;    // 1*10^(-16)
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);

        // value less than 1
        d1 = BigFloat::new();
        d1.m[0] = 4567;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 1;
        d1.n = 17;
        d1.e = -20;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        epsilon.e = -82;    // 1*10^(-43)
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);

        // value is negative
        d1 = BigFloat::new();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.sqrt().unwrap_err() == Error::ArgumentIsNegative);

/*
        d1 = BigFloat::new();
        d1.m[0] = 4567;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 1;
        d1.m[5] = 1;
        d1.m[6] = 1;
        d1.m[7] = 1;
        d1.m[8] = 1;
        d1.e = -7;
        for i in 1..10000 {
            d1.m[9] = i;
            d1.m[0] = i;
            d1.n = 36 + if i < 10 {1} else if i < 100 {2} else if i < 1000 {3} else {4} ;
            let ret = d1.sqrt().unwrap();
            let ret = ret.mul(&ret).unwrap();
            assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) < 0);
        }

        // print precalculated values
        println!("const SQRT_VALUES: [990; BigFloat] = [");
        let mut idx = 0;
        for i in 0..10 {
            for j in 1..100 {
                d1 = BigFloat::new();
                d1.m[i] = j*100;
                d1.n = (i*DECIMAL_BASE_LOG10 + if j < 10 {3} else {4} ) as i16;
                idx += 1;
                let ret = d1.sqrt().unwrap();
            }
        }
*/


        println!("Testing pow");

        d1 = BigFloat::new();
        d2 = BigFloat::new();
        d2.m[0] = 2;
        d2.n = 1;
        d1.m[0] = 2345;
        d1.m[1] = 8901;
        d1.m[2] = 4567;
        d1.m[3] = 123;
        d1.n = 15;
        d1.e = -12;
        d2.pow(&d1).unwrap();


        // zero number
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        d1.m[0] = 123;
        d1.n = 3;
        d1.e = -1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // zero argument
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        ref_num.m[0] = 1;
        ref_num.n = 1;
        d2.m[0] = 123;
        d2.n = 3;
        d2.e = -1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // argument is too large
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        d2.m[0] = 2;
        d2.n = 1;
        d1.m[0] = 123;
        d1.n = 3;
        d1.e = 1;
        assert!(d2.pow(&d1).unwrap_err() == Error::ExponentOverflow);

        // argument is too small
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        ref_num.m[0] = 1;
        ref_num.n = 1;
        d1.m[0] = 123;
        d1.m[1] = 123;
        d1.n = 7;
        d1.e = -47;
        d2.m[0] = 2;
        d2.n = 1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // 2^123.4567890
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        ref_num.m[0] = 5307;
        ref_num.m[1] = 7857;
        ref_num.m[2] = 6147;
        ref_num.m[3] = 8828;
        ref_num.m[4] = 46;
        ref_num.m[5] = 873;
        ref_num.m[6] = 5984; 
        ref_num.m[7] = 9057; 
        ref_num.m[8] = 4749; 
        ref_num.m[9] = 1459;
        ref_num.n = 40;
        ref_num.e = -2;
        d1.m[0] = 7890;
        d1.m[1] = 3456;
        d1.m[2] = 12;
        d1.n = 10;
        d1.e = -7;
        d2.m[0] = 2;
        d2.n = 1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // negative argument
        ref_num = one.div(&ref_num).unwrap();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        let mut ret;
        let mut inv;
        d2 = BigFloat::new();
        d2.m[0] = 4560;
        d2.m[1] = 123;
        d2.m[2] = 6789;
        d2.m[3] = 2345;
        d2.m[4] = 651;
        d2.m[5] = 41;
        d2.m[6] = 671;
        d2.m[7] = 100;
        d2.m[8] = 10;
        d2.m[9] = 9999;
        d2.n = DECIMAL_POSITIONS as i16;
        d2.e = -38;
        d1 = BigFloat::new();
        d1.m[0] = 2;
        d1.m[1] = 0;
        d1.m[2] = 0;
        d1.n = 1;
        epsilon.e = -77; // 1*10^(-38)
        d1.e = 0;
        for i in 1..100 {
            for j in 0..10 {
                d2.m[2] = i;
                d2.m[5] = i;
                d1.m[1] = j*1000;
                d1.m[2] = 10+j;
                inv = one.div(&d1).unwrap();
                ret = d2.pow(&d1).unwrap();
                ret = ret.pow(&inv).unwrap();
                assert!(d2.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);
            }
        }


        println!("Testing ln");

        // arg = 0
        d1 = BigFloat::new();
        assert!(d1.ln().unwrap_err() == Error::InvalidArgument);

        // arg < 0
        d1 = BigFloat::one();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.ln().unwrap_err() == Error::InvalidArgument);

        // ln of E = 1
        epsilon.e = -77;    // 1*10^(-39)
        assert!(E.ln().unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);

        d2 = BigFloat::new();
        d2.m[0] = 4567;
        d2.m[1] = 123;
        d2.m[2] = 6789;
        d2.m[3] = 2345;
        d2.m[4] = 651;
        d2.m[5] = 41;
        d2.m[6] = 671;
        d2.m[7] = 100;
        d2.m[8] = 10;
        d2.m[9] = 9999;
        d2.n = DECIMAL_POSITIONS as i16;
        d2.e = -10;
        for i in 0..100 {
            d2.m[2] = i;
            d2.m[5] = i;
            d2.e = -50 + (i%100) as i8;
            epsilon.e = d2.e - 36;  // 1*10^(1 + d2.e)
            ret = d2.ln().unwrap();
            d1 = E.pow(&ret).unwrap();
            assert!(d2.sub(&d1).unwrap().abs().cmp(&epsilon) <= 0);
        }


        println!("Testing sin and cos");

        d1 = BigFloat::new();
        d1.e = -39;
        d1.m[8] = 123;
        epsilon.e = -77; // 1*10^(-38)
        for i in 1..9999 {
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else {if i<100 {2} else {if i<1000 {3} else {4}}} + 36;
            let s = d1.sin().unwrap();
            let c = d1.cos().unwrap();
            let p = s.mul(&s).unwrap().add(&c.mul(&c).unwrap()).unwrap();
            assert!(p.sub(&one).unwrap().abs().cmp(&epsilon) <= 0);
        }


        println!("Testing tan");

        d1 = BigFloat::new();
        d1.e = -39;
        d1.m[0] = 5678;
        d1.m[8] = 1234;
        epsilon.e = -73; // 1*10^(-34) for arguments close to pi/2 the precision is lost
        for i in 0..9999 {
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else {if i<100 {2} else {if i<1000 {3} else {4}}} + 36;
            let t1 = d1.tan().unwrap();
            let t2 = d1.sin().unwrap().div(&d1.cos().unwrap()).unwrap();
            let p = t1.div(&t2).unwrap();
            assert!(p.sub(&one).unwrap().abs().cmp(&epsilon) <= 0);
        }


        println!("Testing conversions");

        for _ in 0..1000 {
            let i: i8 = random::<i8>() % 10i8;
            let mut f: f64 = random::<f64>().powf(i as f64);
            if i & 1 == 0 {
                f = -f;
            }
            d1 = BigFloat::from_f64(f).unwrap();
            let f2 = d1.to_f64();
            if f2 != 0f64 {
                assert!((1f64 - f/f2).abs() < 0.000000000000001f64);
            } else {
                assert!((f - f2).abs() < 0.000000000000001f64);
            }
        }

        for _ in 0..1000 {
            let i: i8 = random::<i8>() % 10i8;
            let mut f: f32 = random::<f32>().powf(i as f32);
            if i & 1 == 0 {
                f = -f;
            }
            d1 = BigFloat::from_f32(f).unwrap();
            let f2 = d1.to_f32();
            if f2 != 0f32 {
                assert!((1f32 - f/f2).abs() < 0.000001f32);
            } else {
                assert!((f - f2).abs() < 0.000001f32);
            }
        }
    }
}
