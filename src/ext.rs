//! BigFloat number whith support of `NaN`, and `Inf` 
//! values, and implementation of `std::ops` traits.

use crate::defs::{BigFloatNum, Error, DECIMAL_SIGN_POS, DECIMAL_PARTS, DECIMAL_SIGN_NEG, DECIMAL_POSITIONS,
    DECIMAL_MAX_EXPONENT, DECIMAL_MIN_EXPONENT};

/// Maximum value possible.
pub const MAX: BigFloat = BigFloat {inner: Flavor::Value(crate::defs::MAX)};

/// Maximum possible exponent.
pub const MAX_EXP: i8 = DECIMAL_MAX_EXPONENT;

/// Minumum value possible.
pub const MIN: BigFloat = BigFloat {inner: Flavor::Value(crate::defs::MIN)};

/// Minumum possible exponent.
pub const MIN_EXP: i8 = DECIMAL_MIN_EXPONENT;

/// Smalles positive number.
pub const MIN_POSITIVE: BigFloat = BigFloat {inner: Flavor::Value(crate::defs::MIN_POSITIVE)};

/// Radix of BigFloat
pub const RADIX: u32 = 10;

/// NaN representation.
pub const NAN: BigFloat = BigFloat { inner: Flavor::NaN };

/// Positive infinity.
pub const INF_POS: BigFloat = BigFloat { inner: Flavor::Inf(DECIMAL_SIGN_POS) };

/// Negative infinity.
pub const INF_NEG: BigFloat = BigFloat { inner: Flavor::Inf(DECIMAL_SIGN_NEG) };

/// Value of zero.
pub const ZERO: BigFloat = BigFloat { inner: Flavor::Value(crate::defs::ZERO) };

/// Value of one.
pub const ONE: BigFloat = BigFloat { inner: Flavor::Value(crate::defs::ONE) };

/// Value of two.
pub const TWO: BigFloat = BigFloat { inner: Flavor::Value(crate::defs::TWO) };

/// Euler's number.
pub const E: BigFloat = BigFloat { inner: Flavor::Value(crate::defs::E) };

/// PI number.
pub const PI: BigFloat = BigFloat { inner: Flavor::Value(crate::defs::PI) };

/// PI/2
pub const HALF_PI: BigFloat = BigFloat { inner: Flavor::Value(BigFloatNum {
    m: [2099, 5144, 6397, 1691, 3132, 6192, 4896, 2679, 7963, 1570],
    n: DECIMAL_POSITIONS as i16, 
    sign: DECIMAL_SIGN_POS, 
    e: -(DECIMAL_POSITIONS as i8 - 1),
})};

/// Number representation.
#[derive(Copy, Clone, Debug)]
pub struct BigFloat {
    inner: Flavor,
}

#[derive(Copy, Clone, Debug)]
enum Flavor {
    Value(BigFloatNum),
    NaN,
    Inf(i8)         // signed Inf
}

impl BigFloat {

    /// Return new BigFloat with value zero.
    pub fn new() -> Self {
        BigFloat {
            inner: Flavor::Value(BigFloatNum::new())
        }
    }
 

    /// Create a BigFloat value from a sequence of `bytes`. Each byte must represent a decimal digit.
    /// First byte is the most significant. The length of `bytes` can be any. If the length of
    /// `bytes` is greater than required, then the remaining part is ignored.
    /// If `sign` is negative, then the resulting BigFloat will be
    /// negative.
    pub fn from_bytes(bytes: &[u8], sign: i8, exponent: i8) -> Self {
        BigFloat {
            inner: Flavor::Value(BigFloatNum::from_bytes(bytes, sign, exponent))
        }
    }

    /// Construct BigFloat from f64 value.
    /// The conversion is not guaranteed to be lossless, since BigFloat and f64 have different radix.
    pub fn from_f64(f: f64) -> Self {
        #[cfg(feature = "std")] {
            let strepr = format!("{:e}", f);
            Self::parse(&strepr).unwrap()
        }
        #[cfg(not(feature = "std"))] {
            let inner = match BigFloatNum::from_f64(f) {
                Err(e) => match e {
                    Error::ExponentOverflow(s) => Flavor::Inf(s),
                    _ => Flavor::NaN,
                },
                Ok(v) => Flavor::Value(v),
            };
            BigFloat {
                inner
            }
        }
    }

    /// Construct BigFloat from f32 value.
    /// The conversion is not guaranteed to be lossless, since BigFloat and f32 have different radix.
    pub fn from_f32(f: f32) -> Self {
        Self::from_f64(f as f64)
    }

    /// Convert BigFloat to f64.
    pub fn to_f64(&self) -> f64 {
        match self.inner {
            Flavor::Value(v) => v.to_f64(),
            Flavor::Inf(s) => if s == DECIMAL_SIGN_POS {
                f64::INFINITY
            } else {
                f64::NEG_INFINITY
            },
            Flavor::NaN => f64::NAN,
        }
    }

    /// Convert BigFloat to f32.
    pub fn to_f32(&self) -> f32 {
        match self.inner {
            Flavor::Value(v) => v.to_f32(),
            Flavor::Inf(s) => if s == DECIMAL_SIGN_POS {
                f32::INFINITY
            } else {
                f32::NEG_INFINITY
            },
            Flavor::NaN => f32::NAN,
        }
    }

    /// Get BigFloat's mantissa as bytes. Each byte represents a decimal digit.
    /// First byte is the most significant. The length of `bytes` can be any. If the length of
    /// `bytes` is smaller than required, then remaining part of mantissa will be omitted.
    ///
    /// The length of mantissa can be determined using `get_mantissa_len`.
    /// If `self` is Inf or NaN nothing is returned.
    pub fn get_mantissa_bytes(&self, bytes: &mut [u8]) {
        if let Flavor::Value(v) = self.inner {
            v.get_mantissa_bytes(bytes);
        }
    }

    /// Return the number of decimal positions filled in the mantissa.
    /// If `self` is Inf or NaN 0 is returned.
    pub fn get_mantissa_len(&self) -> usize {
        match self.inner {
            Flavor::Value(v) => v.get_mantissa_len(),
            _ => 0,
        }
    }

    /// Return 1 if BigFloat is positive, -1 otherwise.
    /// If `self` is NaN 0 is returned.
    pub fn get_sign(&self) -> i8 {
        match self.inner {
            Flavor::Value(v) => v.sign,
            Flavor::Inf(s) => s,
            _ => 0,
        }
    }

    /// Return exponent part.
    /// If `self` is Inf or NaN 0 is returned.
    pub fn get_exponent(&self) -> i8 {
        match self.inner {
            Flavor::Value(v) => v.e,
            _ => 0,
        }
    }


    /// Sets exponent part of `self`.
    /// Function has no effect on Inf and NaN values.
    pub fn set_exponent(&mut self, e: i8) {
        if let Flavor::Value(mut v) = self.inner { 
            v.e = e;
            self.inner = Flavor::Value(v);
        }
    }

    /// Return raw parts of BigFloat: mantissa, number of decimal positions in mantissa, sing, and
    /// exponent.
    /// If `self` is Inf or NaN None is returned.
    pub fn to_raw_parts(&self) -> Option<([i16; DECIMAL_PARTS], i16, i8, i8)> {
        match self.inner {
            Flavor::Value(v) => Some((v.m, v.n, v.sign, v.e)),
            _ => None,
        }
    }

    /// Construct BigFloat from raw parts.
    pub fn from_raw_parts(mantissa: [i16; DECIMAL_PARTS], mantissa_len: i16, sign: i8, exponent: i8) -> Self {
        let val = BigFloatNum {
            sign,
            e: exponent,
            n: mantissa_len,
            m: mantissa,
        };
        BigFloat { 
            inner: Flavor::Value(val) 
        }
    }

    /// Return true if self is positive infinity.
    pub fn is_inf_pos(&self) -> bool {
        matches!(self.inner, Flavor::Inf(DECIMAL_SIGN_POS))
    }

    /// Return true if self is negative infinity.
    pub fn is_inf_neg(&self) -> bool {
        matches!(self.inner, Flavor::Inf(DECIMAL_SIGN_NEG))
    }

    /// Return true if self is infinite.
    pub fn is_inf(&self) -> bool {
        self.is_inf_pos() || self.is_inf_neg()
    }

    /// Return true if self is not a number.
    pub fn is_nan(&self) -> bool {
        matches!(self.inner, Flavor::NaN)
    }

    /// Add d2 and return result of addition.
    pub fn add(&self, d2: &Self) -> Self {
        match self.inner {
            Flavor::Value(v1) => {
                match d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.add(&v2), v1.is_zero(), v1.sign == v2.sign)
                    },
                    Flavor::Inf(s2) => {
                        BigFloat { inner: Flavor::Inf(s2) }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match d2.inner {
                    Flavor::Value(_) => {
                        BigFloat { inner: Flavor::Inf(s1) }
                    },
                    Flavor::Inf(s2) => {
                        if s1 != s2 {
                            NAN
                        } else {
                            BigFloat { inner: Flavor::Inf(s2) }
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Subtract d2 and return result of subtraction.
    pub fn sub(&self, d2: &Self) -> Self {
        match self.inner {
            Flavor::Value(v1) => {
                match d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.sub(&v2), v1.is_zero(), v1.sign == v2.sign)
                    },
                    Flavor::Inf(s2) => {
                        if s2 == DECIMAL_SIGN_POS {
                            INF_NEG
                        } else {
                            INF_POS
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match d2.inner {
                    Flavor::Value(_) => {
                        BigFloat { inner: Flavor::Inf(s1) }
                    },
                    Flavor::Inf(s2) => {
                        if s1 == s2 {
                            NAN
                        } else {
                            BigFloat { inner: Flavor::Inf(s1) }
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Multiply by d2 and return result of multiplication.
    pub fn mul(&self, d2: &Self) -> Self {
        match self.inner {
            Flavor::Value(v1) => {
                match d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.mul(&v2), v1.is_zero(), v1.sign == v2.sign)
                    },
                    Flavor::Inf(s2) => {
                        if v1.is_zero() { // 0*inf
                            NAN
                        } else {
                            let s = if v1.sign == s2 {
                                DECIMAL_SIGN_POS
                            } else {
                                DECIMAL_SIGN_NEG
                            };
                            BigFloat { inner: Flavor::Inf(s) }
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match d2.inner {
                    Flavor::Value(v2) => {
                        if v2.is_zero() { // inf*0
                            NAN
                        } else {
                            let s = if v2.sign == s1 {
                                DECIMAL_SIGN_POS
                            } else {
                                DECIMAL_SIGN_NEG
                            };
                            BigFloat { inner: Flavor::Inf(s) }
                        }
                    },
                    Flavor::Inf(s2) => {
                        let s = if s1 == s2 {
                            DECIMAL_SIGN_POS
                        } else {
                            DECIMAL_SIGN_NEG
                        };
                        BigFloat { inner: Flavor::Inf(s) }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Divide by d2 and return result of division.
    pub fn div(&self, d2: &Self) -> Self {
        match self.inner {
            Flavor::Value(v1) => {
                match d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.div(&v2), v1.is_zero(), v1.sign == v2.sign)
                    },
                    Flavor::Inf(_) => {
                        ZERO
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match d2.inner {
                    Flavor::Value(v) => {
                        if s1 == v.sign {
                            INF_POS
                        } else {
                            INF_NEG
                        }
                    },
                    Flavor::Inf(_) => {
                        NAN
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Compare to d2.
    /// Returns positive if self > d2, negative if self < d2, zero if self == d2, `None` if `self` or `d2` is NaN.
    pub fn cmp(&self, d2: &BigFloat) -> Option<i16> {
        match self.inner {
            Flavor::Value(v1) => {
                match d2.inner {
                    Flavor::Value(v2) => {
                        Some(v1.cmp(&v2))
                    }
                    Flavor::Inf(s2) => {
                        if s2 == DECIMAL_SIGN_POS {
                            Some(-1)
                        } else {
                            Some(1)
                        }
                    },
                    Flavor::NaN => None,
                }
            },
            Flavor::Inf(s1) => {
                match d2.inner {
                    Flavor::Value(_) => {
                        Some(s1 as i16)
                    }
                    Flavor::Inf(s2) => {
                        Some((s1 - s2) as i16)
                    },
                    Flavor::NaN => None,
                }
            },
            Flavor::NaN => None,
        }
    }

    /// Changes sign of a number to opposite.
    pub fn inv_sign(&self) -> BigFloat {
        match self.inner {
            Flavor::Value(mut v1) => {
                if v1.sign == DECIMAL_SIGN_POS {
                    v1.sign = DECIMAL_SIGN_NEG;
                } else {
                    v1.sign = DECIMAL_SIGN_POS;
                }
                BigFloat {inner: Flavor::Value(v1)}
            },
            Flavor::Inf(s1) => if s1 == DECIMAL_SIGN_POS {INF_NEG} else {INF_POS},
            Flavor::NaN => NAN,
        }
    }

    /// Return BigFloat to the power of `d1`.
    pub fn pow(&self, d1: &Self) -> Self {
        match self.inner {
            Flavor::Value(v1) => {
                match d1.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.pow(&v2), v1.is_zero(), v1.sign == v2.sign)
                    },
                    Flavor::Inf(s2) => {
                        // v1^inf
                        let val = v1.cmp(&BigFloatNum::one());
                        if val > 0 {
                            BigFloat { inner: Flavor::Inf(s2) }
                        } else if val < 0 {
                            ZERO
                        } else {
                            ONE
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match d1.inner {
                    Flavor::Value(v2) => {
                        // inf ^ v2
                        let val = v2.cmp(&BigFloatNum::new());
                        if val > 0 {
                            if s1 == DECIMAL_SIGN_NEG &&
                                v2.frac().is_zero() &&
                                !v2.is_int_even() {
                                    // v2 is odd without fractional part. 
                                    INF_NEG
                            } else {
                                INF_POS
                            }
                        } else if val < 0 {
                            ZERO
                        } else {
                            ONE
                        }
                    },
                    Flavor::Inf(s2) => {
                        // inf^inf
                        if s2 == DECIMAL_SIGN_POS {
                            INF_POS
                        } else {
                            ZERO
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Returns logarithm of base `b` of a number.
    pub fn log(&self, b: &Self) -> Self {
        match self.inner {
            Flavor::Value(v1) => {
                match b.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.log(&v2), false, true)
                    },
                    Flavor::Inf(s2) => {
                        // v1.log(inf)
                        if s2 == DECIMAL_SIGN_POS {
                            ZERO
                        } else {
                            NAN
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                if s1 == DECIMAL_SIGN_NEG {
                    // -inf.log(any)
                    NAN
                } else {
                    match b.inner {
                        Flavor::Value(v2) => {
                            // +inf.log(v2)
                            let val = v2.cmp(&BigFloatNum::one());
                            if val < 0 {
                                INF_NEG
                            } else {
                                INF_POS
                            }
                        },
                        Flavor::Inf(_) => NAN, // +inf.log(inf)
                        Flavor::NaN => NAN,
                    }
                }
            },
            Flavor::NaN => NAN,
        }
    }

    fn result_to_ext(res: Result<BigFloatNum, Error>, is_dividend_zero: bool, is_same_sign: bool) -> BigFloat {
        match res {
            Err(e) => match e {
                Error::ExponentOverflow(s) => if s == DECIMAL_SIGN_POS { INF_POS } else { INF_NEG },
                Error::DivisionByZero => {
                    if is_dividend_zero {
                        NAN
                    } else if is_same_sign {
                        INF_POS
                    } else {
                        INF_NEG
                    }
                },
                Error::ArgumentIsNegative => NAN,
                Error::InvalidArgument => NAN,
            },
            Ok(v) => BigFloat {inner: Flavor::Value(v)},
        }
    }

    /// Returns true if `self` is positive.
    pub fn is_positive(&self) -> bool {
        match self.inner {
            Flavor::Value(v) => v.sign == DECIMAL_SIGN_POS,
            Flavor::Inf(s) => s == DECIMAL_SIGN_POS,
            Flavor::NaN => false,
        }
    }

    /// Returns true if `self` is negative.
    pub fn is_negative(&self) -> bool {
        match self.inner {
            Flavor::Value(v) => v.sign == DECIMAL_SIGN_NEG,
            Flavor::Inf(s) => s == DECIMAL_SIGN_NEG,
            Flavor::NaN => false,
        }
    }

    /// Returns true if `self` is subnormal. 
    /// Number is considered subnormal if not all places of mantissa are used, and exponent has minimum possible value.
    pub fn is_subnormal(&self) -> bool {
        if let Flavor::Value(v) = self.inner {
            return v.is_subnormal()
        }
        false
    }

    /// Returns true if `self` is zero.
    pub fn is_zero(&self) -> bool {
        match self.inner {
            Flavor::Value(v) => v.is_zero(),
            Flavor::Inf(_) => false,
            Flavor::NaN => false,
        }
    }

    /// Restrict value of `self` to an interval determined by values of `min` and `max`.
    /// Returns `max` if `self` is greater than `max`, `min` if `self` is less than `min`, and `self` otherwise.
    /// If any of the arguments is `NAN` or `min` is greater than `max`, the function returns `NAN`.
    pub fn clamp(&self, min: &Self, max: &Self) -> Self {
        if self.is_nan() || min.is_nan() || max.is_nan() || max.cmp(min).unwrap() < 0 {
            NAN
        } else if self.cmp(min).unwrap() < 0 {
            *min
        } else if self.cmp(max).unwrap() > 0 {
            *max
        } else {
            *self
        }
    }

    /// Returns value of `d1` if `d1` is greater than `self`, or the value of `self` otherwise.
    /// If any of the arguments is `NAN`, the function returns `NAN`.
    pub fn max(&self, d1: &Self) -> Self {
        if self.is_nan() || d1.is_nan() {
            NAN
        } else if self.cmp(d1).unwrap() < 0 {
            *d1
        } else {
            *self
        }
    }

    /// Returns value of `d1` if `d1` is less than `self`, or the value of `self` otherwise.
    /// If any of the arguments is `NAN`, the function returns `NAN`.
    pub fn min(&self, d1: &Self) -> Self {
        if self.is_nan() || d1.is_nan() {
            NAN
        } else if self.cmp(d1).unwrap() > 0 {
            *d1
        } else {
            *self
        }
    }

    /// Returns BigFloat with value `-1` if `self` is negative, `+1` if `self` is positive or zero.
    /// Returns `NAN` If self is `NAN`.
    pub fn signum(&self) -> Self {
        if self.is_nan() {
            NAN
        } else if self.is_negative() {
            ONE.inv_sign()
        } else {
            ONE
        }
    }


    /// Parse the number from string `s`. 
    /// Function expects `s` to be a number in scientific format with base 10, or +-Inf, or NaN.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use num_bigfloat::BigFloat;
    /// 
    /// let n = BigFloat::parse("0.0").unwrap();
    /// assert!(n.to_f64() == 0.0);
    /// let n = BigFloat::parse("1.123e-123").unwrap();
    /// assert!((n.to_f64() - 1.123e-123).abs() < f64::EPSILON);
    /// let n = BigFloat::parse("-Inf").unwrap();
    /// assert!(n.to_f64() == f64::NEG_INFINITY);
    /// let n = BigFloat::parse("NaN").unwrap();
    /// assert!(n.to_f64().is_nan());
    /// ```
    #[cfg(feature = "std")]
    pub fn parse(s: &str) -> Option<Self> {
        let ps = crate::parser::parse(s);
        if ps.is_valid() {
            if ps.is_inf() {
                if ps.sign() == DECIMAL_SIGN_POS {
                    Some(INF_POS)
                } else {
                    Some(INF_NEG)
                }
            } else if ps.is_nan() {
                Some(NAN)
            } else {
                let (m, _n, s, e) = ps.raw_parts();
                let mut num = BigFloatNum::from_bytes(&m, s, 0);
                if num.n == 0 {
                    return Some(ZERO);
                }
                if e < DECIMAL_MIN_EXPONENT as i32 {
                    if e > DECIMAL_MIN_EXPONENT as i32 - num.n as i32 {
                        BigFloatNum::shift_right(&mut num.m, (DECIMAL_MIN_EXPONENT as i32 - e) as usize);
                        num.n = (num.n as i32 - DECIMAL_MIN_EXPONENT as i32 + e) as i16;
                        num.e = DECIMAL_MIN_EXPONENT;
                    } else {
                        return Some(ZERO);
                    }
                } else if e > DECIMAL_MAX_EXPONENT as i32 {
                    return Some(BigFloat {inner: Flavor::Inf(s)});
                } else {
                    num.e = e as i8;
                }
                Some(BigFloat {inner: Flavor::Value(num)})
            }
        } else {
            None
        }
    }
}


macro_rules! gen_wrapper2 {
    // unwrap error, function requires self as argument
    ($comment:literal, $fname:ident, $ret:ty, $pos_inf:block, $neg_inf:block, $($arg:ident, $arg_type:ty),*) => {
        #[doc=$comment]
        pub fn $fname(&self$(,$arg: $arg_type)*) -> $ret {
            match self.inner {
                Flavor::Value(v) => Self::result_to_ext(v.$fname($($arg,)*), v.is_zero(), true),
                Flavor::Inf(s) => if s == DECIMAL_SIGN_POS $pos_inf else $neg_inf,
                Flavor::NaN => NAN,
            }
        }
    };
}

macro_rules! gen_wrapper4 {
    // function requires self as argument
    ($comment:literal, $fname:ident, $ret:ty, $pos_inf:block, $neg_inf:block, $($arg:ident, $arg_type:ty),*) => {
        #[doc=$comment]
        pub fn $fname(&self$(,$arg: $arg_type)*) -> $ret {
            let inner = match self.inner {
                Flavor::Value(v) => Flavor::Value(v.$fname($($arg,)*)),
                Flavor::Inf(s) => if s == DECIMAL_SIGN_POS $pos_inf else $neg_inf,
                Flavor::NaN => Flavor::NaN,
            };
            BigFloat {
                inner
            }
        }
    };
}

impl BigFloat {
    
    gen_wrapper4!("Return absolute value.", abs, Self, {Flavor::Inf(DECIMAL_SIGN_POS)}, {Flavor::Inf(DECIMAL_SIGN_POS)},);
    gen_wrapper4!("Return integer part of a number,", int, Self, {Flavor::NaN}, {Flavor::NaN},);
    gen_wrapper4!("Return fractional part of a number.", frac, Self, {Flavor::NaN}, {Flavor::NaN},);
    gen_wrapper2!("Returns the smallest integer greater than or equal to a number.", ceil, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper2!("Returns the largest integer less than or equal to a number.", floor, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper2!("Returns the rounded number with `n` decimal positions in the fractional part of the number.", round, Self, {INF_POS}, {INF_NEG}, n, usize);
    
    gen_wrapper2!("Return square root of a number.", sqrt, Self, {INF_POS}, {NAN},);
    gen_wrapper2!("Return cube root of a number.", cbrt, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper2!("Returns natural logarithm of a number.", ln, Self, {INF_POS}, {NAN},);
    gen_wrapper2!("Returns logarithm base 2 of a number.", log2, Self, {INF_POS}, {NAN},);
    gen_wrapper2!("Returns logarithm base 10 of a number.", log10, Self, {INF_POS}, {NAN},);
    gen_wrapper2!("Returns `e` to the power of `self`.", exp, Self, {INF_POS}, {INF_NEG},);
    
    gen_wrapper2!("Returns sine of a number. Argument is an angle in radians.", sin, Self, {NAN}, {NAN},);
    gen_wrapper2!("Returns cosine of a number. Argument is an angle in radians.", cos, Self, {NAN}, {NAN},);
    gen_wrapper2!("Returns tangent of a number. Argument is an angle in radians.", tan, Self, {NAN}, {NAN},);
    gen_wrapper2!("Returns arcsine of a number. Result is an angle in radians ranging from `-pi/2` to `pi/2`.", asin, Self, {NAN}, {NAN},);
    gen_wrapper2!("Returns arccosine of a number.", acos, Self, {NAN}, {NAN},);
    gen_wrapper2!("Returns arctangent of a number. ", atan, Self, {HALF_PI}, {HALF_PI.inv_sign()},);
    
    gen_wrapper2!("Returns hyperbolic sine of a number.", sinh, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper2!("Returns hyperbolic cosine of a number.", cosh, Self, {INF_POS}, {INF_POS},);
    gen_wrapper2!("Returns hyperbolic tangent of a number.", tanh, Self, {ONE}, {ONE.inv_sign()},);
    gen_wrapper2!("Returns inverse hyperbolic sine of a number.", asinh, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper2!("Returns inverse hyperbolic cosine of a number.", acosh, Self, {ZERO}, {ZERO},);
    gen_wrapper2!("Returns inverse hyperbolic tangent of a number.", atanh, Self, {ZERO}, {ZERO},);
}

/// Standard library features
#[cfg(feature = "std")]
pub mod std_ops {

    use crate::ONE;
    use crate::ZERO;
    use crate::defs::DECIMAL_POSITIONS;
    use crate::defs::DECIMAL_SIGN_NEG;
    use crate::NAN;
    use crate::BigFloat;
    
    use super::Flavor;

    use std::iter::Product;
    use std::iter::Sum;
    use std::ops::Add;
    use std::ops::AddAssign;
    use std::ops::Div;
    use std::ops::DivAssign;
    use std::ops::Mul;
    use std::ops::MulAssign;
    use std::ops::Neg;
    use std::ops::Sub;
    use std::ops::SubAssign;
    use std::cmp::PartialEq;
    use std::cmp::Eq;
    use std::cmp::PartialOrd;
    use std::cmp::Ordering;
    use std::fmt::Display;
    use std::fmt::Formatter;
    use std::str::FromStr;
    
    //
    // ops traits
    //

    impl Add for BigFloat {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            BigFloat::add(&self, &rhs)
        }
    }
    
    impl AddAssign for BigFloat {
        fn add_assign(&mut self, rhs: Self) {
            *self = BigFloat::add(self, &rhs)
        }
    }

    impl Div for BigFloat {
        type Output = Self;
        fn div(self, rhs: Self) -> Self::Output {
            BigFloat::div(&self, &rhs)
        }
    }
    
    impl DivAssign for BigFloat {
        fn div_assign(&mut self, rhs: Self) {
            *self = BigFloat::div(self, &rhs)
        }
    }
    
    impl Mul for BigFloat {
        type Output = Self;
        fn mul(self, rhs: Self) -> Self::Output {
            BigFloat::mul(&self, &rhs)
        }
    }
    
    impl MulAssign for BigFloat {
        fn mul_assign(&mut self, rhs: Self) {
            *self = BigFloat::mul(self, &rhs)
        }
    }

    impl Neg for BigFloat {
        type Output = Self;
        fn neg(self) -> Self::Output {
            self.inv_sign()
        }
    }

    impl Sub for BigFloat {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            BigFloat::sub(&self, &rhs)
        }
    }
    
    impl SubAssign for BigFloat {
        fn sub_assign(&mut self, rhs: Self) {
            *self = BigFloat::sub(self, &rhs)
        }
    }

    impl Add<&BigFloat> for BigFloat {
        type Output = Self;
        fn add(self, rhs: &BigFloat) -> Self::Output {
            BigFloat::add(&self, rhs)
        }
    }
    
    impl AddAssign<&BigFloat> for BigFloat {
        fn add_assign(&mut self, rhs: &BigFloat) {
            *self = BigFloat::add(self, &rhs)
        }
    }
    
    impl Div<&BigFloat> for BigFloat {
        type Output = Self;
        fn div(self, rhs: &BigFloat) -> Self::Output {
            BigFloat::div(&self, &rhs)
        }
    }
    
    impl DivAssign<&BigFloat> for BigFloat {
        fn div_assign(&mut self, rhs: &BigFloat) {
            *self = BigFloat::div(self, &rhs)
        }
    }
    
    impl Mul<&BigFloat> for BigFloat {
        type Output = Self;
        fn mul(self, rhs: &BigFloat) -> Self::Output {
            BigFloat::mul(&self, &rhs)
        }
    }
    
    impl MulAssign<&BigFloat> for BigFloat {
        fn mul_assign(&mut self, rhs: &BigFloat) {
            *self = BigFloat::mul(self, &rhs)
        }
    }

    impl Sub<&BigFloat> for BigFloat {
        type Output = Self;
        fn sub(self, rhs: &BigFloat) -> Self::Output {
            BigFloat::sub(&self, &rhs)
        }
    }
    
    impl SubAssign<&BigFloat> for BigFloat {
        fn sub_assign(&mut self, rhs: &BigFloat) {
            *self = BigFloat::sub(self, &rhs)
        }
    }
    
    //
    // ordering traits
    //
    
    impl PartialEq for BigFloat {
        fn eq(&self, other: &Self) -> bool {
            let cmp_result = BigFloat::cmp(self, other);
            matches!(cmp_result, Some(0))
        }
    }
    
    impl Eq for BigFloat {}
    
    impl PartialOrd for BigFloat {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            let cmp_result = BigFloat::cmp(self, other);
            match cmp_result {
                Some(v) => {
                    if v > 0 {
                        Some(Ordering::Greater)
                    } else if v < 0 {
                        Some(Ordering::Less)
                    } else {
                        Some(Ordering::Equal)
                    }
                },
                None => None,
            }
        }
    }

    impl From<f64> for BigFloat {
        fn from(f: f64) -> Self {
            BigFloat::from_f64(f)
        }
    }

    impl From<f32> for BigFloat {
        fn from(f: f32) -> Self {
            BigFloat::from_f32(f)
        }
    }

    impl Display for BigFloat {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
            let s = match self.inner {
                Flavor::Value(v) => {
                    if v.is_zero() {
                        "0".to_owned()
                    } else {
                        let mut num = if v.sign == DECIMAL_SIGN_NEG {
                            "-".to_owned()
                        } else {
                            "".to_owned()
                        };
                        let mut bytes = [0; DECIMAL_POSITIONS];
                        v.get_mantissa_bytes(&mut bytes);
                        let len = v.get_mantissa_len();
                        num.push(std::char::from_digit(bytes[0] as u32, 10).unwrap());
                        num += ".";
                        for byte in &bytes[1..len] {
                            num.push(std::char::from_digit(*byte as u32, 10).unwrap());
                        }
                        let e = v.n as i32 + v.e as i32 - 1;
                        if e != 0 {
                            num.push('e');
                            if e > 0 {
                                num.push('+');
                            }
                            num += &e.to_string();
                        }
                        num
                    }
                },
                Flavor::Inf(sign) => {
                    if sign == DECIMAL_SIGN_NEG {
                        "-Inf".to_owned()
                    } else {
                        "Inf".to_owned()
                    }
                },
                crate::ext::Flavor::NaN => {
                    "NaN".to_owned()
                },
            };
            write!(f, "{}", s)
        }
    }

    impl Default for BigFloat {
        fn default() -> BigFloat {
            BigFloat::new()
        }
    }

    impl FromStr for BigFloat {
        type Err = BigFloat;

        /// Returns parsed number or NAN in case of error.
        fn from_str(src: &str) -> Result<BigFloat, Self::Err> {
            BigFloat::parse(src).ok_or(NAN)
        }
    }

    impl Product for BigFloat {
        fn product<I: Iterator<Item = BigFloat>>(iter: I) -> Self {
            let mut acc = ONE;
            for v in iter {
                acc *= v;
            }
            acc
        }
    }

    impl Sum for BigFloat {
        fn sum<I: Iterator<Item = BigFloat>>(iter: I) -> Self {
            let mut acc = ZERO;
            for v in iter {
                acc += v;
            }
            acc
        }
    }


    impl<'a> Product<&'a BigFloat> for BigFloat {
        fn product<I: Iterator<Item = &'a BigFloat>>(iter: I) -> Self {
            let mut acc = ONE;
            for v in iter {
                acc *= v;
            }
            acc
        }
    }

    impl<'a> Sum<&'a BigFloat> for BigFloat {
        fn sum<I: Iterator<Item = &'a BigFloat>>(iter: I) -> Self {
            let mut acc = ZERO;
            for v in iter {
                acc += v;
            }
            acc
        }
    }
}

macro_rules! impl_int_conv {
    ($s:ty, $u:ty, $from_s:ident, $from_u:ident, $from_int:ident) => {
        impl BigFloat {

            /// Construct BigFloat from integer value.
            pub fn $from_s(i: $s) -> Self {
                let sign = if i < 0 {
                    DECIMAL_SIGN_NEG
                } else {
                    DECIMAL_SIGN_POS
                };
                Self::$from_int(i.abs() as $u, sign)
            }
        
            /// Construct BigFloat from integer value.
            pub fn $from_u(i: $u) -> Self {
                Self::$from_int(i, DECIMAL_SIGN_POS)
            }
        
            fn $from_int(mut v: $u, sign: i8) -> Self {
                let mut d = [0u8; DECIMAL_POSITIONS];
                let mut p = DECIMAL_POSITIONS;
                while v > 0 {
                    p -= 1;
                    d[p] = (v % 10) as u8;
                    v /= 10;
                }
                if p < DECIMAL_POSITIONS {
                    Self::from_bytes(&d[p..], sign, 0)
                } else {
                    Self::new()
                }
            }
        }

        #[cfg(feature = "std")]
        impl From<$s> for BigFloat {
            fn from(i: $s) -> Self {
                BigFloat::$from_s(i)
            }
        }

        #[cfg(feature = "std")]
        impl From<$u> for BigFloat {
            fn from(i: $u) -> Self {
                BigFloat::$from_u(i)
            }
        }
    };
}

impl_int_conv!(i8, u8, from_i8, from_u8, from_int_u8);
impl_int_conv!(i16, u16, from_i16, from_u16, from_int_u16);
impl_int_conv!(i32, u32, from_i32, from_u32, from_int_u32);
impl_int_conv!(i64, u64, from_i64, from_u64, from_int_u64);
impl_int_conv!(i128, u128, from_i128, from_u128, from_int_u128);


#[cfg(test)]
mod tests {

    use crate::defs::DECIMAL_PARTS;
    use crate::*;

    #[cfg(feature = "std")]
    use std::str::FromStr;

    #[test]
    fn test_ext() {

        // Inf & NaN
        let d1 = ONE;
        assert!(!d1.is_inf());
        assert!(!d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.get_sign() > 0);

        let d1 = ONE.div(&BigFloat::new());
        assert!(d1.is_inf());
        assert!(!d1.is_nan());
        assert!(d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.get_sign() > 0);

        let d1 = d1.inv_sign();
        assert!(d1.is_inf());
        assert!(!d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(d1.is_inf_neg());
        assert!(d1.get_sign() < 0);

        let d1 = BigFloat::new().div(&BigFloat::new());
        assert!(!d1.is_inf());
        assert!(d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.get_sign() == 0);

        // conversions
        let d1 = ONE;
        assert!(d1.to_f64() == 1.0);
        assert!(d1.to_f32() == 1.0);
        let d1 = BigFloat::new().div(&BigFloat::new());
        assert!(d1.to_f64().is_nan());
        assert!(d1.to_f32().is_nan());
        let d1 = ONE.div(&BigFloat::new());
        assert!(d1.to_f64().is_infinite());
        assert!(d1.to_f32().is_infinite());
        assert!(d1.to_f64().is_sign_positive());
        assert!(d1.to_f32().is_sign_positive());
        let d1 = d1.inv_sign();
        assert!(d1.to_f64().is_sign_negative());
        assert!(d1.to_f32().is_sign_negative());
        assert!(d1.to_f64().is_infinite());
        assert!(d1.to_f32().is_infinite());

        let d1 = ONE;
        let mut bytes = [1; DECIMAL_PARTS];
        d1.get_mantissa_bytes(&mut bytes);
        assert!(bytes != [1; DECIMAL_PARTS]);
        assert!(d1.get_mantissa_len() != 0);
        let mut bytes = [1; DECIMAL_PARTS];
        let d1 = INF_POS;
        d1.get_mantissa_bytes(&mut bytes);
        assert!(d1.get_mantissa_len() == 0);
        assert!(bytes == [1; DECIMAL_PARTS]);
        let d1 = INF_NEG;
        d1.get_mantissa_bytes(&mut bytes);
        assert!(d1.get_mantissa_len() == 0);
        assert!(bytes == [1; DECIMAL_PARTS]);
        let d1 = NAN;
        d1.get_mantissa_bytes(&mut bytes);
        assert!(d1.get_mantissa_len() == 0);
        assert!(bytes == [1; DECIMAL_PARTS]);

        assert!(ONE.get_exponent() < 0);
        assert!(INF_POS.get_exponent() == 0);
        assert!(INF_NEG.get_exponent() == 0);
        assert!(NAN.get_exponent() == 0);
    
        assert!(ONE.to_raw_parts().is_some());
        assert!(INF_POS.to_raw_parts().is_none());
        assert!(INF_NEG.to_raw_parts().is_none());
        assert!(NAN.to_raw_parts().is_none());

        assert!(ONE.add(&ONE).cmp(&TWO) == Some(0));
        assert!(ONE.add(&INF_POS).is_inf_pos());
        assert!(INF_POS.add(&ONE).is_inf_pos());
        assert!(ONE.add(&INF_NEG).is_inf_neg());
        assert!(INF_NEG.add(&ONE).is_inf_neg());
        assert!(INF_POS.add(&INF_POS).is_inf_pos());
        assert!(INF_POS.add(&INF_NEG).is_nan());
        assert!(INF_NEG.add(&INF_NEG).is_inf_neg());
        assert!(INF_NEG.add(&INF_POS).is_nan());

        assert!(TWO.sub(&ONE).cmp(&ONE) == Some(0));
        assert!(ONE.sub(&INF_POS).is_inf_neg());
        assert!(INF_POS.sub(&ONE).is_inf_pos());
        assert!(ONE.sub(&INF_NEG).is_inf_pos());
        assert!(INF_NEG.sub(&ONE).is_inf_neg());
        assert!(INF_POS.sub(&INF_POS).is_nan());
        assert!(INF_POS.sub(&INF_NEG).is_inf_pos());
        assert!(INF_NEG.sub(&INF_NEG).is_nan());
        assert!(INF_NEG.sub(&INF_POS).is_inf_neg());

        assert!(TWO.mul(&ONE).cmp(&TWO) == Some(0));
        assert!(ONE.mul(&INF_POS).is_inf_pos());
        assert!(INF_POS.mul(&ONE).is_inf_pos());
        assert!(ONE.mul(&INF_NEG).is_inf_neg());
        assert!(INF_NEG.mul(&ONE).is_inf_neg());
        assert!(ONE.inv_sign().mul(&INF_POS).is_inf_neg());
        assert!(ONE.inv_sign().mul(&INF_NEG).is_inf_pos());
        assert!(INF_POS.mul(&ONE.inv_sign()).is_inf_neg());
        assert!(INF_NEG.mul(&ONE.inv_sign()).is_inf_pos());
        assert!(INF_POS.mul(&INF_POS).is_inf_pos());
        assert!(INF_POS.mul(&INF_NEG).is_inf_neg());
        assert!(INF_NEG.mul(&INF_NEG).is_inf_pos());
        assert!(INF_NEG.mul(&INF_POS).is_inf_neg());
        assert!(INF_POS.mul(&BigFloat::new()).is_nan());
        assert!(INF_NEG.mul(&BigFloat::new()).is_nan());
        assert!(BigFloat::new().mul(&INF_POS).is_nan());
        assert!(BigFloat::new().mul(&INF_NEG).is_nan());

        assert!(TWO.div(&TWO).cmp(&ONE) == Some(0));
        assert!(TWO.div(&INF_POS).is_zero());
        assert!(INF_POS.div(&TWO).is_inf_pos());
        assert!(TWO.div(&INF_NEG).is_zero());
        assert!(INF_NEG.div(&TWO).is_inf_neg());
        assert!(TWO.inv_sign().div(&INF_POS).is_zero());
        assert!(TWO.inv_sign().div(&INF_NEG).is_zero());
        assert!(INF_POS.div(&TWO.inv_sign()).is_inf_neg());
        assert!(INF_NEG.div(&TWO.inv_sign()).is_inf_pos());
        assert!(INF_POS.div(&INF_POS).is_nan());
        assert!(INF_POS.div(&INF_NEG).is_nan());
        assert!(INF_NEG.div(&INF_NEG).is_nan());
        assert!(INF_NEG.div(&INF_POS).is_nan());
        assert!(INF_POS.div(&BigFloat::new()).is_inf_pos());
        assert!(INF_NEG.div(&BigFloat::new()).is_inf_neg());
        assert!(BigFloat::new().div(&INF_POS).is_zero());
        assert!(BigFloat::new().div(&INF_NEG).is_zero());

        for op in [BigFloat::add, 
            BigFloat::sub, 
            BigFloat::mul, 
            BigFloat::div, ] {
            assert!(op(&NAN, &ONE).is_nan());
            assert!(op(&ONE, &NAN).is_nan());
            assert!(op(&NAN, &INF_POS).is_nan());
            assert!(op(&INF_POS, &NAN).is_nan());
            assert!(op(&NAN, &INF_NEG).is_nan());
            assert!(op(&INF_NEG, &NAN).is_nan());
            assert!(op(&NAN, &NAN).is_nan());
        }

        assert!(ONE.cmp(&ONE).unwrap() == 0);
        assert!(ONE.cmp(&INF_POS).unwrap() < 0);
        assert!(INF_POS.cmp(&ONE).unwrap() > 0);
        assert!(INF_POS.cmp(&INF_POS).unwrap() == 0);
        assert!(ONE.cmp(&INF_NEG).unwrap() > 0);
        assert!(INF_NEG.cmp(&ONE).unwrap() < 0);
        assert!(INF_NEG.cmp(&INF_NEG).unwrap() == 0);
        assert!(ONE.cmp(&NAN).is_none());
        assert!(NAN.cmp(&ONE).is_none());
        assert!(INF_POS.cmp(&NAN).is_none());
        assert!(NAN.cmp(&INF_POS).is_none());
        assert!(INF_NEG.cmp(&NAN).is_none());
        assert!(NAN.cmp(&INF_NEG).is_none());
        assert!(NAN.cmp(&NAN).is_none());

        assert!(ONE.is_positive());
        assert!(!ONE.is_negative());

        assert!(ONE.inv_sign().is_negative());
        assert!(!ONE.inv_sign().is_positive());
        assert!(!INF_POS.is_negative());
        assert!(INF_POS.is_positive());
        assert!(INF_NEG.is_negative());
        assert!(!INF_NEG.is_positive());
        assert!(!NAN.is_positive());
        assert!(!NAN.is_negative());


        assert!(ONE.pow(&ONE).cmp(&ONE) == Some(0));
        assert!(BigFloat::new().pow(&INF_POS).is_zero());
        assert!(BigFloat::new().pow(&INF_NEG).is_zero());
        assert!(ONE.pow(&INF_POS).cmp(&ONE) == Some(0));
        assert!(ONE.pow(&INF_NEG).cmp(&ONE) == Some(0));
        assert!(TWO.pow(&INF_POS).is_inf_pos());
        assert!(TWO.pow(&INF_NEG).is_inf_neg());
        assert!(INF_POS.pow(&ONE).is_inf_pos());
        assert!(INF_NEG.pow(&ONE).is_inf_neg());
        assert!(INF_NEG.pow(&TWO).is_inf_pos());
        assert!(INF_NEG.pow(&BigFloat::from_f64(10.2)).is_inf_pos());
        assert!(INF_NEG.pow(&BigFloat::from_f64(3.0)).is_inf_neg());
        assert!(INF_POS.pow(&ONE.inv_sign()).is_zero());
        assert!(INF_NEG.pow(&ONE.inv_sign()).is_zero());
        assert!(INF_POS.pow(&BigFloat::new()).cmp(&ONE) == Some(0));
        assert!(INF_NEG.pow(&BigFloat::new()).cmp(&ONE) == Some(0));
        assert!(INF_POS.pow(&INF_POS).is_inf_pos());
        assert!(INF_NEG.pow(&INF_POS).is_inf_pos());
        assert!(INF_POS.pow(&INF_NEG).is_zero());
        assert!(INF_NEG.pow(&INF_NEG).is_zero());

        let half = ONE.div(&TWO);
        assert!(TWO.log(&TWO).cmp(&ONE) == Some(0));
        assert!(TWO.log(&INF_POS).is_zero());
        assert!(TWO.log(&INF_NEG).is_nan());
        assert!(INF_POS.log(&TWO).is_inf_pos());
        assert!(INF_NEG.log(&TWO).is_nan());
        assert!(half.log(&half).cmp(&ONE) == Some(0));
        assert!(half.log(&INF_POS).is_zero());
        assert!(half.log(&INF_NEG).is_nan());
        assert!(INF_POS.log(&half).is_inf_neg());
        assert!(INF_NEG.log(&half).is_nan());
        assert!(INF_POS.log(&INF_POS).is_nan());
        assert!(INF_POS.log(&INF_NEG).is_nan());
        assert!(INF_NEG.log(&INF_POS).is_nan());
        assert!(INF_NEG.log(&INF_NEG).is_nan());
        assert!(TWO.log(&ONE).is_inf_pos());
        assert!(half.log(&ONE).is_inf_pos());
        assert!(ONE.log(&ONE).is_nan());

        assert!(BigFloat::from_f32(f32::NAN).is_nan());
        assert!(BigFloat::from_f32(f32::INFINITY).is_inf_pos());
        assert!(BigFloat::from_f32(f32::NEG_INFINITY).is_inf_neg());
        assert!(!BigFloat::from_f32(1.0).is_nan());
        assert!(BigFloat::from_f64(f64::NAN).is_nan());
        assert!(BigFloat::from_f64(f64::INFINITY).is_inf_pos());
        assert!(BigFloat::from_f64(f64::NEG_INFINITY).is_inf_neg());
        assert!(!BigFloat::from_f64(1.0).is_nan());

        assert!(ONE.pow(&NAN).is_nan());
        assert!(NAN.pow(&ONE).is_nan());
        assert!(INF_POS.pow(&NAN).is_nan());
        assert!(NAN.pow(&INF_POS).is_nan());
        assert!(INF_NEG.pow(&NAN).is_nan());
        assert!(NAN.pow(&INF_NEG).is_nan());
        assert!(NAN.pow(&NAN).is_nan());

        assert!(TWO.log(&NAN).is_nan());
        assert!(NAN.log(&TWO).is_nan());
        assert!(INF_POS.log(&NAN).is_nan());
        assert!(NAN.log(&INF_POS).is_nan());
        assert!(INF_NEG.log(&NAN).is_nan());
        assert!(NAN.log(&INF_NEG).is_nan());
        assert!(NAN.log(&NAN).is_nan());

        assert!(INF_NEG.abs().is_inf_pos());
        assert!(INF_POS.abs().is_inf_pos());
        assert!(NAN.abs().is_nan());

        assert!(INF_NEG.int().is_nan());
        assert!(INF_POS.int().is_nan());
        assert!(NAN.int().is_nan());

        assert!(INF_NEG.frac().is_nan());
        assert!(INF_POS.frac().is_nan());
        assert!(NAN.frac().is_nan());

        assert!(INF_NEG.ceil().is_inf_neg());
        assert!(INF_POS.ceil().is_inf_pos());
        assert!(NAN.ceil().is_nan());

        assert!(INF_NEG.floor().is_inf_neg());
        assert!(INF_POS.floor().is_inf_pos());
        assert!(NAN.floor().is_nan());

        assert!(INF_NEG.round(0).is_inf_neg());
        assert!(INF_POS.round(0).is_inf_pos());
        assert!(NAN.round(0).is_nan());

        assert!(INF_NEG.sqrt().is_nan());
        assert!(INF_POS.sqrt().is_inf_pos());
        assert!(NAN.sqrt().is_nan());

        assert!(INF_NEG.cbrt().is_inf_neg());
        assert!(INF_POS.cbrt().is_inf_pos());
        assert!(NAN.cbrt().is_nan());

        for op in [BigFloat::ln, 
            BigFloat::log2, 
            BigFloat::log10,] {
            assert!(op(&INF_NEG).is_nan());
            assert!(op(&INF_POS).is_inf_pos());
            assert!(op(&NAN).is_nan());
        }

        assert!(INF_NEG.exp().is_inf_neg());
        assert!(INF_POS.exp().is_inf_pos());
        assert!(NAN.exp().is_nan());

        assert!(INF_NEG.sin().is_nan());
        assert!(INF_POS.sin().is_nan());
        assert!(NAN.sin().is_nan());

        assert!(INF_NEG.cos().is_nan());
        assert!(INF_POS.cos().is_nan());
        assert!(NAN.cos().is_nan());

        assert!(INF_NEG.tan().is_nan());
        assert!(INF_POS.tan().is_nan());
        assert!(NAN.tan().is_nan());

        assert!(INF_NEG.asin().is_nan());
        assert!(INF_POS.asin().is_nan());
        assert!(NAN.asin().is_nan());

        assert!(INF_NEG.acos().is_nan());
        assert!(INF_POS.acos().is_nan());
        assert!(NAN.acos().is_nan());

        assert!(INF_NEG.atan().cmp(&HALF_PI.inv_sign()) == Some(0));
        assert!(INF_POS.atan().cmp(&HALF_PI) == Some(0));
        assert!(NAN.atan().is_nan());

        assert!(INF_NEG.sinh().is_inf_neg());
        assert!(INF_POS.sinh().is_inf_pos());
        assert!(NAN.sinh().is_nan());
        
        assert!(INF_NEG.cosh().is_inf_pos());
        assert!(INF_POS.cosh().is_inf_pos());
        assert!(NAN.cosh().is_nan());

        assert!(INF_NEG.tanh().cmp(&ONE.inv_sign()) == Some(0));
        assert!(INF_POS.tanh().cmp(&ONE) == Some(0));
        assert!(NAN.tanh().is_nan());
        
        assert!(INF_NEG.asinh().is_inf_neg());
        assert!(INF_POS.asinh().is_inf_pos());
        assert!(NAN.asinh().is_nan());
        
        assert!(INF_NEG.acosh().is_zero());
        assert!(INF_POS.acosh().is_zero());
        assert!(NAN.acosh().is_nan());
        
        assert!(INF_NEG.atanh().is_zero());
        assert!(INF_POS.atanh().is_zero());
        assert!(NAN.atanh().is_nan());
    }


    #[cfg(feature = "std")]
    #[test]
    pub fn test_std() {

        let d1 = ONE;
        let d2 = BigFloat::new();
        assert!(d1 - d2 == d1);
        assert!(d1 + d2 == d1);
        let mut d3 = BigFloat::new();
        d3 += d1;
        assert!(d1 == d3);
        d3 -= d1;
        assert!(d1 > d3);
        d3 = TWO;
        d3 *= TWO;
        assert!(d3 == TWO*TWO);
        d3 /= TWO;
        assert!(TWO == d3);
        assert!(ONE < d3);
        assert!(ONE == TWO/TWO);

        let d1 = ONE;
        let d2 = BigFloat::new();
        assert!(d1 - &d2 == d1);
        assert!(d1 + &d2 == d1);
        let mut d3 = BigFloat::new();
        d3 += &d1;
        assert!(d1 == d3);
        d3 -= &d1;
        assert!(d1 > d3);
        d3 = TWO;
        d3 *= &TWO;
        assert!(d3 == TWO*&TWO);
        d3 /= &TWO;
        assert!(TWO == d3);
        assert!(ONE < d3);
        assert!(ONE == TWO/&TWO);

        let d1 = BigFloat::from_f64(0.0123456789);
        assert!(format!("{}", d1) == "1.234567890000000000000000000000000000000e-2");
        assert!(BigFloat::from_str(&format!("{}", d1)).unwrap() == d1);
        let d1 = BigFloat::from_f64(-123.456789);
        assert!(format!("{}", d1) == "-1.234567890000000000000000000000000000000e+2");
        assert!(BigFloat::from_str(&format!("{}", d1)).unwrap() == d1);
        assert!(format!("{}", INF_POS) == "Inf");
        assert!(format!("{}", INF_NEG) == "-Inf");
        assert!(format!("{}", NAN) == "NaN");

        assert!(BigFloat::from_str("abc").unwrap_err().is_nan());

        let arr = [TWO, ONE, TWO];
        assert!(arr.into_iter().product::<BigFloat>() == TWO * TWO);
        assert!(arr.into_iter().sum::<BigFloat>() == TWO + ONE + TWO);

        assert!(BigFloat::from_i8(-123) == BigFloat::parse("-1.23e+2").unwrap());
        assert!(BigFloat::from_u8(123) == BigFloat::parse("1.23e+2").unwrap());
        assert!(BigFloat::from_i16(-12312) == BigFloat::parse("-1.2312e+4").unwrap());
        assert!(BigFloat::from_u16(12312) == BigFloat::parse("1.2312e+4").unwrap());
        assert!(BigFloat::from_i32(-123456789) == BigFloat::parse("-1.23456789e+8").unwrap());
        assert!(BigFloat::from_u32(123456789) == BigFloat::parse("1.23456789e+8").unwrap());
        assert!(BigFloat::from_i64(-1234567890123456789) == BigFloat::parse("-1.234567890123456789e+18").unwrap());
        assert!(BigFloat::from_u64(1234567890123456789) == BigFloat::parse("1.234567890123456789e+18").unwrap());
        assert!(BigFloat::from_i128(-123456789012345678901234567890123456789) == BigFloat::parse("-1.23456789012345678901234567890123456789e+38").unwrap());
        assert!(BigFloat::from_u128(123456789012345678901234567890123456789) == BigFloat::parse("1.23456789012345678901234567890123456789e+38").unwrap());
    }
}
