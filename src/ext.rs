///! `BigFloat` by default does not support `NaN`, and `Inf`. 
///! `BigFloatExt` is a wrapper for `BigFloat` which supports `NaN`, and `Inf` 
///! values in addition to functionality of `BigFloat`, 
///! and also implements `std::ops` traits from the standard library.  

use crate::defs::{BigFloat, Error, DECIMAL_SIGN_POS, DECIMAL_PARTS, DECIMAL_SIGN_NEG, DECIMAL_POSITIONS,
    DECIMAL_MAX_EXPONENT, DECIMAL_MIN_EXPONENT};

/// Maximum value possible.
pub const MAX: BigFloatExt = BigFloatExt {inner: Flavor::Value(crate::defs::MAX)};

/// Maximum possible exponent.
pub const MAX_EXP: i8 = DECIMAL_MAX_EXPONENT;

/// Minumum value possible.
pub const MIN: BigFloatExt = BigFloatExt {inner: Flavor::Value(crate::defs::MIN)};

/// Minumum possible exponent.
pub const MIN_EXP: i8 = DECIMAL_MIN_EXPONENT;

/// Smalles positive number.
pub const MIN_POSITIVE: BigFloatExt = BigFloatExt {inner: Flavor::Value(crate::defs::MIN_POSITIVE)};

/// Radix of BigFloatExt
pub const RADIX: u32 = 10;

/// NaN representation.
pub const NAN: BigFloatExt = BigFloatExt { inner: Flavor::NaN };

/// Positive infinity.
pub const INF_POS: BigFloatExt = BigFloatExt { inner: Flavor::Inf(DECIMAL_SIGN_POS) };

/// Negative infinity.
pub const INF_NEG: BigFloatExt = BigFloatExt { inner: Flavor::Inf(DECIMAL_SIGN_NEG) };

/// Value of zero.
pub const ZERO: BigFloatExt = BigFloatExt { inner: Flavor::Value(crate::defs::ZERO) };

/// Value of one
pub const ONE: BigFloatExt = BigFloatExt { inner: Flavor::Value(crate::defs::ONE) };

/// Eulers number.
pub const E: BigFloatExt = BigFloatExt { inner: Flavor::Value(crate::defs::E) };

/// PI number.
pub const PI: BigFloatExt = BigFloatExt { inner: Flavor::Value(crate::defs::PI) };

/// PI/2
pub const HALF_PI: BigFloatExt = BigFloatExt { inner: Flavor::Value(BigFloat {
    m: [2099, 5144, 6397, 1691, 3132, 6192, 4896, 2679, 7963, 1570],
    n: DECIMAL_POSITIONS as i16, 
    sign: DECIMAL_SIGN_POS, 
    e: -(DECIMAL_POSITIONS as i8 - 1),
})};

/// `BigFloat` with support of `NaN`, and `Inf` and operators like `+`, `-`, etc.
#[derive(Copy, Clone, Debug)]
pub struct BigFloatExt {
    inner: Flavor,
}

#[derive(Copy, Clone, Debug)]
enum Flavor {
    Value(BigFloat),
    NaN,
    Inf(i8)         // signed Inf
}

impl BigFloatExt {

    /// Return new BigFloat with value zero.
    pub fn new() -> Self {
        BigFloatExt {
            inner: Flavor::Value(BigFloat::new())
        }
    }
 
    /// Return BigFloat with the value of 1.
    pub fn one() -> Self {
        BigFloatExt {
            inner: Flavor::Value(BigFloat::one())
        }
    }

    /// Return new BigFloat with value of 2.
    pub fn two() -> Self {
        BigFloatExt {
            inner: Flavor::Value(BigFloat::two())
        }
    }

    /// Create a BigFloat value from a sequence of `bytes`. Each byte must represent a decimal digit.
    /// First byte is the most significant. The length of `bytes` can be any. If the length of
    /// `bytes` is greater than required, then the remaining part is ignored.
    /// If `sign` is negative, then the resulting BigFloat will be
    /// negative.
    pub fn from_bytes(bytes: &[u8], sign: i8, exponent: i8) -> Self {
        BigFloatExt {
            inner: Flavor::Value(BigFloat::from_bytes(bytes, sign, exponent))
        }
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
    /// If `self` is Inf or NaN 0 is returned.
    pub fn get_sign(&self) -> i8 {
        match self.inner {
            Flavor::Value(v) => v.sign,
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
        let val = BigFloat {
            sign,
            e: exponent,
            n: mantissa_len,
            m: mantissa,
        };
        BigFloatExt { 
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
                        Self::result_to_ext(v1.add(&v2), v1.n == 0, v1.sign == v2.sign)
                    },
                    Flavor::Inf(s2) => {
                        BigFloatExt { inner: Flavor::Inf(s2) }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match d2.inner {
                    Flavor::Value(_) => {
                        BigFloatExt { inner: Flavor::Inf(s1) }
                    },
                    Flavor::Inf(s2) => {
                        if s1 != s2 {
                            NAN
                        } else {
                            BigFloatExt { inner: Flavor::Inf(s2) }
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
                        Self::result_to_ext(v1.sub(&v2), v1.n == 0, v1.sign == v2.sign)
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
                        BigFloatExt { inner: Flavor::Inf(s1) }
                    },
                    Flavor::Inf(s2) => {
                        if s1 == s2 {
                            NAN
                        } else {
                            BigFloatExt { inner: Flavor::Inf(s1) }
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
                        Self::result_to_ext(v1.mul(&v2), v1.n == 0, v1.sign == v2.sign)
                    },
                    Flavor::Inf(s2) => {
                        if v1.n == 0 { // 0*inf
                            NAN
                        } else {
                            let s = if v1.sign == s2 {
                                DECIMAL_SIGN_POS
                            } else {
                                DECIMAL_SIGN_NEG
                            };
                            BigFloatExt { inner: Flavor::Inf(s) }
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match d2.inner {
                    Flavor::Value(v2) => {
                        if v2.n == 0 { // inf*0
                            NAN
                        } else {
                            let s = if v2.sign == s1 {
                                DECIMAL_SIGN_POS
                            } else {
                                DECIMAL_SIGN_NEG
                            };
                            BigFloatExt { inner: Flavor::Inf(s) }
                        }
                    },
                    Flavor::Inf(s2) => {
                        let s = if s1 == s2 {
                            DECIMAL_SIGN_POS
                        } else {
                            DECIMAL_SIGN_NEG
                        };
                        BigFloatExt { inner: Flavor::Inf(s) }
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
                        Self::result_to_ext(v1.div(&v2), v1.n == 0, v1.sign == v2.sign)
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
    pub fn cmp(&self, d2: &BigFloatExt) -> Option<i16> {
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
    pub fn inv_sign(&self) -> BigFloatExt {
        match self.inner {
            Flavor::Value(mut v1) => {
                if v1.sign == DECIMAL_SIGN_POS {
                    v1.sign = DECIMAL_SIGN_NEG;
                } else {
                    v1.sign = DECIMAL_SIGN_POS;
                }
                BigFloatExt {inner: Flavor::Value(v1)}
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
                        Self::result_to_ext(v1.pow(&v2), v1.n == 0, v1.sign == v2.sign)
                    },
                    Flavor::Inf(s2) => {
                        // v1^inf
                        let val = v1.cmp(&BigFloat::one());
                        if val > 0 {
                            BigFloatExt { inner: Flavor::Inf(s2) }
                        } else if val < 0 {
                            ZERO
                        } else {
                            ONE
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(_) => {
                match d1.inner {
                    Flavor::Value(v2) => {
                        // inf ^ v2
                        let val = v2.cmp(&BigFloat::new());
                        if val > 0 {
                            INF_POS
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

    fn result_to_ext(res: Result<BigFloat, Error>, is_dividend_zero: bool, is_same_sign: bool) -> BigFloatExt {
        match res {
            Err(e) => match e {
                Error::ExponentOverflow => INF_POS,
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
            Ok(v) => BigFloatExt {inner: Flavor::Value(v)},
        }
    }
}



// wrapper function creator
macro_rules! gen_wrapper1 {
    // unwrap error
    ($comment:literal, $fname:ident, $ret:ty, $($arg:ident, $arg_type:ty),*) => {
        #[doc=$comment]
        pub fn $fname($($arg: $arg_type,)*) -> $ret {
            let inner = match BigFloat::$fname($($arg,)*) {
                Err(e) => match e {
                    Error::ExponentOverflow => Flavor::Inf(DECIMAL_SIGN_POS),
                    _ => Flavor::NaN,
                },
                Ok(v) => Flavor::Value(v),
            };
            BigFloatExt {
                inner
            }
        }
    };
}

macro_rules! gen_wrapper2 {
    // unwrap error, function requires self as argument
    ($comment:literal, $fname:ident, $ret:ty, $pos_inf:block, $neg_inf:block, $($arg:ident, $arg_type:ty),*) => {
        #[doc=$comment]
        pub fn $fname(&self$(,$arg: $arg_type)*) -> $ret {
            match self.inner {
                Flavor::Value(v) => Self::result_to_ext(v.$fname($($arg,)*), v.n == 0, true),
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
            BigFloatExt {
                inner
            }
        }
    };
}

impl BigFloatExt {

gen_wrapper1!("Construct BigFloat from f32.", from_f32, Self, f, f32);
gen_wrapper1!("Construct BigFloat from f64.", from_f64, Self, f, f64);

gen_wrapper4!("Return absolute value.", abs, Self, {Flavor::Inf(DECIMAL_SIGN_POS)}, {Flavor::Inf(DECIMAL_SIGN_POS)},);
gen_wrapper4!("Return integer part of a number,", int, Self, {Flavor::NaN}, {Flavor::NaN},);
gen_wrapper4!("Return fractional part of a number.", frac, Self, {Flavor::NaN}, {Flavor::NaN},);
gen_wrapper2!("Returns the smallest integer greater than or equal to a number.", ceil, Self, {INF_POS}, {INF_NEG},);
gen_wrapper2!("Returns the largest integer less than or equal to a number.", floor, Self, {INF_POS}, {INF_NEG},);
gen_wrapper2!("Returns the rounded number with `n` decimal positions in the fractional part of the number.", round, Self, {INF_POS}, {INF_NEG}, n, usize);

gen_wrapper2!("Return square root of a number.", sqrt, Self, {INF_POS}, {NAN},);
gen_wrapper2!("Returns natural logarithm of a number.", ln, Self, {INF_POS}, {NAN},);

gen_wrapper2!("Returns sine of a number. Argument is an angle in radians.", sin, Self, {NAN}, {NAN},);
gen_wrapper2!("Returns cosine of a number. Argument is an angle in radians.", cos, Self, {NAN}, {NAN},);
gen_wrapper2!("Returns tangent of a number. Argument is an angle in radians.", tan, Self, {NAN}, {NAN},);
gen_wrapper2!("Returns arcsine of a number. Result is an angle in radians ranging from `-pi` to `pi`.", asin, Self, {NAN}, {NAN},);
gen_wrapper2!("Returns arccosine of a number.", acos, Self, {NAN}, {NAN},);
gen_wrapper2!("Returns arctangent of a number. ", atan, Self, {HALF_PI}, {HALF_PI.inv_sign()},);

gen_wrapper2!("Returns hyperbolic sine of a number.", sinh, Self, {INF_POS}, {INF_NEG},);
gen_wrapper2!("Returns hyperbolic cosine of a number.", cosh, Self, {INF_POS}, {INF_POS},);
gen_wrapper2!("Returns hyperbolic tangent of a number.", tanh, Self, {ONE}, {ONE.inv_sign()},);
gen_wrapper2!("Returns inverse hyperbolic sine of a number.", asinh, Self, {INF_POS}, {INF_NEG},);
gen_wrapper2!("Returns inverse hyperbolic cosine of a number.", acosh, Self, {ZERO}, {ZERO},);
gen_wrapper2!("Returns inverse hyperbolic tangent of a number.", atanh, Self, {ZERO}, {ZERO},);

}

//
// ops traits
//

use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;


impl Add for BigFloatExt {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        BigFloatExt::add(&self, &rhs)
    }
}

impl AddAssign for BigFloatExt {
    fn add_assign(&mut self, rhs: Self) {
        *self = BigFloatExt::add(self, &rhs)
    }
}


impl Div for BigFloatExt {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        BigFloatExt::div(&self, &rhs)
    }
}

impl DivAssign for BigFloatExt {
    fn div_assign(&mut self, rhs: Self) {
        *self = BigFloatExt::div(self, &rhs)
    }
}

impl Mul for BigFloatExt {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        BigFloatExt::mul(&self, &rhs)
    }
}

impl MulAssign for BigFloatExt {
    fn mul_assign(&mut self, rhs: Self) {
        *self = BigFloatExt::mul(self, &rhs)
    }
}

impl Neg for BigFloatExt {
    type Output = Self;
    fn neg(self) -> Self::Output {
        self.inv_sign()
    }
}

impl Sub for BigFloatExt {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        BigFloatExt::sub(&self, &rhs)
    }
}

impl SubAssign for BigFloatExt {
    fn sub_assign(&mut self, rhs: Self) {
        *self = BigFloatExt::sub(self, &rhs)
    }
}

//
// ordering traits
//

use std::cmp::PartialEq;
use std::cmp::Eq;
use std::cmp::PartialOrd;
use std::cmp::Ordering;


impl PartialEq for BigFloatExt {
    fn eq(&self, other: &Self) -> bool {
        let cmp_result = BigFloatExt::cmp(self, other);
        matches!(cmp_result, Some(0))
    }
}

impl Eq for BigFloatExt {}

impl PartialOrd for BigFloatExt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let cmp_result = BigFloatExt::cmp(self, other);
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
