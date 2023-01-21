//! BigFloat including finite numbers, `NaN`, and `Inf`.

use crate::defs::SignedWord;
use crate::defs::DEFAULT_P;
use crate::BigFloatNumber;
use crate::Consts;
use crate::Error;
use crate::Exponent;
use crate::Radix;
use crate::RoundingMode;
use crate::Sign;
use crate::Word;
use core::fmt::Write;
use core::num::FpCategory;
use lazy_static::lazy_static;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

/// Not a number.
pub const NAN: BigFloat = BigFloat {
    inner: Flavor::NaN(None),
};

/// Positive infinity.
pub const INF_POS: BigFloat = BigFloat {
    inner: Flavor::Inf(Sign::Pos),
};

/// Negative infinity.
pub const INF_NEG: BigFloat = BigFloat {
    inner: Flavor::Inf(Sign::Neg),
};

lazy_static! {

    /// 1
    pub static ref ONE: BigFloat = BigFloat { inner: Flavor::Value(BigFloatNumber::from_word(1, DEFAULT_P).expect("Constant ONE initialized")) };

    /// 2
    pub static ref TWO: BigFloat = BigFloat { inner: Flavor::Value(BigFloatNumber::from_word(2, DEFAULT_P).expect("Constant TWO initialized")) };
}

/// A floating point number of arbitrary precision.
#[derive(Debug)]
pub struct BigFloat {
    inner: Flavor,
}

#[derive(Debug)]
enum Flavor {
    Value(BigFloatNumber),
    NaN(Option<Error>),
    Inf(Sign), // signed Inf
}

impl BigFloat {
    /// Returns a new number with value of 0 and precision of `p` bits. Precision is rounded upwards to the word size.
    pub fn new(p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::new(p), false, true)
    }

    /// Constructs a number with precision `p` from f64 value.
    /// Precision is rounded upwards to the word size.
    pub fn from_f64(f: f64, p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::from_f64(p, f), false, true)
    }

    fn nan(err: Option<Error>) -> Self {
        BigFloat {
            inner: Flavor::NaN(err),
        }
    }

    /// Constructs a number with precision `p` from f32 value.
    /// Precision is rounded upwards to the word size.
    pub fn from_f32(f: f32, p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::from_f64(p, f as f64), false, true)
    }

    /// Returns true if `self` is positive infinity.
    pub fn is_inf_pos(&self) -> bool {
        matches!(self.inner, Flavor::Inf(Sign::Pos))
    }

    /// Returns true if `self` is negative infinity.
    pub fn is_inf_neg(&self) -> bool {
        matches!(self.inner, Flavor::Inf(Sign::Neg))
    }

    /// Returns true if `self` is infinite.
    pub fn is_inf(&self) -> bool {
        matches!(self.inner, Flavor::Inf(_))
    }

    /// Return true if `self` is not a number.
    pub fn is_nan(&self) -> bool {
        matches!(self.inner, Flavor::NaN(_))
    }

    /// Return true if `self` is an integer number.
    pub fn is_int(&self) -> bool {
        match &self.inner {
            Flavor::Value(v) => v.is_int(),
            Flavor::NaN(_) => false,
            Flavor::Inf(_) => false,
        }
    }

    /// Returns the associated with `NaN` error, if any.
    pub fn get_err(&self) -> Option<Error> {
        match &self.inner {
            Flavor::NaN(Some(e)) => Some(e.clone()),
            _ => None,
        }
    }

    /// Adds `d2` to `self` and returns the result of the operation with precision `p` rounded according to `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn add(&self, d2: &Self, p: usize, rm: RoundingMode) -> Self {
        self.add_op(d2, p, rm, false)
    }

    /// Adds `d2` to `self` and returns the result of the operation.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer addition.
    pub fn add_full_prec(&self, d2: &Self) -> Self {
        self.add_op(d2, 0, RoundingMode::None, true)
    }

    fn add_op(&self, d2: &Self, p: usize, rm: RoundingMode, full_prec: bool) -> Self {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Self::result_to_ext(
                    if full_prec { v1.add_full_prec(v2) } else { v1.add(v2, p, rm) },
                    v1.is_zero(),
                    v1.get_sign() == v2.get_sign(),
                ),
                Flavor::Inf(s2) => BigFloat {
                    inner: Flavor::Inf(*s2),
                },
                Flavor::NaN(err) => Self::nan(err.clone()),
            },
            Flavor::Inf(s1) => match &d2.inner {
                Flavor::Value(_) => BigFloat {
                    inner: Flavor::Inf(*s1),
                },
                Flavor::Inf(s2) => {
                    if *s1 != *s2 {
                        NAN
                    } else {
                        BigFloat {
                            inner: Flavor::Inf(*s2),
                        }
                    }
                }
                Flavor::NaN(err) => Self::nan(err.clone()),
            },
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Subtracts `d2` from `self` and returns the result of the operation with precision `p` rounded according to `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn sub(&self, d2: &Self, p: usize, rm: RoundingMode) -> Self {
        self.sub_op(d2, p, rm, false)
    }

    /// Subtracts `d2` from `self` and returns the result of the operation.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer subtraction.
    pub fn sub_full_prec(&self, d2: &Self) -> Self {
        self.sub_op(d2, 0, RoundingMode::None, true)
    }

    fn sub_op(&self, d2: &Self, p: usize, rm: RoundingMode, full_prec: bool) -> Self {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Self::result_to_ext(
                    if full_prec { v1.sub_full_prec(v2) } else { v1.sub(v2, p, rm) },
                    v1.is_zero(),
                    v1.get_sign() == v2.get_sign(),
                ),
                Flavor::Inf(s2) => {
                    if s2.is_positive() {
                        INF_NEG
                    } else {
                        INF_POS
                    }
                }
                Flavor::NaN(err) => Self::nan(err.clone()),
            },
            Flavor::Inf(s1) => match &d2.inner {
                Flavor::Value(_) => BigFloat {
                    inner: Flavor::Inf(*s1),
                },
                Flavor::Inf(s2) => {
                    if *s1 == *s2 {
                        NAN
                    } else {
                        BigFloat {
                            inner: Flavor::Inf(*s1),
                        }
                    }
                }
                Flavor::NaN(err) => Self::nan(err.clone()),
            },
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Multiplies `d2` by `self` and returns the result of the operation with precision `p` rounded according to `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn mul(&self, d2: &Self, p: usize, rm: RoundingMode) -> Self {
        self.mul_op(d2, p, rm, false)
    }

    /// Multiplies `d2` by `self` and returns the result of the operation.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer multiplication.
    pub fn mul_full_prec(&self, d2: &Self) -> Self {
        self.mul_op(d2, 0, RoundingMode::None, true)
    }

    fn mul_op(&self, d2: &Self, p: usize, rm: RoundingMode, full_prec: bool) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d2.inner {
                    Flavor::Value(v2) => Self::result_to_ext(
                        if full_prec { v1.mul_full_prec(v2) } else { v1.mul(v2, p, rm) },
                        v1.is_zero(),
                        v1.get_sign() == v2.get_sign(),
                    ),
                    Flavor::Inf(s2) => {
                        if v1.is_zero() {
                            // 0*inf
                            NAN
                        } else {
                            let s = if v1.get_sign() == *s2 { Sign::Pos } else { Sign::Neg };
                            BigFloat {
                                inner: Flavor::Inf(s),
                            }
                        }
                    }
                    Flavor::NaN(err) => Self::nan(err.clone()),
                }
            }
            Flavor::Inf(s1) => {
                match &d2.inner {
                    Flavor::Value(v2) => {
                        if v2.is_zero() {
                            // inf*0
                            NAN
                        } else {
                            let s = if v2.get_sign() == *s1 { Sign::Pos } else { Sign::Neg };
                            BigFloat {
                                inner: Flavor::Inf(s),
                            }
                        }
                    }
                    Flavor::Inf(s2) => {
                        let s = if s1 == s2 { Sign::Pos } else { Sign::Neg };
                        BigFloat {
                            inner: Flavor::Inf(s),
                        }
                    }
                    Flavor::NaN(err) => Self::nan(err.clone()),
                }
            }
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Divides `self` by `d2` and returns the result of the operation with precision `p` rounded according to `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn div(&self, d2: &Self, p: usize, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Self::result_to_ext(
                    v1.div(v2, p, rm),
                    v1.is_zero(),
                    v1.get_sign() == v2.get_sign(),
                ),
                Flavor::Inf(_) => Self::new(v1.get_mantissa_max_bit_len()),
                Flavor::NaN(err) => Self::nan(err.clone()),
            },
            Flavor::Inf(s1) => match &d2.inner {
                Flavor::Value(v) => {
                    if *s1 == v.get_sign() {
                        INF_POS
                    } else {
                        INF_NEG
                    }
                }
                Flavor::Inf(_) => NAN,
                Flavor::NaN(err) => Self::nan(err.clone()),
            },
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Returns the remainder of division of `|self|` by `|d2|`. The sign of the result is set to the sign of `self`.
    pub fn rem(&self, d2: &Self) -> Self {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => {
                    Self::result_to_ext(v1.rem(v2), v1.is_zero(), v1.get_sign() == v2.get_sign())
                }
                Flavor::Inf(_) => self.clone(),
                Flavor::NaN(err) => Self::nan(err.clone()),
            },
            Flavor::Inf(_) => NAN,
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Compares `self` to `d2`.
    /// Returns positive if `self` > `d2`, negative if `self` < `d2`, zero if `self` == `d2`, None if `self` or `d2` is NaN.
    pub fn cmp(&self, d2: &BigFloat) -> Option<SignedWord> {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Some(v1.cmp(&v2)),
                Flavor::Inf(s2) => {
                    if *s2 == Sign::Pos {
                        Some(-1)
                    } else {
                        Some(1)
                    }
                }
                Flavor::NaN(_) => None,
            },
            Flavor::Inf(s1) => match &d2.inner {
                Flavor::Value(_) => Some(*s1 as SignedWord),
                Flavor::Inf(s2) => Some(*s1 as SignedWord - *s2 as SignedWord),
                Flavor::NaN(_) => None,
            },
            Flavor::NaN(_) => None,
        }
    }

    /// Compares the absolute value of `self` to the absolute value of `d2`.
    /// Returns positive if `|self|` is greater than `|d2|`, negative if `|self|` is smaller than `|d2|`, 0 if `|self|` equals to `|d2|`, None if `self` or `d2` is NaN.
    pub fn abs_cmp(&self, d2: &Self) -> Option<SignedWord> {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Some(v1.cmp(&v2)),
                Flavor::Inf(_) => Some(-1),
                Flavor::NaN(_) => None,
            },
            Flavor::Inf(_) => match &d2.inner {
                Flavor::Value(_) => Some(1),
                Flavor::Inf(_) => Some(0),
                Flavor::NaN(_) => None,
            },
            Flavor::NaN(_) => None,
        }
    }

    /// Reverses the sign of `self`.
    pub fn inv_sign(&mut self) {
        match &mut self.inner {
            Flavor::Value(v1) => v1.inv_sign(),
            Flavor::Inf(s) => self.inner = Flavor::Inf(s.invert()),
            Flavor::NaN(_) => {}
        }
    }

    /// Compute the power of `self` to the `n` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    pub fn pow(&self, n: &Self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &n.inner {
                    Flavor::Value(v2) => Self::result_to_ext(
                        v1.pow(v2, p, rm, cc),
                        v1.is_zero(),
                        v1.get_sign() == v2.get_sign(),
                    ),
                    Flavor::Inf(s2) => {
                        // v1^inf
                        let val = v1.cmp(&crate::common::consts::ONE);
                        if val > 0 {
                            BigFloat {
                                inner: Flavor::Inf(*s2),
                            }
                        } else if val < 0 {
                            Self::new(p)
                        } else {
                            Self::from_u8(1, p)
                        }
                    }
                    Flavor::NaN(err) => Self::nan(err.clone()),
                }
            }
            Flavor::Inf(s1) => {
                match &n.inner {
                    Flavor::Value(v2) => {
                        // inf ^ v2
                        if v2.is_zero() {
                            Self::from_u8(1, p)
                        } else if v2.is_positive() {
                            if s1.is_negative() && v2.is_odd_int() {
                                // v2 is odd and has no fractional part.
                                INF_NEG
                            } else {
                                INF_POS
                            }
                        } else {
                            Self::new(p)
                        }
                    }
                    Flavor::Inf(s2) => {
                        // inf^inf
                        if s2.is_positive() {
                            INF_POS
                        } else {
                            Self::new(p)
                        }
                    }
                    Flavor::NaN(err) => Self::nan(err.clone()),
                }
            }
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Compute the power of `self` to the integer `n` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn powi(&self, n: usize, p: usize, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => Self::result_to_ext(v1.powi(n, p, rm), false, true),
            Flavor::Inf(s1) => {
                // inf ^ v2
                if n == 0 {
                    Self::from_u8(1, p)
                } else if s1.is_negative() && (n & 1 == 1) {
                    INF_NEG
                } else {
                    INF_POS
                }
            }
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Computes the logarithm base `n` of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    pub fn log(&self, n: &Self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &n.inner {
                    Flavor::Value(v2) => {
                        if v2.is_zero() {
                            return INF_NEG;
                        }
                        Self::result_to_ext(v1.log(v2, p, rm, cc), false, true)
                    }
                    Flavor::Inf(s2) => {
                        // v1.log(inf)
                        if s2.is_positive() {
                            Self::new(p)
                        } else {
                            NAN
                        }
                    }
                    Flavor::NaN(err) => Self::nan(err.clone()),
                }
            }
            Flavor::Inf(s1) => {
                if *s1 == Sign::Neg {
                    // -inf.log(any)
                    NAN
                } else {
                    match &n.inner {
                        Flavor::Value(v2) => {
                            // +inf.log(v2)
                            if v2.get_exponent() <= 0 {
                                INF_NEG
                            } else {
                                INF_POS
                            }
                        }
                        Flavor::Inf(_) => NAN, // +inf.log(inf)
                        Flavor::NaN(err) => Self::nan(err.clone()),
                    }
                }
            }
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Returns true if `self` is positive.
    /// The function returns false if `self` is NaN.
    pub fn is_positive(&self) -> bool {
        match &self.inner {
            Flavor::Value(v) => v.is_positive(),
            Flavor::Inf(s) => *s == Sign::Pos,
            Flavor::NaN(_) => false,
        }
    }

    /// Returns true if `self` is negative.
    /// The function returns false if `self` is NaN.
    pub fn is_negative(&self) -> bool {
        match &self.inner {
            Flavor::Value(v) => v.is_negative(),
            Flavor::Inf(s) => *s == Sign::Neg,
            Flavor::NaN(_) => false,
        }
    }

    /// Returns true if `self` is subnormal. A number is subnormal if the most significant bit of the mantissa is not equal to 1.
    pub fn is_subnormal(&self) -> bool {
        if let Flavor::Value(v) = &self.inner {
            return v.is_subnormal();
        }
        false
    }

    /// Returns true if `self` is zero.
    pub fn is_zero(&self) -> bool {
        match &self.inner {
            Flavor::Value(v) => v.is_zero(),
            Flavor::Inf(_) => false,
            Flavor::NaN(_) => false,
        }
    }

    /// Restricts the value of `self` to an interval determined by the values of `min` and `max`.
    /// The function returns `max` if `self` is greater than `max`, `min` if `self` is less than `min`, and `self` otherwise.
    /// If either argument is NaN or `min` is greater than `max`, the function returns NaN.
    pub fn clamp(&self, min: &Self, max: &Self) -> Self {
        if self.is_nan() || min.is_nan() || max.is_nan() || max.cmp(min).unwrap() < 0 {
            // call to unwrap() is unreacheable
            NAN
        } else if self.cmp(min).unwrap() < 0 {
            // call to unwrap() is unreacheable
            min.clone()
        } else if self.cmp(max).unwrap() > 0 {
            // call to unwrap() is unreacheable
            max.clone()
        } else {
            self.clone()
        }
    }

    /// Returns the value of `d1` if `d1` is greater than `self`, or the value of `self` otherwise.
    /// If either argument is NaN, the function returns NaN.
    pub fn max(&self, d1: &Self) -> Self {
        if self.is_nan() || d1.is_nan() {
            NAN
        } else if self.cmp(d1).unwrap() < 0 {
            // call to unwrap() is unreacheable
            d1.clone()
        } else {
            self.clone()
        }
    }

    /// Returns value of `d1` if `d1` is less than `self`, or the value of `self` otherwise.
    /// If either argument is NaN, the function returns NaN.
    pub fn min(&self, d1: &Self) -> Self {
        if self.is_nan() || d1.is_nan() {
            NAN
        } else if self.cmp(d1).unwrap() > 0 {
            // call to unwrap() is unreacheable
            d1.clone()
        } else {
            self.clone()
        }
    }

    /// Returns a BigFloat with the value -1 if `self` is negative, 1 if `self` is positive, zero otherwise.
    /// The function returns NaN If `self` is NaN.
    pub fn signum(&self) -> Self {
        if self.is_nan() {
            NAN
        } else if self.is_negative() {
            let mut ret = Self::from_u8(1, DEFAULT_P);
            ret.inv_sign();
            ret
        } else {
            Self::from_u8(1, DEFAULT_P)
        }
    }

    /// Parses a number from the string `s`.
    /// The function expects `s` to be a number in scientific format in base 10, or +-Inf, or NaN.
    ///
    /// ## Examples
    ///
    /// ```
    /// use astro_float::BigFloat;
    /// use astro_float::Radix;
    /// use astro_float::RoundingMode;
    ///
    /// let n = BigFloat::parse("0.0", Radix::Bin, 64, RoundingMode::ToEven);
    /// assert!(n.is_zero());
    ///
    /// let n = BigFloat::parse("1.124e-24", Radix::Dec, 128, RoundingMode::ToEven);
    /// assert!(n.sub(&BigFloat::from_f64(1.124e-24, 128), 128, RoundingMode::ToEven).get_exponent() <= Some(-52 - 24));
    ///
    /// let n = BigFloat::parse("-Inf", Radix::Hex, 1, RoundingMode::None);
    /// assert!(n.is_inf_neg());
    ///
    /// let n = BigFloat::parse("NaN", Radix::Oct, 2, RoundingMode::None);
    /// assert!(n.is_nan());
    /// ```
    pub fn parse(s: &str, rdx: Radix, p: usize, rm: RoundingMode) -> Self {
        match crate::parser::parse(s, rdx) {
            Ok(ps) => {
                if ps.is_inf() {
                    if ps.sign() == Sign::Pos {
                        INF_POS
                    } else {
                        INF_NEG
                    }
                } else if ps.is_nan() {
                    NAN
                } else {
                    let (m, s, e) = ps.raw_parts();
                    Self::result_to_ext(
                        BigFloatNumber::convert_from_radix(s, m, e, rdx, p, rm),
                        false,
                        true,
                    )
                }
            }
            Err(e) => Self::nan(Some(e)),
        }
    }

    pub(crate) fn write_str<T: Write>(
        &self,
        w: &mut T,
        rdx: Radix,
        rm: RoundingMode,
    ) -> Result<(), core::fmt::Error> {
        match &self.inner {
            Flavor::Value(v) => match v.format(rdx, rm) {
                Ok(s) => w.write_str(&s),
                Err(e) => match e {
                    Error::ExponentOverflow(s) => {
                        if s.is_positive() {
                            w.write_str("Inf")
                        } else {
                            w.write_str("-Inf")
                        }
                    }
                    _ => w.write_str("Err"),
                },
            },
            Flavor::Inf(sign) => {
                let s = if sign.is_negative() { "-Inf" } else { "Inf" };
                w.write_str(s)
            }
            crate::ext::Flavor::NaN(_) => w.write_str("NaN"),
        }
    }

    /// Returns a random normalized (not subnormal) BigFloat number with exponent in the range
    /// from `exp_from` to `exp_to` inclusive. The sign can be positive and negative. Zero is excluded.
    /// Precision is rounded upwards to the word size.
    /// Function does not follow any specific distribution law.
    /// The intended use of this function is for testing.
    #[cfg(feature = "random")]
    pub fn random_normal(p: usize, exp_from: Exponent, exp_to: Exponent) -> Self {
        Self::result_to_ext(
            BigFloatNumber::random_normal(p, exp_from, exp_to),
            false,
            true,
        )
    }

    /// Returns category of `self`.
    pub fn classify(&self) -> FpCategory {
        match &self.inner {
            Flavor::Value(v) => {
                if v.is_subnormal() {
                    FpCategory::Subnormal
                } else if v.is_zero() {
                    FpCategory::Zero
                } else {
                    FpCategory::Normal
                }
            }
            Flavor::Inf(_) => FpCategory::Infinite,
            Flavor::NaN(_) => FpCategory::Nan,
        }
    }

    /// Computes the arctangent of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    pub fn atan(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Self {
        match &self.inner {
            Flavor::Value(v) => Self::result_to_ext(v.atan(p, rm, cc), v.is_zero(), true),
            Flavor::Inf(s) => Self::result_to_ext(Self::half_pi(*s, p, rm, cc), false, true),
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Computes the hyperbolic tangent of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    pub fn tanh(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Self {
        match &self.inner {
            Flavor::Value(v) => Self::result_to_ext(v.tanh(p, rm, cc), v.is_zero(), true),
            Flavor::Inf(s) => Self::from_i8(s.as_int(), p),
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    fn half_pi(
        s: Sign,
        p: usize,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<BigFloatNumber, Error> {
        let mut half_pi = cc.pi(p, rm)?;

        half_pi.set_exponent(1);
        half_pi.set_sign(s);

        Ok(half_pi)
    }

    fn result_to_ext(
        res: Result<BigFloatNumber, Error>,
        is_dividend_zero: bool,
        is_same_sign: bool,
    ) -> BigFloat {
        match res {
            Err(e) => match e {
                Error::ExponentOverflow(s) => {
                    if s.is_positive() {
                        INF_POS
                    } else {
                        INF_NEG
                    }
                }
                Error::DivisionByZero => {
                    if is_dividend_zero {
                        NAN
                    } else if is_same_sign {
                        INF_POS
                    } else {
                        INF_NEG
                    }
                }
                Error::MemoryAllocation(e) => Self::nan(Some(Error::MemoryAllocation(e))),
                Error::InvalidArgument => Self::nan(Some(Error::InvalidArgument)),
            },
            Ok(v) => BigFloat {
                inner: Flavor::Value(v),
            },
        }
    }

    /// Returns exponent of `self` or None if `self` is Inf or NaN.
    pub fn get_exponent(&self) -> Option<Exponent> {
        match &self.inner {
            Flavor::Value(v) => Some(v.get_exponent()),
            _ => None,
        }
    }

    /// Returns the number of significant bits used in the mantissa or None if `self` is Inf or NaN.
    /// Normal numbers use all bits of the mantissa.
    /// Subnormal numbers use fewer bits than the mantissa can hold.
    pub fn get_precision(&self) -> Option<usize> {
        match &self.inner {
            Flavor::Value(v) => Some(v.get_precision()),
            _ => None,
        }
    }

    /// Returns the maximum value for the specified precision `p`: all bits of the mantissa are set to 1,
    /// the exponent has the maximum possible value, and the sign is positive.
    /// Precision is rounded upwards to the word size.
    pub fn max_value(p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::max_value(p), false, true)
    }

    /// Returns the minimum value for the specified precision `p`: all bits of the mantissa are set to 1, the exponent has the maximum possible value, and the sign is negative. Precision is rounded upwards to the word size.
    pub fn min_value(p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::min_value(p), false, true)
    }

    /// Returns the minimum positive subnormal value for the specified precision `p`:
    /// only the least significant bit of the mantissa is set to 1, the exponent has
    /// the minimum possible value, and the sign is positive.
    /// Precision is rounded upwards to the word size.
    pub fn min_positive(p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::min_positive(p), false, true)
    }

    /// Returns the minimum positive normal value for the specified precision `p`:
    /// only the most significant bit of the mantissa is set to 1, the exponent has
    /// the minimum possible value, and the sign is positive.
    /// Precision is rounded upwards to the word size.
    pub fn min_positive_normal(p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::min_positive_normal(p), false, true)
    }

    /// Returns a new number with value `d` and the precision `p`. Precision is rounded upwards to the word size.
    pub fn from_word(d: Word, p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::from_word(d, p), false, true)
    }

    /// Returns a copy of the number with the sign reversed.
    pub fn neg(&self) -> Self {
        let mut ret = self.clone();
        ret.inv_sign();
        ret
    }

    /// Decomposes `self` into raw parts.
    /// The function returns a reference to a slice of words representing mantissa, numbers of significant bits in the mantissa, sign, and exponent.
    pub fn to_raw_parts(&self) -> Option<(&[Word], usize, Sign, Exponent)> {
        if let Flavor::Value(v) = &self.inner {
            Some(v.to_raw_parts())
        } else {
            None
        }
    }

    /// Constructs a number from the raw parts:
    ///
    ///  - `m` is the mantisaa.
    ///  - `n` is the number of significant bits in mantissa.
    ///  - `s` is the sign.
    ///  - `e` is the exponent.
    ///
    /// This function returns NaN in the following situations:
    ///
    /// - `n` is larger than the number of bits in `m`.
    /// - `n` is smaller than the number of bits in `m`, but `m` does not represent corresponding subnormal number mantissa.
    /// - `n` is smaller than the number of bits in `m`, but `e` is not the minimum possible exponent.
    /// - `n` or the size of `m` is too large (larger than isize::MAX / 2 + EXPONENT_MIN).
    pub fn from_raw_parts(m: &[Word], n: usize, s: Sign, e: Exponent) -> Self {
        Self::result_to_ext(BigFloatNumber::from_raw_parts(m, n, s, e), false, true)
    }

    /// Constructs a number from the slice of words:
    ///
    ///  - `m` is the mantissa.
    ///  - `s` is the sign.
    ///  - `e` is the exponent.
    pub fn from_words(m: &[Word], s: Sign, e: Exponent) -> Self {
        Self::result_to_ext(BigFloatNumber::from_words(m, s, e), false, true)
    }

    /// Returns the sign of `self` or None if `self` is NaN.
    pub fn get_sign(&self) -> Option<Sign> {
        match &self.inner {
            Flavor::Value(v) => Some(v.get_sign()),
            Flavor::Inf(s) => Some(*s),
            Flavor::NaN(_) => None,
        }
    }

    /// Sets the exponent of `self`.
    /// Note that if `self` is subnormal, the exponent may not change, but the mantissa will shift instead.
    /// See example below.
    ///
    /// ## Examples
    ///
    /// ```
    /// use astro_float::BigFloat;
    /// use astro_float::EXPONENT_MIN;
    ///
    /// // construct a subnormal value.
    /// let mut n = BigFloat::min_positive(128);
    ///
    /// assert_eq!(n.get_exponent().unwrap(), EXPONENT_MIN);
    /// assert_eq!(n.get_precision().unwrap(), 1);
    ///
    /// // increase exponent.
    /// n.set_exponent(n.get_exponent().unwrap() + 1);
    ///
    /// // the outcome for subnormal number.
    /// assert_eq!(n.get_exponent().unwrap(), EXPONENT_MIN);
    /// assert_eq!(n.get_precision().unwrap(), 2);
    /// ```
    pub fn set_exponent(&mut self, e: Exponent) {
        if let Flavor::Value(v) = &mut self.inner {
            v.set_exponent(e)
        }
    }

    /// Returns the maximum mantissa length of `self` in bits regardless of whether `self` is normal or subnormal.
    pub fn get_mantissa_max_bit_len(&self) -> Option<usize> {
        if let Flavor::Value(v) = &self.inner {
            Some(v.get_mantissa_max_bit_len())
        } else {
            None
        }
    }

    /// Sets the precision of `self` to `p`.
    /// If the new precision is smaller than the existing one, the number is rounded using specified rounding mode `rm`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn set_precision(&mut self, p: usize, rm: RoundingMode) -> Result<(), Error> {
        if let Flavor::Value(v) = &mut self.inner {
            v.set_precision(p, rm)
        } else {
            Ok(())
        }
    }

    /// Computes the reciprocal of a number with precision `p`.
    /// The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    pub fn reciprocal(&self, p: usize, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v) => Self::result_to_ext(v.reciprocal(p, rm), v.is_zero(), true),
            Flavor::Inf(s) => {
                let mut ret = Self::new(p);
                ret.set_sign(*s);
                ret
            }
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }

    /// Sets the sign of `self`.
    pub fn set_sign(&mut self, s: Sign) {
        match &mut self.inner {
            Flavor::Value(v) => v.set_sign(s),
            Flavor::Inf(_) => self.inner = Flavor::Inf(s),
            Flavor::NaN(_) => {}
        };
    }

    /// Returns the raw mantissa words of a number.
    pub fn get_mantissa_digits(&self) -> Option<&[Word]> {
        if let Flavor::Value(v) = &self.inner {
            Some(v.get_mantissa_digits())
        } else {
            None
        }
    }

    /// Converts an array of digits in radix `rdx` to BigFloat with precision `p`.
    /// `digits` represents mantissa and is interpreted as a number smaller than 1 and greater or equal to 1/`rdx`.
    /// The first element in `digits` is the most significant digit.
    /// `e` is the exponent part of the number, such that the number can be represented as `digits` * `rdx` ^ `e`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Examples
    ///
    /// Code below converts `-0.1234567₈ × 10₈^3₈` given in radix 8 to BigFloat.
    ///
    /// ``` rust
    /// use astro_float::{BigFloat, Sign, RoundingMode, Radix};
    ///
    /// let g = BigFloat::convert_from_radix(
    ///     Sign::Neg,
    ///     &[1, 2, 3, 4, 5, 6, 7, 0],
    ///     3,
    ///     Radix::Oct,
    ///     64,
    ///     RoundingMode::None);
    ///
    /// let n = BigFloat::from_f64(-83.591552734375, 64);
    ///
    /// assert!(n.cmp(&g) == Some(0));
    /// ```
    ///
    /// ## Errors
    ///
    /// On error, the function returns NaN with the following associated error:
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - InvalidArgument: the precision is incorrect, or `digits` contains unacceptable digits for given radix.
    pub fn convert_from_radix(
        sign: Sign,
        digits: &[u8],
        e: Exponent,
        rdx: Radix,
        p: usize,
        rm: RoundingMode,
    ) -> Self {
        Self::result_to_ext(
            BigFloatNumber::convert_from_radix(sign, digits, e, rdx, p, rm),
            false,
            true,
        )
    }

    /// Converts `self` to radix `rdx` using rounding mode `rm`.
    /// The function returns sign, mantissa digits in radix `rdx`, and exponent such that the converted number
    /// can be represented as `mantissa digits` * `rdx` ^ `exponent`.
    /// The first element in the mantissa is the most significant digit.
    ///
    /// ## Examples
    ///
    /// ``` rust
    /// use astro_float::{BigFloat, Sign, RoundingMode, Radix};
    ///
    /// let n = BigFloat::from_f64(0.00012345678f64, 64);
    ///
    /// let (s, m, e) = n.convert_to_radix(Radix::Dec, RoundingMode::None).unwrap();
    ///
    /// assert_eq!(s, Sign::Pos);
    /// assert_eq!(m, [1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 4, 2]);
    /// assert_eq!(e, -3);
    /// ```
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - InvalidArgument: `self` is Inf or NaN.
    pub fn convert_to_radix(
        &self,
        rdx: Radix,
        rm: RoundingMode,
    ) -> Result<(Sign, Vec<u8>, Exponent), Error> {
        match &self.inner {
            Flavor::Value(v) => v.convert_to_radix(rdx, rm),
            Flavor::NaN(_) => Err(Error::InvalidArgument),
            Flavor::Inf(_) => Err(Error::InvalidArgument),
        }
    }
}

impl Clone for BigFloat {
    fn clone(&self) -> Self {
        match &self.inner {
            Flavor::Value(v) => Self::result_to_ext(v.clone(), false, true),
            Flavor::Inf(s) => {
                if s.is_positive() {
                    INF_POS
                } else {
                    INF_NEG
                }
            }
            Flavor::NaN(err) => Self::nan(err.clone()),
        }
    }
}

macro_rules! gen_wrapper_arg {
    // function requires self as argument
    ($comment:literal, $fname:ident, $ret:ty, $pos_inf:block, $neg_inf:block, $($arg:ident, $arg_type:ty),*) => {
        #[doc=$comment]
        pub fn $fname(&self$(,$arg: $arg_type)*) -> $ret {
            match &self.inner {
                Flavor::Value(v) => Self::result_to_ext(v.$fname($($arg,)*), v.is_zero(), true),
                Flavor::Inf(s) => if s.is_positive() $pos_inf else $neg_inf,
                Flavor::NaN(err) => Self::nan(err.clone()),
            }
        }
    };
}

macro_rules! gen_wrapper_arg_rm {
    // unwrap error, function requires self as argument
    ($comment:literal, $fname:ident, $ret:ty, $pos_inf:block, $neg_inf:block, $($arg:ident, $arg_type:ty),*) => {
        #[doc=$comment]
        pub fn $fname(&self$(,$arg: $arg_type)*, rm: RoundingMode) -> $ret {
            match &self.inner {
                Flavor::Value(v) => {
                    Self::result_to_ext(v.$fname($($arg,)* rm), v.is_zero(), true)
                },
                Flavor::Inf(s) => if s.is_positive() $pos_inf else $neg_inf,
                Flavor::NaN(err) => Self::nan(err.clone()),
            }
        }
    };
}

macro_rules! gen_wrapper_arg_rm_cc {
    // unwrap error, function requires self as argument
    ($comment:literal, $fname:ident, $ret:ty, $pos_inf:block, $neg_inf:block, $($arg:ident, $arg_type:ty),*) => {
        #[doc=$comment]
        pub fn $fname(&self$(,$arg: $arg_type)*, rm: RoundingMode, cc: &mut Consts) -> $ret {
            match &self.inner {
                Flavor::Value(v) => {
                    Self::result_to_ext(v.$fname($($arg,)* rm, cc), v.is_zero(), true)
                },
                Flavor::Inf(s) => if s.is_positive() $pos_inf else $neg_inf,
                Flavor::NaN(err) => Self::nan(err.clone()),
            }
        }
    };
}

macro_rules! gen_wrapper_log {
    ($comment:literal, $fname:ident, $ret:ty, $pos_inf:block, $neg_inf:block, $($arg:ident, $arg_type:ty),*) => {
        #[doc=$comment]
        pub fn $fname(&self$(,$arg: $arg_type)*, rm: RoundingMode, cc: &mut Consts) -> $ret {
            match &self.inner {
                Flavor::Value(v) => {
                    if v.is_zero() {
                        return INF_NEG;
                    }
                    Self::result_to_ext(v.$fname($($arg,)* rm, cc), v.is_zero(), true)
                },
                Flavor::Inf(s) => if s.is_positive() $pos_inf else $neg_inf,
                Flavor::NaN(err) => Self::nan(err.clone()),
            }
        }
    };
}

impl BigFloat {
    gen_wrapper_arg!(
        "Returns the absolute value of `self`.",
        abs,
        Self,
        { INF_POS },
        { INF_POS },
    );
    gen_wrapper_arg!("Returns the integer part of `self`.", int, Self, { NAN }, {
        NAN
    },);
    gen_wrapper_arg!(
        "Returns the fractional part of `self`.",
        fract,
        Self,
        { NAN },
        { NAN },
    );
    gen_wrapper_arg!(
        "Returns the smallest integer greater than or equal to `self`.",
        ceil,
        Self,
        { INF_POS },
        { INF_NEG },
    );
    gen_wrapper_arg!(
        "Returns the largest integer less than or equal to `self`.",
        floor,
        Self,
        { INF_POS },
        { INF_NEG },
    );
    gen_wrapper_arg_rm!("Returns the rounded number with `n` binary positions in the fractional part of the number using rounding mode `rm`.", 
        round,
        Self,
        { INF_POS },
        { INF_NEG },
        n,
        usize
    );
    gen_wrapper_arg_rm!(
        "Computes the square root of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        Precision is rounded upwards to the word size.",
        sqrt,
        Self,
        { INF_POS },
        { NAN },
        p,
        usize
    );
    gen_wrapper_arg_rm!(
        "Computes the cube root of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        Precision is rounded upwards to the word size.",
        cbrt,
        Self,
        { INF_POS },
        { INF_NEG },
        p,
        usize
    );
    gen_wrapper_log!(
        "Computes the natural logarithm of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        ln,
        Self,
        { INF_POS },
        { NAN },
        p,
        usize
    );
    gen_wrapper_log!(
        "Computes the logarithm base 2 of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        log2,
        Self,
        { INF_POS },
        { NAN },
        p,
        usize
    );
    gen_wrapper_log!(
        "Computes the logarithm base 10 of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        log10,
        Self,
        { INF_POS },
        { NAN },
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes `e` to the power of `self` with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        exp,
        Self,
        { INF_POS },
        { INF_NEG },
        p,
        usize
    );

    gen_wrapper_arg_rm_cc!(
        "Computes the sine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        sin,
        Self,
        { NAN },
        { NAN },
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes the cosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        cos,
        Self,
        { NAN },
        { NAN },
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes the tangent of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        tan,
        Self,
        { NAN },
        { NAN },
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes the arcsine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.", 
        asin,
        Self,
        {NAN},
        {NAN},
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes the arccosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        acos,
        Self,
        { NAN },
        { NAN },
        p,
        usize
    );

    gen_wrapper_arg_rm_cc!(
        "Computes the hyperbolic sine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache cc for computing the result. 
        Precision is rounded upwards to the word size.",
        sinh,
        Self,
        { INF_POS },
        { INF_NEG },
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes the hyperbolic cosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache cc for computing the result. 
        Precision is rounded upwards to the word size.",
        cosh,
        Self,
        { INF_POS },
        { INF_POS },
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes the hyperbolic arcsine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        asinh,
        Self,
        { INF_POS },
        { INF_NEG },
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes the hyperbolic arccosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        acosh,
        Self,
        { BigFloat::new(1) },
        { BigFloat::new(1) },
        p,
        usize
    );
    gen_wrapper_arg_rm_cc!(
        "Computes the hyperbolic arctangent of a number with precision `p`. The result is rounded using the rounding mode `rm`.
        This function requires constants cache `cc` for computing the result.
        Precision is rounded upwards to the word size.",
        atanh,
        Self,
        { BigFloat::new(1) },
        { BigFloat::new(1) },
        p,
        usize
    );
}

macro_rules! impl_int_conv {
    ($s:ty, $from_s:ident) => {
        impl BigFloat {
            /// Constructs BigFloat with precision `p` from an integer value `i`.
            /// Precision is rounded upwards to the word size.
            pub fn $from_s(i: $s, p: usize) -> Self {
                Self::result_to_ext(BigFloatNumber::$from_s(i, p), false, true)
            }
        }

        //#[cfg(feature = "std")]
        //impl From<$s> for BigFloat {
        //    fn from(i: $s) -> Self {
        //        let p = GCTX.with(|x| x.borrow().precision);
        //        BigFloat::$from_s(i, p)
        //    }
        //}
    };
}

impl_int_conv!(i8, from_i8);
impl_int_conv!(i16, from_i16);
impl_int_conv!(i32, from_i32);
impl_int_conv!(i64, from_i64);
impl_int_conv!(i128, from_i128);

impl_int_conv!(u8, from_u8);
impl_int_conv!(u16, from_u16);
impl_int_conv!(u32, from_u32);
impl_int_conv!(u64, from_u64);
impl_int_conv!(u128, from_u128);

impl From<BigFloatNumber> for BigFloat {
    fn from(x: BigFloatNumber) -> Self {
        BigFloat {
            inner: Flavor::Value(x),
        }
    }
}

/// Standard library features
pub mod ops {

    use crate::defs::DEFAULT_P;
    use crate::defs::DEFAULT_RM;
    use crate::BigFloat;
    use crate::Radix;

    use core::fmt::Binary;
    use core::fmt::Octal;
    use core::fmt::UpperHex;
    use core::{
        cmp::Eq, cmp::Ordering, cmp::PartialEq, cmp::PartialOrd, fmt::Display, fmt::Formatter,
        ops::Neg, str::FromStr,
    };

    impl Neg for BigFloat {
        type Output = BigFloat;
        fn neg(mut self) -> Self::Output {
            self.inv_sign();
            self
        }
    }

    impl Neg for &BigFloat {
        type Output = BigFloat;
        fn neg(self) -> Self::Output {
            let mut ret = self.clone();
            ret.inv_sign();
            ret
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

    impl<'a> PartialEq<&'a BigFloat> for BigFloat {
        fn eq(&self, other: &&'a BigFloat) -> bool {
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
                }
                None => None,
            }
        }
    }

    impl<'a> PartialOrd<&'a BigFloat> for BigFloat {
        fn partial_cmp(&self, other: &&'a BigFloat) -> Option<Ordering> {
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
                }
                None => None,
            }
        }
    }

    impl Default for BigFloat {
        fn default() -> BigFloat {
            BigFloat::new(DEFAULT_P)
        }
    }

    impl FromStr for BigFloat {
        type Err = ();

        /// Returns parsed number or NAN in case of error.
        fn from_str(src: &str) -> Result<BigFloat, Self::Err> {
            Ok(BigFloat::parse(src, Radix::Dec, DEFAULT_P, DEFAULT_RM))
        }
    }

    macro_rules! impl_from {
        ($tt:ty, $fn:ident) => {
            impl From<$tt> for BigFloat {
                fn from(v: $tt) -> Self {
                    BigFloat::$fn(v, DEFAULT_P)
                }
            }
        };
    }

    impl_from!(f32, from_f32);
    impl_from!(f64, from_f64);
    impl_from!(i8, from_i8);
    impl_from!(i16, from_i16);
    impl_from!(i32, from_i32);
    impl_from!(i64, from_i64);
    impl_from!(i128, from_i128);
    impl_from!(u8, from_u8);
    impl_from!(u16, from_u16);
    impl_from!(u32, from_u32);
    impl_from!(u64, from_u64);
    impl_from!(u128, from_u128);

    macro_rules! impl_format_rdx {
        ($trait:ty, $rdx:path) => {
            impl $trait for BigFloat {
                fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
                    self.write_str(f, $rdx, DEFAULT_RM)
                }
            }
        };
    }

    impl_format_rdx!(Binary, Radix::Bin);
    impl_format_rdx!(Octal, Radix::Oct);
    impl_format_rdx!(Display, Radix::Dec);
    impl_format_rdx!(UpperHex, Radix::Hex);
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::common::util::rand_p;
    use crate::{defs::RoundingMode, WORD_BIT_SIZE};

    #[cfg(feature = "std")]
    use std::str::FromStr;

    #[cfg(not(feature = "std"))]
    use core::str::FromStr;

    #[cfg(not(feature = "std"))]
    use alloc::format;

    #[test]
    fn test_ext() {
        let rm = RoundingMode::ToOdd;

        // Inf & NaN
        let d1 = BigFloat::from_u8(1, rand_p());
        assert!(!d1.is_inf());
        assert!(!d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.is_positive());

        let mut d1 = d1.div(&BigFloat::new(rand_p()), rand_p(), rm);
        assert!(d1.is_inf());
        assert!(!d1.is_nan());
        assert!(d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.is_positive());

        d1.inv_sign();
        assert!(d1.is_inf());
        assert!(!d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(d1.is_inf_neg());
        assert!(d1.is_negative());

        let d1 = BigFloat::new(rand_p()).div(&BigFloat::new(rand_p()), rand_p(), rm);
        assert!(!d1.is_inf());
        assert!(d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.get_sign().is_none());

        for _ in 0..1000 {
            let i = rand::random::<i64>();
            let d1 = BigFloat::from_i64(i, rand_p());
            let n1 = BigFloat::parse(&format!("{}", i), Radix::Dec, rand_p(), rm);
            assert!(d1.cmp(&n1) == Some(0));

            let i = rand::random::<u64>();
            let d1 = BigFloat::from_u64(i, rand_p());
            let n1 = BigFloat::parse(&format!("{}", i), Radix::Dec, rand_p(), rm);
            assert!(d1.cmp(&n1) == Some(0));

            let i = rand::random::<i128>();
            let d1 = BigFloat::from_i128(i, rand_p());
            let n1 = BigFloat::parse(&format!("{}", i), Radix::Dec, rand_p(), rm);
            assert!(d1.cmp(&n1) == Some(0));

            let i = rand::random::<u128>();
            let d1 = BigFloat::from_u128(i, rand_p());
            let n1 = BigFloat::parse(&format!("{}", i), Radix::Dec, rand_p(), rm);
            assert!(d1.cmp(&n1) == Some(0));
        }

        assert!(ONE.get_exponent().is_some());
        assert!(INF_POS.get_exponent().is_none());
        assert!(INF_NEG.get_exponent().is_none());
        assert!(NAN.get_exponent().is_none());

        assert!(ONE.to_raw_parts().is_some());
        assert!(INF_POS.to_raw_parts().is_none());
        assert!(INF_NEG.to_raw_parts().is_none());
        assert!(NAN.to_raw_parts().is_none());

        assert!(ONE.add(&ONE, rand_p(), rm).cmp(&TWO) == Some(0));
        assert!(ONE.add(&INF_POS, rand_p(), rm).is_inf_pos());
        assert!(INF_POS.add(&ONE, rand_p(), rm).is_inf_pos());
        assert!(ONE.add(&INF_NEG, rand_p(), rm).is_inf_neg());
        assert!(INF_NEG.add(&ONE, rand_p(), rm).is_inf_neg());
        assert!(INF_POS.add(&INF_POS, rand_p(), rm).is_inf_pos());
        assert!(INF_POS.add(&INF_NEG, rand_p(), rm).is_nan());
        assert!(INF_NEG.add(&INF_NEG, rand_p(), rm).is_inf_neg());
        assert!(INF_NEG.add(&INF_POS, rand_p(), rm).is_nan());

        assert!(ONE.add_full_prec(&ONE).cmp(&TWO) == Some(0));
        assert!(ONE.add_full_prec(&INF_POS).is_inf_pos());
        assert!(INF_POS.add_full_prec(&ONE).is_inf_pos());
        assert!(ONE.add_full_prec(&INF_NEG).is_inf_neg());
        assert!(INF_NEG.add_full_prec(&ONE).is_inf_neg());
        assert!(INF_POS.add_full_prec(&INF_POS).is_inf_pos());
        assert!(INF_POS.add_full_prec(&INF_NEG).is_nan());
        assert!(INF_NEG.add_full_prec(&INF_NEG).is_inf_neg());
        assert!(INF_NEG.add_full_prec(&INF_POS).is_nan());

        assert!(ONE.sub_full_prec(&ONE).is_zero());
        assert!(ONE.sub_full_prec(&INF_POS).is_inf_neg());
        assert!(INF_POS.sub_full_prec(&ONE).is_inf_pos());
        assert!(ONE.sub_full_prec(&INF_NEG).is_inf_pos());
        assert!(INF_NEG.sub_full_prec(&ONE).is_inf_neg());
        assert!(INF_POS.sub_full_prec(&INF_POS).is_nan());
        assert!(INF_POS.sub_full_prec(&INF_NEG).is_inf_pos());
        assert!(INF_NEG.sub_full_prec(&INF_NEG).is_nan());
        assert!(INF_NEG.sub_full_prec(&INF_POS).is_inf_neg());

        assert!(ONE.mul_full_prec(&ONE).cmp(&ONE) == Some(0));
        assert!(ONE.mul_full_prec(&INF_POS).is_inf_pos());
        assert!(INF_POS.mul_full_prec(&ONE).is_inf_pos());
        assert!(ONE.mul_full_prec(&INF_NEG).is_inf_neg());
        assert!(INF_NEG.mul_full_prec(&ONE).is_inf_neg());
        assert!(INF_POS.mul_full_prec(&INF_POS).is_inf_pos());
        assert!(INF_POS.mul_full_prec(&INF_NEG).is_inf_neg());
        assert!(INF_NEG.mul_full_prec(&INF_NEG).is_inf_pos());
        assert!(INF_NEG.mul_full_prec(&INF_POS).is_inf_neg());

        assert!(TWO.sub(&ONE, rand_p(), rm).cmp(&ONE) == Some(0));
        assert!(ONE.sub(&INF_POS, rand_p(), rm).is_inf_neg());
        assert!(INF_POS.sub(&ONE, rand_p(), rm).is_inf_pos());
        assert!(ONE.sub(&INF_NEG, rand_p(), rm).is_inf_pos());
        assert!(INF_NEG.sub(&ONE, rand_p(), rm).is_inf_neg());
        assert!(INF_POS.sub(&INF_POS, rand_p(), rm).is_nan());
        assert!(INF_POS.sub(&INF_NEG, rand_p(), rm).is_inf_pos());
        assert!(INF_NEG.sub(&INF_NEG, rand_p(), rm).is_nan());
        assert!(INF_NEG.sub(&INF_POS, rand_p(), rm).is_inf_neg());

        assert!(TWO.mul(&ONE, rand_p(), rm).cmp(&TWO) == Some(0));
        assert!(ONE.mul(&INF_POS, rand_p(), rm).is_inf_pos());
        assert!(INF_POS.mul(&ONE, rand_p(), rm).is_inf_pos());
        assert!(ONE.mul(&INF_NEG, rand_p(), rm).is_inf_neg());
        assert!(INF_NEG.mul(&ONE, rand_p(), rm).is_inf_neg());
        assert!(ONE.neg().mul(&INF_POS, rand_p(), rm).is_inf_neg());
        assert!(ONE.neg().mul(&INF_NEG, rand_p(), rm).is_inf_pos());
        assert!(INF_POS.mul(&ONE.neg(), rand_p(), rm).is_inf_neg());
        assert!(INF_NEG.mul(&ONE.neg(), rand_p(), rm).is_inf_pos());
        assert!(INF_POS.mul(&INF_POS, rand_p(), rm).is_inf_pos());
        assert!(INF_POS.mul(&INF_NEG, rand_p(), rm).is_inf_neg());
        assert!(INF_NEG.mul(&INF_NEG, rand_p(), rm).is_inf_pos());
        assert!(INF_NEG.mul(&INF_POS, rand_p(), rm).is_inf_neg());
        assert!(INF_POS.mul(&BigFloat::new(rand_p()), rand_p(), rm).is_nan());
        assert!(INF_NEG.mul(&BigFloat::new(rand_p()), rand_p(), rm).is_nan());
        assert!(BigFloat::new(rand_p()).mul(&INF_POS, rand_p(), rm).is_nan());
        assert!(BigFloat::new(rand_p()).mul(&INF_NEG, rand_p(), rm).is_nan());

        assert!(TWO.div(&TWO, rand_p(), rm).cmp(&ONE) == Some(0));
        assert!(TWO.div(&INF_POS, rand_p(), rm).is_zero());
        assert!(INF_POS.div(&TWO, rand_p(), rm).is_inf_pos());
        assert!(TWO.div(&INF_NEG, rand_p(), rm).is_zero());
        assert!(INF_NEG.div(&TWO, rand_p(), rm).is_inf_neg());
        assert!(TWO.neg().div(&INF_POS, rand_p(), rm).is_zero());
        assert!(TWO.neg().div(&INF_NEG, rand_p(), rm).is_zero());
        assert!(INF_POS.div(&TWO.neg(), rand_p(), rm).is_inf_neg());
        assert!(INF_NEG.div(&TWO.neg(), rand_p(), rm).is_inf_pos());
        assert!(INF_POS.div(&INF_POS, rand_p(), rm).is_nan());
        assert!(INF_POS.div(&INF_NEG, rand_p(), rm).is_nan());
        assert!(INF_NEG.div(&INF_NEG, rand_p(), rm).is_nan());
        assert!(INF_NEG.div(&INF_POS, rand_p(), rm).is_nan());
        assert!(INF_POS
            .div(&BigFloat::new(rand_p()), rand_p(), rm)
            .is_inf_pos());
        assert!(INF_NEG
            .div(&BigFloat::new(rand_p()), rand_p(), rm)
            .is_inf_neg());
        assert!(BigFloat::new(rand_p())
            .div(&INF_POS, rand_p(), rm)
            .is_zero());
        assert!(BigFloat::new(rand_p())
            .div(&INF_NEG, rand_p(), rm)
            .is_zero());

        assert!(TWO.rem(&TWO).is_zero());
        assert!(TWO.rem(&INF_POS).cmp(&TWO) == Some(0));
        assert!(INF_POS.rem(&TWO).is_nan());
        assert!(TWO.rem(&INF_NEG).cmp(&TWO) == Some(0));
        assert!(INF_NEG.rem(&TWO).is_nan());
        assert!(TWO.neg().rem(&INF_POS).cmp(&TWO.neg()) == Some(0));
        assert!(TWO.neg().rem(&INF_NEG).cmp(&TWO.neg()) == Some(0));
        assert!(INF_POS.rem(&TWO.neg()).is_nan());
        assert!(INF_NEG.rem(&TWO.neg()).is_nan());
        assert!(INF_POS.rem(&INF_POS).is_nan());
        assert!(INF_POS.rem(&INF_NEG).is_nan());
        assert!(INF_NEG.rem(&INF_NEG).is_nan());
        assert!(INF_NEG.rem(&INF_POS).is_nan());
        assert!(INF_POS.rem(&BigFloat::new(rand_p())).is_nan());
        assert!(INF_NEG.rem(&BigFloat::new(rand_p())).is_nan());
        assert!(BigFloat::new(rand_p()).rem(&INF_POS).is_zero());
        assert!(BigFloat::new(rand_p()).rem(&INF_NEG).is_zero());

        for op in [BigFloat::add, BigFloat::sub, BigFloat::mul, BigFloat::div] {
            assert!(op(&NAN, &ONE, rand_p(), rm).is_nan());
            assert!(op(&ONE, &NAN, rand_p(), rm).is_nan());
            assert!(op(&NAN, &INF_POS, rand_p(), rm).is_nan());
            assert!(op(&INF_POS, &NAN, rand_p(), rm).is_nan());
            assert!(op(&NAN, &INF_NEG, rand_p(), rm).is_nan());
            assert!(op(&INF_NEG, &NAN, rand_p(), rm).is_nan());
            assert!(op(&NAN, &NAN, rand_p(), rm).is_nan());
        }

        assert!(BigFloat::rem(&NAN, &ONE).is_nan());
        assert!(BigFloat::rem(&ONE, &NAN).is_nan());
        assert!(BigFloat::rem(&NAN, &INF_POS).is_nan());
        assert!(BigFloat::rem(&INF_POS, &NAN).is_nan());
        assert!(BigFloat::rem(&NAN, &INF_NEG).is_nan());
        assert!(BigFloat::rem(&INF_NEG, &NAN).is_nan());
        assert!(BigFloat::rem(&NAN, &NAN).is_nan());

        for op in [BigFloat::add_full_prec, BigFloat::sub_full_prec, BigFloat::mul_full_prec] {
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
        assert!(INF_POS.cmp(&INF_NEG).unwrap() > 0);
        assert!(INF_NEG.cmp(&INF_POS).unwrap() < 0);
        assert!(INF_POS.cmp(&INF_POS).unwrap() == 0);
        assert!(ONE.cmp(&NAN).is_none());
        assert!(NAN.cmp(&ONE).is_none());
        assert!(INF_POS.cmp(&NAN).is_none());
        assert!(NAN.cmp(&INF_POS).is_none());
        assert!(INF_NEG.cmp(&NAN).is_none());
        assert!(NAN.cmp(&INF_NEG).is_none());
        assert!(NAN.cmp(&NAN).is_none());

        assert!(ONE.abs_cmp(&ONE).unwrap() == 0);
        assert!(ONE.abs_cmp(&INF_POS).unwrap() < 0);
        assert!(INF_POS.abs_cmp(&ONE).unwrap() > 0);
        assert!(INF_POS.abs_cmp(&INF_POS).unwrap() == 0);
        assert!(ONE.abs_cmp(&INF_NEG).unwrap() < 0);
        assert!(INF_NEG.abs_cmp(&ONE).unwrap() > 0);
        assert!(INF_NEG.abs_cmp(&INF_NEG).unwrap() == 0);
        assert!(INF_POS.abs_cmp(&INF_NEG).unwrap() == 0);
        assert!(INF_NEG.abs_cmp(&INF_POS).unwrap() == 0);
        assert!(INF_POS.abs_cmp(&INF_POS).unwrap() == 0);
        assert!(ONE.abs_cmp(&NAN).is_none());
        assert!(NAN.abs_cmp(&ONE).is_none());
        assert!(INF_POS.abs_cmp(&NAN).is_none());
        assert!(NAN.abs_cmp(&INF_POS).is_none());
        assert!(INF_NEG.abs_cmp(&NAN).is_none());
        assert!(NAN.abs_cmp(&INF_NEG).is_none());
        assert!(NAN.abs_cmp(&NAN).is_none());

        assert!(ONE.is_positive());
        assert!(!ONE.is_negative());

        assert!(ONE.neg().is_negative());
        assert!(!ONE.neg().is_positive());
        assert!(!INF_POS.is_negative());
        assert!(INF_POS.is_positive());
        assert!(INF_NEG.is_negative());
        assert!(!INF_NEG.is_positive());
        assert!(!NAN.is_positive());
        assert!(!NAN.is_negative());

        let mut cc = Consts::new().unwrap();

        assert!(ONE.pow(&ONE, rand_p(), rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(BigFloat::new(DEFAULT_P)
            .pow(&INF_POS, rand_p(), rm, &mut cc)
            .is_zero());
        assert!(BigFloat::new(DEFAULT_P)
            .pow(&INF_NEG, rand_p(), rm, &mut cc)
            .is_zero());
        assert!(ONE.pow(&INF_POS, rand_p(), rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(ONE.pow(&INF_NEG, rand_p(), rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(TWO.pow(&INF_POS, rand_p(), rm, &mut cc).is_inf_pos());
        assert!(TWO.pow(&INF_NEG, rand_p(), rm, &mut cc).is_inf_neg());
        assert!(INF_POS.pow(&ONE, rand_p(), rm, &mut cc).is_inf_pos());
        assert!(INF_NEG.pow(&ONE, rand_p(), rm, &mut cc).is_inf_neg());
        assert!(INF_NEG.pow(&TWO, rand_p(), rm, &mut cc).is_inf_pos());
        assert!(INF_NEG
            .pow(&BigFloat::from_f64(10.2, DEFAULT_P), rand_p(), rm, &mut cc)
            .is_inf_pos());
        assert!(INF_NEG
            .pow(&BigFloat::from_f64(3.0, DEFAULT_P), rand_p(), rm, &mut cc)
            .is_inf_neg());
        assert!(INF_POS.pow(&ONE.neg(), rand_p(), rm, &mut cc).is_zero());
        assert!(INF_NEG.pow(&ONE.neg(), rand_p(), rm, &mut cc).is_zero());
        assert!(
            INF_POS
                .pow(&BigFloat::new(DEFAULT_P), rand_p(), rm, &mut cc)
                .cmp(&ONE)
                == Some(0)
        );
        assert!(
            INF_NEG
                .pow(&BigFloat::new(DEFAULT_P), rand_p(), rm, &mut cc)
                .cmp(&ONE)
                == Some(0)
        );
        assert!(INF_POS.pow(&INF_POS, rand_p(), rm, &mut cc).is_inf_pos());
        assert!(INF_NEG.pow(&INF_POS, rand_p(), rm, &mut cc).is_inf_pos());
        assert!(INF_POS.pow(&INF_NEG, rand_p(), rm, &mut cc).is_zero());
        assert!(INF_NEG.pow(&INF_NEG, rand_p(), rm, &mut cc).is_zero());

        let half = ONE.div(&TWO, rand_p(), rm);
        assert!(TWO.log(&TWO, rand_p(), rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(TWO.log(&INF_POS, rand_p(), rm, &mut cc).is_zero());
        assert!(TWO.log(&INF_NEG, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.log(&TWO, rand_p(), rm, &mut cc).is_inf_pos());
        assert!(INF_NEG.log(&TWO, rand_p(), rm, &mut cc).is_nan());
        assert!(half.log(&half, rand_p(), rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(half.log(&INF_POS, rand_p(), rm, &mut cc).is_zero());
        assert!(half.log(&INF_NEG, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.log(&half, rand_p(), rm, &mut cc).is_inf_neg());
        assert!(INF_NEG.log(&half, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.log(&INF_POS, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.log(&INF_NEG, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_NEG.log(&INF_POS, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_NEG.log(&INF_NEG, rand_p(), rm, &mut cc).is_nan());
        assert!(TWO.log(&ONE, rand_p(), rm, &mut cc).is_inf_pos());
        assert!(half.log(&ONE, rand_p(), rm, &mut cc).is_inf_pos());
        assert!(ONE.log(&ONE, rand_p(), rm, &mut cc).is_nan());

        assert!(BigFloat::from_f32(f32::NAN, DEFAULT_P).is_nan());
        assert!(BigFloat::from_f32(f32::INFINITY, DEFAULT_P).is_inf_pos());
        assert!(BigFloat::from_f32(f32::NEG_INFINITY, DEFAULT_P).is_inf_neg());
        assert!(!BigFloat::from_f32(1.0, DEFAULT_P).is_nan());
        assert!(BigFloat::from_f64(f64::NAN, DEFAULT_P).is_nan());
        assert!(BigFloat::from_f64(f64::INFINITY, DEFAULT_P).is_inf_pos());
        assert!(BigFloat::from_f64(f64::NEG_INFINITY, DEFAULT_P).is_inf_neg());
        assert!(!BigFloat::from_f64(1.0, DEFAULT_P).is_nan());

        assert!(ONE.pow(&NAN, rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.pow(&ONE, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.pow(&NAN, rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.pow(&INF_POS, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_NEG.pow(&NAN, rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.pow(&INF_NEG, rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.pow(&NAN, rand_p(), rm, &mut cc).is_nan());

        assert!(NAN.powi(2, rand_p(), rm).is_nan());
        assert!(NAN.powi(0, rand_p(), rm).is_nan());
        assert!(INF_POS.powi(2, rand_p(), rm).is_inf_pos());
        assert!(INF_POS.powi(3, rand_p(), rm).is_inf_pos());
        assert!(INF_NEG.powi(4, rand_p(), rm).is_inf_pos());
        assert!(INF_NEG.powi(5, rand_p(), rm).is_inf_neg());
        assert!(INF_POS.powi(0, rand_p(), rm).cmp(&ONE) == Some(0));
        assert!(INF_NEG.powi(0, rand_p(), rm).cmp(&ONE) == Some(0));

        assert!(TWO.log(&NAN, rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.log(&TWO, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.log(&NAN, rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.log(&INF_POS, rand_p(), rm, &mut cc).is_nan());
        assert!(INF_NEG.log(&NAN, rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.log(&INF_NEG, rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.log(&NAN, rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.abs().is_inf_pos());
        assert!(INF_POS.abs().is_inf_pos());
        assert!(NAN.abs().is_nan());

        assert!(INF_NEG.int().is_nan());
        assert!(INF_POS.int().is_nan());
        assert!(NAN.int().is_nan());

        assert!(INF_NEG.fract().is_nan());
        assert!(INF_POS.fract().is_nan());
        assert!(NAN.fract().is_nan());

        assert!(INF_NEG.ceil().is_inf_neg());
        assert!(INF_POS.ceil().is_inf_pos());
        assert!(NAN.ceil().is_nan());

        assert!(INF_NEG.floor().is_inf_neg());
        assert!(INF_POS.floor().is_inf_pos());
        assert!(NAN.floor().is_nan());

        for rm in [
            RoundingMode::Up,
            RoundingMode::Down,
            RoundingMode::ToZero,
            RoundingMode::FromZero,
            RoundingMode::ToEven,
            RoundingMode::ToOdd,
        ] {
            assert!(INF_NEG.round(0, rm).is_inf_neg());
            assert!(INF_POS.round(0, rm).is_inf_pos());
            assert!(NAN.round(0, rm).is_nan());
        }

        assert!(INF_NEG.sqrt(rand_p(), rm).is_nan());
        assert!(INF_POS.sqrt(rand_p(), rm).is_inf_pos());
        assert!(NAN.sqrt(rand_p(), rm).is_nan());

        assert!(INF_NEG.cbrt(rand_p(), rm).is_inf_neg());
        assert!(INF_POS.cbrt(rand_p(), rm).is_inf_pos());
        assert!(NAN.cbrt(rand_p(), rm).is_nan());

        for op in [BigFloat::ln, BigFloat::log2, BigFloat::log10] {
            assert!(op(&INF_NEG, rand_p(), rm, &mut cc).is_nan());
            assert!(op(&INF_POS, rand_p(), rm, &mut cc).is_inf_pos());
            assert!(op(&NAN, rand_p(), rm, &mut cc).is_nan());
        }

        assert!(INF_NEG.exp(rand_p(), rm, &mut cc).is_inf_neg());
        assert!(INF_POS.exp(rand_p(), rm, &mut cc).is_inf_pos());
        assert!(NAN.exp(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.sin(rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.sin(rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.sin(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.cos(rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.cos(rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.cos(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.tan(rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.tan(rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.tan(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.asin(rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.asin(rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.asin(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.acos(rand_p(), rm, &mut cc).is_nan());
        assert!(INF_POS.acos(rand_p(), rm, &mut cc).is_nan());
        assert!(NAN.acos(rand_p(), rm, &mut cc).is_nan());

        let p = rand_p();
        let mut half_pi: BigFloat = cc.pi(p, rm).unwrap().into();
        half_pi.set_exponent(1);
        assert!(INF_NEG.atan(p, rm, &mut cc).cmp(&half_pi.neg()) == Some(0));
        assert!(INF_POS.atan(p, rm, &mut cc).cmp(&half_pi) == Some(0));
        assert!(NAN.atan(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.sinh(rand_p(), rm, &mut cc).is_inf_neg());
        assert!(INF_POS.sinh(rand_p(), rm, &mut cc).is_inf_pos());
        assert!(NAN.sinh(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.cosh(rand_p(), rm, &mut cc).is_inf_pos());
        assert!(INF_POS.cosh(rand_p(), rm, &mut cc).is_inf_pos());
        assert!(NAN.cosh(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.tanh(rand_p(), rm, &mut cc).cmp(&ONE.neg()) == Some(0));
        assert!(INF_POS.tanh(rand_p(), rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(NAN.tanh(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.asinh(rand_p(), rm, &mut cc).is_inf_neg());
        assert!(INF_POS.asinh(rand_p(), rm, &mut cc).is_inf_pos());
        assert!(NAN.asinh(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.acosh(rand_p(), rm, &mut cc).is_zero());
        assert!(INF_POS.acosh(rand_p(), rm, &mut cc).is_zero());
        assert!(NAN.acosh(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.atanh(rand_p(), rm, &mut cc).is_zero());
        assert!(INF_POS.atanh(rand_p(), rm, &mut cc).is_zero());
        assert!(NAN.atanh(rand_p(), rm, &mut cc).is_nan());

        assert!(INF_NEG.reciprocal(rand_p(), rm).is_zero());
        assert!(INF_POS.reciprocal(rand_p(), rm).is_zero());
        assert!(NAN.reciprocal(rand_p(), rm).is_nan());

        assert!(TWO.signum().cmp(&ONE) == Some(0));
        assert!(TWO.neg().signum().cmp(&ONE.neg()) == Some(0));
        assert!(INF_POS.signum().cmp(&ONE) == Some(0));
        assert!(INF_NEG.signum().cmp(&ONE.neg()) == Some(0));
        assert!(NAN.signum().is_nan());

        let d1 = ONE.clone();
        assert!(d1.get_exponent() == Some(1));
        assert!(d1.get_mantissa_digits() == Some(&[0, 0x8000000000000000]));
        assert!(d1.get_mantissa_max_bit_len() == Some(DEFAULT_P));
        assert!(d1.get_precision() == Some(DEFAULT_P));
        assert!(d1.get_sign() == Some(Sign::Pos));

        assert!(INF_POS.get_exponent().is_none());
        assert!(INF_POS.get_mantissa_digits().is_none());
        assert!(INF_POS.get_mantissa_max_bit_len().is_none());
        assert!(INF_POS.get_precision().is_none());
        assert!(INF_POS.get_sign() == Some(Sign::Pos));

        assert!(INF_NEG.get_exponent().is_none());
        assert!(INF_NEG.get_mantissa_digits().is_none());
        assert!(INF_NEG.get_mantissa_max_bit_len().is_none());
        assert!(INF_NEG.get_precision().is_none());
        assert!(INF_NEG.get_sign() == Some(Sign::Neg));

        assert!(NAN.get_exponent().is_none());
        assert!(NAN.get_mantissa_digits().is_none());
        assert!(NAN.get_mantissa_max_bit_len().is_none());
        assert!(NAN.get_precision().is_none());
        assert!(NAN.get_sign().is_none());

        INF_POS.clone().set_exponent(1);
        INF_POS.clone().set_precision(1, rm).unwrap();
        INF_POS.clone().set_sign(Sign::Pos);

        INF_NEG.clone().set_exponent(1);
        INF_NEG.clone().set_precision(1, rm).unwrap();
        INF_NEG.clone().set_sign(Sign::Pos);

        NAN.clone().set_exponent(1);
        NAN.clone().set_precision(1, rm).unwrap();
        NAN.clone().set_sign(Sign::Pos);

        assert!(INF_POS.min(&ONE).cmp(&ONE) == Some(0));
        assert!(INF_NEG.min(&ONE).is_inf_neg());
        assert!(NAN.min(&ONE).is_nan());
        assert!(ONE.min(&INF_POS).cmp(&ONE) == Some(0));
        assert!(ONE.min(&INF_NEG).is_inf_neg());
        assert!(ONE.min(&NAN).is_nan());
        assert!(NAN.min(&INF_POS).is_nan());
        assert!(NAN.min(&INF_NEG).is_nan());
        assert!(NAN.min(&NAN).is_nan());
        assert!(INF_NEG.min(&INF_POS).is_inf_neg());
        assert!(INF_POS.min(&INF_NEG).is_inf_neg());
        assert!(INF_POS.min(&INF_POS).is_inf_pos());
        assert!(INF_NEG.min(&INF_NEG).is_inf_neg());

        assert!(INF_POS.max(&ONE).is_inf_pos());
        assert!(INF_NEG.max(&ONE).cmp(&ONE) == Some(0));
        assert!(NAN.max(&ONE).is_nan());
        assert!(ONE.max(&INF_POS).is_inf_pos());
        assert!(ONE.max(&INF_NEG).cmp(&ONE) == Some(0));
        assert!(ONE.max(&NAN).is_nan());
        assert!(NAN.max(&INF_POS).is_nan());
        assert!(NAN.max(&INF_NEG).is_nan());
        assert!(NAN.max(&NAN).is_nan());
        assert!(INF_NEG.max(&INF_POS).is_inf_pos());
        assert!(INF_POS.max(&INF_NEG).is_inf_pos());
        assert!(INF_POS.max(&INF_POS).is_inf_pos());
        assert!(INF_NEG.max(&INF_NEG).is_inf_neg());

        assert!(ONE.clamp(&ONE.neg(), &TWO).cmp(&ONE) == Some(0));
        assert!(ONE.clamp(&TWO, &ONE).is_nan());
        assert!(ONE.clamp(&INF_POS, &ONE).is_nan());
        assert!(ONE.clamp(&TWO, &INF_NEG).is_nan());
        assert!(ONE.neg().clamp(&ONE, &TWO).cmp(&ONE) == Some(0));
        assert!(TWO.clamp(&ONE.neg(), &ONE).cmp(&ONE) == Some(0));
        assert!(INF_POS.clamp(&ONE, &TWO).cmp(&TWO) == Some(0));
        assert!(INF_POS.clamp(&ONE, &INF_POS).is_inf_pos());
        assert!(INF_POS.clamp(&INF_NEG, &ONE).cmp(&ONE) == Some(0));
        assert!(INF_POS.clamp(&NAN, &INF_POS).is_nan());
        assert!(INF_POS.clamp(&ONE, &NAN).is_nan());
        assert!(INF_POS.clamp(&NAN, &NAN).is_nan());
        assert!(INF_NEG.clamp(&ONE, &TWO).cmp(&ONE) == Some(0));
        assert!(INF_NEG.clamp(&ONE, &INF_POS).cmp(&ONE) == Some(0));
        assert!(INF_NEG.clamp(&INF_NEG, &ONE).is_inf_neg());
        assert!(INF_NEG.clamp(&NAN, &INF_POS).is_nan());
        assert!(INF_NEG.clamp(&ONE, &NAN).is_nan());
        assert!(INF_NEG.clamp(&NAN, &NAN).is_nan());
        assert!(NAN.clamp(&ONE, &TWO).is_nan());
        assert!(NAN.clamp(&NAN, &TWO).is_nan());
        assert!(NAN.clamp(&ONE, &NAN).is_nan());
        assert!(NAN.clamp(&NAN, &NAN).is_nan());
        assert!(NAN.clamp(&INF_NEG, &INF_POS).is_nan());

        assert!(BigFloat::min_positive(DEFAULT_P).classify() == FpCategory::Subnormal);
        assert!(INF_POS.classify() == FpCategory::Infinite);
        assert!(INF_NEG.classify() == FpCategory::Infinite);
        assert!(NAN.classify() == FpCategory::Nan);
        assert!(ONE.classify() == FpCategory::Normal);

        assert!(!INF_POS.is_subnormal());
        assert!(!INF_NEG.is_subnormal());
        assert!(!NAN.is_subnormal());
        assert!(BigFloat::min_positive(DEFAULT_P).is_subnormal());
        assert!(!BigFloat::min_positive_normal(DEFAULT_P).is_subnormal());
        assert!(!BigFloat::max_value(DEFAULT_P).is_subnormal());
        assert!(!BigFloat::min_value(DEFAULT_P).is_subnormal());

        let n1 = BigFloat::convert_from_radix(
            Sign::Pos,
            &[],
            0,
            Radix::Dec,
            usize::MAX,
            RoundingMode::None,
        );
        assert!(n1.is_nan());
        assert!(n1.get_err() == Some(Error::InvalidArgument));

        assert!(n1.convert_to_radix(Radix::Dec, RoundingMode::None) == Err(Error::InvalidArgument));
        assert!(
            INF_POS.convert_to_radix(Radix::Dec, RoundingMode::None) == Err(Error::InvalidArgument)
        );
        assert!(
            INF_NEG.convert_to_radix(Radix::Dec, RoundingMode::None) == Err(Error::InvalidArgument)
        );
    }

    #[test]
    pub fn test_ops() {
        let d1 = -&(TWO.clone());
        assert!(d1.is_negative());

        let d1 = BigFloat::parse(
            "0.0123456789012345678901234567890123456789",
            Radix::Dec,
            DEFAULT_P,
            RoundingMode::None,
        );

        let d1str = format!("{}", d1);
        assert_eq!(&d1str, "1.234567890123456789012345678901234567889e-2");
        assert!(BigFloat::from_str(&d1str).unwrap() == d1);

        let d1 = BigFloat::parse(
            "-123.456789012345678901234567890123456789",
            Radix::Dec,
            DEFAULT_P,
            RoundingMode::None,
        );
        let d1str = format!("{}", d1);
        assert_eq!(&d1str, "-1.23456789012345678901234567890123456788918e+2");
        assert_eq!(BigFloat::from_str(&d1str).unwrap(), d1);

        let d1str = format!("{}", INF_POS);
        assert_eq!(d1str, "Inf");

        let d1str = format!("{}", INF_NEG);
        assert_eq!(d1str, "-Inf");

        let d1str = format!("{}", NAN);
        assert_eq!(d1str, "NaN");

        assert!(BigFloat::from_str("abc").is_ok());
        assert!(BigFloat::from_str("abc").unwrap().is_nan());

        let p = DEFAULT_P;
        let rm = RoundingMode::ToEven;
        assert!(BigFloat::from_i8(-123, p) == BigFloat::parse("-1.23e+2", Radix::Dec, p, rm));
        assert!(BigFloat::from_u8(123, p) == BigFloat::parse("1.23e+2", Radix::Dec, p, rm));
        assert!(BigFloat::from_i16(-12312, p) == BigFloat::parse("-1.2312e+4", Radix::Dec, p, rm));
        assert!(BigFloat::from_u16(12312, p) == BigFloat::parse("1.2312e+4", Radix::Dec, p, rm));
        assert!(
            BigFloat::from_i32(-123456789, p)
                == BigFloat::parse("-1.23456789e+8", Radix::Dec, p, rm)
        );
        assert!(
            BigFloat::from_u32(123456789, p) == BigFloat::parse("1.23456789e+8", Radix::Dec, p, rm)
        );
        assert!(
            BigFloat::from_i64(-1234567890123456789, p)
                == BigFloat::parse("-1.234567890123456789e+18", Radix::Dec, p, rm)
        );
        assert!(
            BigFloat::from_u64(1234567890123456789, p)
                == BigFloat::parse("1.234567890123456789e+18", Radix::Dec, p, rm)
        );
        assert!(
            BigFloat::from_i128(-123456789012345678901234567890123456789, p)
                == BigFloat::parse(
                    "-1.23456789012345678901234567890123456789e+38",
                    Radix::Dec,
                    p,
                    rm
                )
        );
        assert!(
            BigFloat::from_u128(123456789012345678901234567890123456789, p)
                == BigFloat::parse(
                    "1.23456789012345678901234567890123456789e+38",
                    Radix::Dec,
                    p,
                    rm
                )
        );

        let neg = BigFloat::from_i8(-3, WORD_BIT_SIZE);
        let pos = BigFloat::from_i8(5, WORD_BIT_SIZE);

        assert!(pos > neg);
        assert!(neg < pos);
        assert!(!(pos < neg));
        assert!(!(neg > pos));
        assert!(INF_NEG < neg);
        assert!(INF_NEG < pos);
        assert!(INF_NEG < INF_POS);
        assert!(!(INF_NEG > neg));
        assert!(!(INF_NEG > pos));
        assert!(!(INF_NEG > INF_POS));
        assert!(INF_POS > neg);
        assert!(INF_POS > pos);
        assert!(INF_POS > INF_NEG);
        assert!(!(INF_POS < neg));
        assert!(!(INF_POS < pos));
        assert!(!(INF_POS < INF_NEG));
        assert!(!(INF_POS > INF_POS));
        assert!(!(INF_POS < INF_POS));
        assert!(!(INF_NEG > INF_NEG));
        assert!(!(INF_NEG < INF_NEG));
        assert!(!(INF_POS > NAN));
        assert!(!(INF_POS < NAN));
        assert!(!(INF_NEG > NAN));
        assert!(!(INF_NEG < NAN));
        assert!(!(NAN > INF_POS));
        assert!(!(NAN < INF_POS));
        assert!(!(NAN > INF_NEG));
        assert!(!(NAN < INF_NEG));
        assert!(!(NAN > NAN));
        assert!(!(NAN < NAN));
        assert!(!(neg > NAN));
        assert!(!(neg < NAN));
        assert!(!(pos > NAN));
        assert!(!(pos < NAN));
        assert!(!(NAN > neg));
        assert!(!(NAN < neg));
        assert!(!(NAN > pos));
        assert!(!(NAN < pos));

        assert!(!(NAN == NAN));
        assert!(!(NAN == INF_POS));
        assert!(!(NAN == INF_NEG));
        assert!(!(INF_POS == NAN));
        assert!(!(INF_NEG == NAN));
        assert!(!(INF_NEG == INF_POS));
        assert!(!(INF_POS == INF_NEG));
        assert!(!(INF_POS == neg));
        assert!(!(INF_POS == pos));
        assert!(!(INF_NEG == neg));
        assert!(!(INF_NEG == pos));
        assert!(!(neg == INF_POS));
        assert!(!(pos == INF_POS));
        assert!(!(neg == INF_NEG));
        assert!(!(pos == INF_NEG));
        assert!(!(pos == neg));
        assert!(!(neg == pos));
        assert!(neg == neg);
        assert!(pos == pos);
        assert!(INF_NEG == INF_NEG);
        assert!(INF_POS == INF_POS);
    }
}

#[cfg(feature = "random")]
#[cfg(test)]
mod rand_tests {

    use super::*;
    use crate::defs::EXPONENT_MAX;

    #[test]
    fn test_rand() {
        for _ in 0..1000 {
            let p = rand::random::<usize>() % 1000 + DEFAULT_P;
            let exp_from = rand::random::<Exponent>();
            let exp_shift = if EXPONENT_MAX > exp_from {
                rand::random::<Exponent>().abs()
                    % (EXPONENT_MAX as isize - exp_from as isize) as Exponent
            } else {
                0
            };
            let exp_to = (exp_from as isize + exp_shift as isize) as Exponent;

            let n = BigFloat::random_normal(p, exp_from, exp_to);

            assert!(!n.is_subnormal());
            assert!(n.get_exponent().unwrap() >= exp_from && n.get_exponent().unwrap() <= exp_to);
            assert!(n.get_precision().unwrap() >= p);
        }
    }
}
