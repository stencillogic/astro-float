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
use alloc::string::String;

/// Not a number.
pub const NAN: BigFloat = BigFloat { inner: Flavor::NaN };

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

/// Number representation.
#[derive(Debug)]
pub struct BigFloat {
    inner: Flavor,
}

#[derive(Debug)]
enum Flavor {
    Value(BigFloatNumber),
    NaN,
    Inf(Sign), // signed Inf
}

impl BigFloat {
    /// Returns a new BigFloat with the value of zero and precision `p`.
    pub fn new(p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::new(p), false, true)
    }

    /// Creates a BigFloat from f64.\
    pub fn from_f64(f: f64, p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::from_f64(p, f), false, true)
    }

    /// Creates a BigFloat from f32.
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
        matches!(self.inner, Flavor::NaN)
    }

    /// Adds `d2` to `self` and returns the result of the addition.
    pub fn add(&self, d2: &Self, rm: RoundingMode) -> Self {
        self.add_op(d2, rm, false)
    }

    /// Adds `d2` to `self` and returns the result of the addition.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer addition.
    pub fn add_full_prec(&self, d2: &Self) -> Self {
        self.add_op(d2, RoundingMode::None, true)
    }

    fn add_op(&self, d2: &Self, rm: RoundingMode, full_prec: bool) -> Self {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Self::result_to_ext(
                    if full_prec { v1.add_full_prec(v2) } else { v1.add(v2, rm) },
                    v1.is_zero(),
                    v1.get_sign() == v2.get_sign(),
                ),
                Flavor::Inf(s2) => BigFloat {
                    inner: Flavor::Inf(*s2),
                },
                Flavor::NaN => NAN,
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
                Flavor::NaN => NAN,
            },
            Flavor::NaN => NAN,
        }
    }

    /// Subtracts `d2` from `self` and return the result of the subtraction.
    pub fn sub(&self, d2: &Self, rm: RoundingMode) -> Self {
        self.sub_op(d2, rm, false)
    }

    /// Subtracts `d2` from `self` and returns the result of the operation.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer subtraction.
    pub fn sub_full_prec(&self, d2: &Self) -> Self {
        self.sub_op(d2, RoundingMode::None, true)
    }

    fn sub_op(&self, d2: &Self, rm: RoundingMode, full_prec: bool) -> Self {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Self::result_to_ext(
                    if full_prec { v1.sub_full_prec(v2) } else { v1.sub(v2, rm) },
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
                Flavor::NaN => NAN,
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
                Flavor::NaN => NAN,
            },
            Flavor::NaN => NAN,
        }
    }

    /// Multiplies `self` by `d2` and returns the result of the multiplication.
    pub fn mul(&self, d2: &Self, rm: RoundingMode) -> Self {
        self.mul_op(d2, rm, false)
    }

    /// Multiplies `d2` by `self` and returns the result of the operation.
    /// The resulting precision is equal to the full precision of the result.
    /// This operation can be used to emulate integer multiplication.
    pub fn mul_full_prec(&self, d2: &Self) -> Self {
        self.mul_op(d2, RoundingMode::None, true)
    }

    /// Multiplies `self` by `d2` and returns the result of the multiplication.
    fn mul_op(&self, d2: &Self, rm: RoundingMode, full_prec: bool) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d2.inner {
                    Flavor::Value(v2) => Self::result_to_ext(
                        if full_prec { v1.mul_full_prec(v2) } else { v1.mul(v2, rm) },
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
                    Flavor::NaN => NAN,
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
                    Flavor::NaN => NAN,
                }
            }
            Flavor::NaN => NAN,
        }
    }

    /// Divides `self` by `d2` and returns the result of the division.
    pub fn div(&self, d2: &Self, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Self::result_to_ext(
                    v1.div(v2, rm),
                    v1.is_zero(),
                    v1.get_sign() == v2.get_sign(),
                ),
                Flavor::Inf(_) => Self::new(v1.get_mantissa_max_bit_len()),
                Flavor::NaN => NAN,
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
                Flavor::NaN => NAN,
            },
            Flavor::NaN => NAN,
        }
    }

    /// Returns the remainder of division of `self` by `d1`.
    pub fn rem(&self, d2: &Self, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => match &d2.inner {
                Flavor::Value(v2) => Self::result_to_ext(
                    v1.rem(v2, rm),
                    v1.is_zero(),
                    v1.get_sign() == v2.get_sign(),
                ),
                Flavor::Inf(_) => self.clone(),
                Flavor::NaN => NAN,
            },
            Flavor::Inf(_) => NAN,
            Flavor::NaN => NAN,
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
                Flavor::NaN => None,
            },
            Flavor::Inf(s1) => match &d2.inner {
                Flavor::Value(_) => Some(*s1 as SignedWord),
                Flavor::Inf(s2) => Some(*s1 as SignedWord - *s2 as SignedWord),
                Flavor::NaN => None,
            },
            Flavor::NaN => None,
        }
    }

    /// Reverses the sign of `self`.
    pub fn inv_sign(&mut self) {
        match &mut self.inner {
            Flavor::Value(v1) => v1.inv_sign(),
            Flavor::Inf(s) => self.inner = Flavor::Inf(s.invert()),
            Flavor::NaN => {}
        }
    }

    /// Returns `self` to the power of `d1`.
    pub fn pow(&self, d1: &Self, rm: RoundingMode, cc: &mut Consts) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d1.inner {
                    Flavor::Value(v2) => Self::result_to_ext(
                        v1.pow(v2, rm, cc),
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
                            Self::new(v1.get_mantissa_max_bit_len())
                        } else {
                            Self::from_u8(1, v1.get_mantissa_max_bit_len())
                        }
                    }
                    Flavor::NaN => NAN,
                }
            }
            Flavor::Inf(s1) => {
                match &d1.inner {
                    Flavor::Value(v2) => {
                        // inf ^ v2
                        if v2.is_zero() {
                            Self::from_u8(1, v2.get_mantissa_max_bit_len())
                        } else if v2.is_positive() {
                            if s1.is_negative() && v2.is_odd_int() {
                                // v2 is odd and has no fractional part.
                                INF_NEG
                            } else {
                                INF_POS
                            }
                        } else {
                            Self::new(v2.get_mantissa_max_bit_len())
                        }
                    }
                    Flavor::Inf(s2) => {
                        // inf^inf
                        if s2.is_positive() {
                            INF_POS
                        } else {
                            Self::new(1)
                        }
                    }
                    Flavor::NaN => NAN,
                }
            }
            Flavor::NaN => NAN,
        }
    }

    /// Returns `self` to the power of `i`.
    pub fn powi(&self, i: usize, p: usize, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => Self::result_to_ext(v1.powi(i, rm), false, true),
            Flavor::Inf(s1) => {
                // inf ^ v2
                if i == 0 {
                    Self::from_u8(1, p)
                } else if i > 0 {
                    if s1.is_negative() && i & 1 == 1 {
                        INF_NEG
                    } else {
                        INF_POS
                    }
                } else {
                    Self::new(p)
                }
            }
            Flavor::NaN => NAN,
        }
    }

    /// Returns the logarithm base `b` of a number.
    pub fn log(&self, b: &Self, rm: RoundingMode, cc: &mut Consts) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &b.inner {
                    Flavor::Value(v2) => Self::result_to_ext(v1.log(v2, rm, cc), false, true),
                    Flavor::Inf(s2) => {
                        // v1.log(inf)
                        if s2.is_positive() {
                            Self::new(v1.get_mantissa_max_bit_len())
                        } else {
                            NAN
                        }
                    }
                    Flavor::NaN => NAN,
                }
            }
            Flavor::Inf(s1) => {
                if *s1 == Sign::Neg {
                    // -inf.log(any)
                    NAN
                } else {
                    match &b.inner {
                        Flavor::Value(v2) => {
                            // +inf.log(v2)
                            if v2.get_exponent() <= 0 {
                                INF_NEG
                            } else {
                                INF_POS
                            }
                        }
                        Flavor::Inf(_) => NAN, // +inf.log(inf)
                        Flavor::NaN => NAN,
                    }
                }
            }
            Flavor::NaN => NAN,
        }
    }

    /// Returns true if `self` is positive.
    /// The function returns false if `self` is NaN.
    pub fn is_positive(&self) -> bool {
        match &self.inner {
            Flavor::Value(v) => v.is_positive(),
            Flavor::Inf(s) => *s == Sign::Pos,
            Flavor::NaN => false,
        }
    }

    /// Returns true if `self` is negative.
    /// The function returns false if `self` is NaN.
    pub fn is_negative(&self) -> bool {
        match &self.inner {
            Flavor::Value(v) => v.is_negative(),
            Flavor::Inf(s) => *s == Sign::Neg,
            Flavor::NaN => false,
        }
    }

    /// Returns true if `self` is subnormal.
    /// A number is considered subnormal if not all digits of the mantissa are used, and the exponent has the minimum possible value.
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
            Flavor::NaN => false,
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
    /// # Examples
    ///
    /// ```
    /// use astro_float::BigFloat;
    /// use astro_float::Radix;
    /// use astro_float::RoundingMode;
    ///
    /// let n = BigFloat::parse("0.0", Radix::Bin, 64, RoundingMode::ToEven).unwrap();
    /// assert!(n.is_zero());
    /// let n = BigFloat::parse("1.124e-24", Radix::Dec, 128, RoundingMode::ToEven).unwrap();
    /// assert!(n.sub(&BigFloat::from_f64(1.124e-24, 128), RoundingMode::ToEven).get_exponent() <= Some(-52 - 24));
    /// let n = BigFloat::parse("-Inf", Radix::Hex, 1, RoundingMode::None).unwrap();
    /// assert!(n.is_inf_neg());
    /// let n = BigFloat::parse("NaN", Radix::Oct, 2, RoundingMode::None).unwrap();
    /// assert!(n.is_nan());
    /// ```
    pub fn parse(s: &str, rdx: Radix, p: usize, rm: RoundingMode) -> Option<Self> {
        let ps = crate::parser::parse(s, rdx);

        if ps.is_valid() {
            if ps.is_inf() {
                if ps.sign() == Sign::Pos {
                    Some(INF_POS)
                } else {
                    Some(INF_NEG)
                }
            } else if ps.is_nan() {
                Some(NAN)
            } else {
                let (m, s, e) = ps.raw_parts();
                Some(Self::result_to_ext(
                    BigFloatNumber::convert_from_radix(s, m, e, rdx, p, rm),
                    false,
                    true,
                ))
            }
        } else {
            None
        }
    }

    pub(crate) fn write_str<T: Write>(
        &self,
        w: &mut T,
        rdx: Radix,
        rm: RoundingMode,
    ) -> Result<(), core::fmt::Error> {
        match &self.inner {
            Flavor::Value(v) => {
                let s = match v.format(rdx, rm) {
                    Ok(s) => s,
                    Err(e) => String::from(match e {
                        Error::ExponentOverflow(s) => {
                            if s.is_positive() {
                                "Inf"
                            } else {
                                "-Inf"
                            }
                        }
                        Error::DivisionByZero => "Div by zero",
                        Error::InvalidArgument => "Invalid arg",
                        Error::MemoryAllocation(_) => panic!("Memory allocation"),
                    }),
                };
                w.write_str(&s)
            }
            Flavor::Inf(sign) => {
                let s = if sign.is_negative() { "-Inf" } else { "Inf" };
                w.write_str(s)
            }
            crate::ext::Flavor::NaN => w.write_str("NaN"),
        }
    }

    /// Returns a random normalized (not subnormal) BigFloat number with exponent in the range
    /// from `exp_from` to `exp_to` inclusive. The sign can be positive and negative. Zero is excluded.
    /// Function does not follow any specific distribution law.
    /// The intended use of this function is for testing.
    ///
    /// # Errors
    ///
    /// InvalidArgument - when `exp_from` is greater than `exp_to`.
    #[cfg(feature = "random")]
    pub fn random_normal(p: usize, exp_from: Exponent, exp_to: Exponent) -> Self {
        Self::result_to_ext(
            BigFloatNumber::random_normal(p, exp_from, exp_to),
            true,
            false,
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
            Flavor::NaN => FpCategory::Nan,
        }
    }

    /// Returns the arctangent of `self`. The result is an angle in radians ranging from -pi/2 to pi/2.
    pub fn atan(&self, rm: RoundingMode, p: usize, cc: &mut Consts) -> Self {
        match &self.inner {
            Flavor::Value(v) => Self::result_to_ext(v.atan(rm, cc), v.is_zero(), true),
            Flavor::Inf(s) => Self::result_to_ext(Self::half_pi(*s, p, rm, cc), false, true),
            Flavor::NaN => NAN,
        }
    }

    /// Returns the hyperbolic tangent of `self`.
    pub fn tanh(&self, rm: RoundingMode, p: usize, cc: &mut Consts) -> Self {
        match &self.inner {
            Flavor::Value(v) => Self::result_to_ext(v.atan(rm, cc), v.is_zero(), true),
            Flavor::Inf(s) => Self::from_i8(s.as_int(), p),
            Flavor::NaN => NAN,
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
                Error::MemoryAllocation(_) => panic!("Memory allocation for BigFloat failed"),
                Error::InvalidArgument => NAN,
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

    /// Returns the maximum value for the specified precision `p`: all bits of the mantissa are set to 1, the exponent has the maximum possible value, and the sign is positive. Precision is rounded upwards to the word size.
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

    /// Decomposes `self` into raw parts. The function returns a reference to a slice of words representing mantissa, numbers of significant bits in the mantissa, sign, and exponent.
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
    pub fn from_raw_parts(m: &[Word], n: usize, s: Sign, e: Exponent) -> Self {
        Self::result_to_ext(BigFloatNumber::from_raw_parts(m, n, s, e), false, true)
    }

    /// Returns sign of a number or None if `self` is NaN
    pub fn get_sign(&self) -> Option<Sign> {
        match &self.inner {
            Flavor::Value(v) => Some(v.get_sign()),
            Flavor::Inf(s) => Some(*s),
            Flavor::NaN => None,
        }
    }

    /// Sets the exponent of `self`.
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
    /// If `self` is Inf or NaN, the function has no effect.
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

    /// Computes the reciprocal of a number. The result is rounded using the rounding mode `rm`.
    pub fn reciprocal(&self, p: usize, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v) => Self::result_to_ext(v.reciprocal(rm), v.is_zero(), true),
            Flavor::Inf(s) => {
                let mut ret = Self::new(p);
                ret.set_sign(*s);
                ret
            }
            Flavor::NaN => NAN,
        }
    }

    /// Sets the sign of `self`.
    pub fn set_sign(&mut self, s: Sign) {
        match &mut self.inner {
            Flavor::Value(v) => v.set_sign(s),
            Flavor::Inf(_) => self.inner = Flavor::Inf(s),
            Flavor::NaN => {}
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
            Flavor::NaN => NAN,
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
                Flavor::NaN => NAN,
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
                Flavor::NaN => NAN,
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
                Flavor::NaN => NAN,
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
    gen_wrapper_arg_rm!("Returns a rounded number with `n` decimal positions in the fractional part of the number using the rounding mode `rm`.", 
        round,
        Self,
        { INF_POS },
        { INF_NEG },
        n,
        usize
    );
    gen_wrapper_arg_rm!(
        "Returns the square root of `self`.",
        sqrt,
        Self,
        { INF_POS },
        { NAN },
    );
    gen_wrapper_arg_rm!(
        "Returns the cube root of `self`.",
        cbrt,
        Self,
        { INF_POS },
        { INF_NEG },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the natural logarithm of `self`.",
        ln,
        Self,
        { INF_POS },
        { NAN },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the logarithm base 2 of `self`.",
        log2,
        Self,
        { INF_POS },
        { NAN },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the logarithm base 10 of `self`.",
        log10,
        Self,
        { INF_POS },
        { NAN },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns `e` to the power of `self`.",
        exp,
        Self,
        { INF_POS },
        { INF_NEG },
    );

    gen_wrapper_arg_rm_cc!(
        "Returns the sine of `self`. The function takes an angle in radians as an argument.",
        sin,
        Self,
        { NAN },
        { NAN },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the cosine of `self`. The function takes an angle in radians as an argument.",
        cos,
        Self,
        { NAN },
        { NAN },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the tangent of `self`. The function takes an angle in radians as an argument.",
        tan,
        Self,
        { NAN },
        { NAN },
    );
    gen_wrapper_arg_rm_cc!("Returns the arcsine of `self`. The result is an angle in radians ranging from -pi/2 to pi/2.", 
        asin,
        Self,
        {NAN},
        {NAN},
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the arccosine of `self`. The result is an angle in radians ranging from 0 to pi.",
        acos,
        Self,
        { NAN },
        { NAN },
    );

    gen_wrapper_arg_rm!(
        "Returns the hyperbolic sine of `self`.",
        sinh,
        Self,
        { INF_POS },
        { INF_NEG },
    );
    gen_wrapper_arg_rm!(
        "Returns the hyperbolic cosine of `self`.",
        cosh,
        Self,
        { INF_POS },
        { INF_POS },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the inverse hyperbolic sine of `self`.",
        asinh,
        Self,
        { INF_POS },
        { INF_NEG },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the inverse hyperbolic cosine of `self`.",
        acosh,
        Self,
        { BigFloat::new(1) },
        { BigFloat::new(1) },
    );
    gen_wrapper_arg_rm_cc!(
        "Returns the inverse hyperbolic tangent of `self`.",
        atanh,
        Self,
        { BigFloat::new(1) },
        { BigFloat::new(1) },
    );
}

macro_rules! impl_int_conv {
    ($s:ty, $from_s:ident) => {
        impl BigFloat {
            /// Construct BigFloat from an integer value.
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

    use crate::ctx::with_value;
    use crate::ctx::Context;
    use crate::defs::DEFAULT_P;
    use crate::defs::DEFAULT_RM;
    use crate::BigFloat;
    use crate::Radix;
    use crate::NAN;

    use core::{
        cmp::Eq, cmp::Ordering, cmp::PartialEq, cmp::PartialOrd, fmt::Display, fmt::Formatter,
        iter::Product, iter::Sum, ops::Add, ops::Div, ops::Mul, ops::Neg, ops::Rem, ops::Sub,
        str::FromStr,
    };

    //
    // ops traits
    //

    macro_rules! impl_binary_op {
        ($t:ident, $f:ident, $a:ty, $b:ty) => {
            impl $t<$b> for $a {
                type Output = Context;
                fn $f(self, rhs: $b) -> Self::Output {
                    with_value(BigFloat::$f(&self, &rhs, DEFAULT_RM))
                }
            }
        };
    }

    macro_rules! impl_binary_op_ctx {
        ($t:ident, $f:ident, $a:ty, $b:ty) => {
            impl $t<$b> for $a {
                type Output = Context;
                fn $f(self, rhs: $b) -> Self::Output {
                    with_value(BigFloat::$f(&self, &rhs.get_value(), DEFAULT_RM))
                }
            }
        };
    }

    impl_binary_op!(Add, add, BigFloat, BigFloat);
    impl_binary_op!(Add, add, BigFloat, &BigFloat);
    impl_binary_op!(Add, add, &BigFloat, &BigFloat);
    impl_binary_op!(Add, add, &BigFloat, BigFloat);

    impl_binary_op!(Sub, sub, BigFloat, BigFloat);
    impl_binary_op!(Sub, sub, BigFloat, &BigFloat);
    impl_binary_op!(Sub, sub, &BigFloat, &BigFloat);
    impl_binary_op!(Sub, sub, &BigFloat, BigFloat);

    impl_binary_op!(Mul, mul, BigFloat, BigFloat);
    impl_binary_op!(Mul, mul, BigFloat, &BigFloat);
    impl_binary_op!(Mul, mul, &BigFloat, &BigFloat);
    impl_binary_op!(Mul, mul, &BigFloat, BigFloat);

    impl_binary_op!(Div, div, BigFloat, BigFloat);
    impl_binary_op!(Div, div, BigFloat, &BigFloat);
    impl_binary_op!(Div, div, &BigFloat, &BigFloat);
    impl_binary_op!(Div, div, &BigFloat, BigFloat);

    impl_binary_op!(Rem, rem, BigFloat, BigFloat);
    impl_binary_op!(Rem, rem, BigFloat, &BigFloat);
    impl_binary_op!(Rem, rem, &BigFloat, &BigFloat);
    impl_binary_op!(Rem, rem, &BigFloat, BigFloat);

    impl_binary_op_ctx!(Add, add, BigFloat, Context);
    impl_binary_op_ctx!(Add, add, BigFloat, &Context);
    impl_binary_op_ctx!(Add, add, &BigFloat, &Context);
    impl_binary_op_ctx!(Add, add, &BigFloat, Context);

    impl_binary_op_ctx!(Sub, sub, BigFloat, Context);
    impl_binary_op_ctx!(Sub, sub, BigFloat, &Context);
    impl_binary_op_ctx!(Sub, sub, &BigFloat, &Context);
    impl_binary_op_ctx!(Sub, sub, &BigFloat, Context);

    impl_binary_op_ctx!(Mul, mul, BigFloat, Context);
    impl_binary_op_ctx!(Mul, mul, BigFloat, &Context);
    impl_binary_op_ctx!(Mul, mul, &BigFloat, &Context);
    impl_binary_op_ctx!(Mul, mul, &BigFloat, Context);

    impl_binary_op_ctx!(Div, div, BigFloat, Context);
    impl_binary_op_ctx!(Div, div, BigFloat, &Context);
    impl_binary_op_ctx!(Div, div, &BigFloat, &Context);
    impl_binary_op_ctx!(Div, div, &BigFloat, Context);

    impl_binary_op_ctx!(Rem, rem, BigFloat, Context);
    impl_binary_op_ctx!(Rem, rem, BigFloat, &Context);
    impl_binary_op_ctx!(Rem, rem, &BigFloat, &Context);
    impl_binary_op_ctx!(Rem, rem, &BigFloat, Context);

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

    impl From<f64> for BigFloat {
        fn from(f: f64) -> Self {
            BigFloat::from_f64(f, DEFAULT_P)
        }
    }

    impl From<f32> for BigFloat {
        fn from(f: f32) -> Self {
            BigFloat::from_f32(f, DEFAULT_P)
        }
    }

    impl Display for BigFloat {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
            self.write_str(f, Radix::Dec, DEFAULT_RM)
        }
    }

    impl Default for BigFloat {
        fn default() -> BigFloat {
            BigFloat::new(DEFAULT_P)
        }
    }

    impl FromStr for BigFloat {
        type Err = BigFloat;

        /// Returns parsed number or NAN in case of error.
        fn from_str(src: &str) -> Result<BigFloat, Self::Err> {
            BigFloat::parse(src, Radix::Dec, DEFAULT_P, DEFAULT_RM).ok_or(NAN)
        }
    }

    impl Product for BigFloat {
        fn product<I: Iterator<Item = BigFloat>>(iter: I) -> Self {
            Context::product(iter).get_value()
        }
    }

    impl Sum for BigFloat {
        fn sum<I: Iterator<Item = BigFloat>>(iter: I) -> Self {
            Context::sum(iter).get_value()
        }
    }

    impl<'a> Product<&'a BigFloat> for BigFloat {
        fn product<I: Iterator<Item = &'a BigFloat>>(iter: I) -> Self {
            Context::product(iter).get_value()
        }
    }

    impl<'a> Sum<&'a BigFloat> for BigFloat {
        fn sum<I: Iterator<Item = &'a BigFloat>>(iter: I) -> Self {
            Context::sum(iter).get_value()
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::RoundingMode;

    #[cfg(feature = "std")]
    use std::str::FromStr;

    #[cfg(not(feature = "std"))]
    use core::str::FromStr;

    #[cfg(not(feature = "std"))]
    use alloc::format;

    #[inline]
    fn rand_p() -> usize {
        rand::random::<usize>() % 1000 + DEFAULT_P
    }

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

        let mut d1 = d1.div(&BigFloat::new(rand_p()), rm);
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

        let d1 = BigFloat::new(rand_p()).div(&BigFloat::new(rand_p()), rm);
        assert!(!d1.is_inf());
        assert!(d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.get_sign().is_none());

        for _ in 0..1000 {
            let i = rand::random::<i64>();
            let d1 = BigFloat::from_i64(i, rand_p());
            let n1 = BigFloat::parse(&format!("{}", i), Radix::Dec, rand_p(), rm).unwrap();
            assert!(d1.cmp(&n1) == Some(0));

            let i = rand::random::<u64>();
            let d1 = BigFloat::from_u64(i, rand_p());
            let n1 = BigFloat::parse(&format!("{}", i), Radix::Dec, rand_p(), rm).unwrap();
            assert!(d1.cmp(&n1) == Some(0));

            let i = rand::random::<i128>();
            let d1 = BigFloat::from_i128(i, rand_p());
            let n1 = BigFloat::parse(&format!("{}", i), Radix::Dec, rand_p(), rm).unwrap();
            assert!(d1.cmp(&n1) == Some(0));

            let i = rand::random::<u128>();
            let d1 = BigFloat::from_u128(i, rand_p());
            let n1 = BigFloat::parse(&format!("{}", i), Radix::Dec, rand_p(), rm).unwrap();
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

        assert!(ONE.add(&ONE, rm).cmp(&TWO) == Some(0));
        assert!(ONE.add(&INF_POS, rm).is_inf_pos());
        assert!(INF_POS.add(&ONE, rm).is_inf_pos());
        assert!(ONE.add(&INF_NEG, rm).is_inf_neg());
        assert!(INF_NEG.add(&ONE, rm).is_inf_neg());
        assert!(INF_POS.add(&INF_POS, rm).is_inf_pos());
        assert!(INF_POS.add(&INF_NEG, rm).is_nan());
        assert!(INF_NEG.add(&INF_NEG, rm).is_inf_neg());
        assert!(INF_NEG.add(&INF_POS, rm).is_nan());

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

        assert!(TWO.sub(&ONE, rm).cmp(&ONE) == Some(0));
        assert!(ONE.sub(&INF_POS, rm).is_inf_neg());
        assert!(INF_POS.sub(&ONE, rm).is_inf_pos());
        assert!(ONE.sub(&INF_NEG, rm).is_inf_pos());
        assert!(INF_NEG.sub(&ONE, rm).is_inf_neg());
        assert!(INF_POS.sub(&INF_POS, rm).is_nan());
        assert!(INF_POS.sub(&INF_NEG, rm).is_inf_pos());
        assert!(INF_NEG.sub(&INF_NEG, rm).is_nan());
        assert!(INF_NEG.sub(&INF_POS, rm).is_inf_neg());

        assert!(TWO.mul(&ONE, rm).cmp(&TWO) == Some(0));
        assert!(ONE.mul(&INF_POS, rm).is_inf_pos());
        assert!(INF_POS.mul(&ONE, rm).is_inf_pos());
        assert!(ONE.mul(&INF_NEG, rm).is_inf_neg());
        assert!(INF_NEG.mul(&ONE, rm).is_inf_neg());
        assert!(ONE.neg().mul(&INF_POS, rm).is_inf_neg());
        assert!(ONE.neg().mul(&INF_NEG, rm).is_inf_pos());
        assert!(INF_POS.mul(&ONE.neg(), rm).is_inf_neg());
        assert!(INF_NEG.mul(&ONE.neg(), rm).is_inf_pos());
        assert!(INF_POS.mul(&INF_POS, rm).is_inf_pos());
        assert!(INF_POS.mul(&INF_NEG, rm).is_inf_neg());
        assert!(INF_NEG.mul(&INF_NEG, rm).is_inf_pos());
        assert!(INF_NEG.mul(&INF_POS, rm).is_inf_neg());
        assert!(INF_POS.mul(&BigFloat::new(rand_p()), rm).is_nan());
        assert!(INF_NEG.mul(&BigFloat::new(rand_p()), rm).is_nan());
        assert!(BigFloat::new(rand_p()).mul(&INF_POS, rm).is_nan());
        assert!(BigFloat::new(rand_p()).mul(&INF_NEG, rm).is_nan());

        assert!(TWO.div(&TWO, rm).cmp(&ONE) == Some(0));
        assert!(TWO.div(&INF_POS, rm).is_zero());
        assert!(INF_POS.div(&TWO, rm).is_inf_pos());
        assert!(TWO.div(&INF_NEG, rm).is_zero());
        assert!(INF_NEG.div(&TWO, rm).is_inf_neg());
        assert!(TWO.neg().div(&INF_POS, rm).is_zero());
        assert!(TWO.neg().div(&INF_NEG, rm).is_zero());
        assert!(INF_POS.div(&TWO.neg(), rm).is_inf_neg());
        assert!(INF_NEG.div(&TWO.neg(), rm).is_inf_pos());
        assert!(INF_POS.div(&INF_POS, rm).is_nan());
        assert!(INF_POS.div(&INF_NEG, rm).is_nan());
        assert!(INF_NEG.div(&INF_NEG, rm).is_nan());
        assert!(INF_NEG.div(&INF_POS, rm).is_nan());
        assert!(INF_POS.div(&BigFloat::new(rand_p()), rm).is_inf_pos());
        assert!(INF_NEG.div(&BigFloat::new(rand_p()), rm).is_inf_neg());
        assert!(BigFloat::new(rand_p()).div(&INF_POS, rm).is_zero());
        assert!(BigFloat::new(rand_p()).div(&INF_NEG, rm).is_zero());

        assert!(TWO.rem(&TWO, rm).is_zero());
        assert!(TWO.rem(&INF_POS, rm).cmp(&TWO) == Some(0));
        assert!(INF_POS.rem(&TWO, rm).is_nan());
        assert!(TWO.rem(&INF_NEG, rm).cmp(&TWO) == Some(0));
        assert!(INF_NEG.rem(&TWO, rm).is_nan());
        assert!(TWO.neg().rem(&INF_POS, rm).cmp(&TWO.neg()) == Some(0));
        assert!(TWO.neg().rem(&INF_NEG, rm).cmp(&TWO.neg()) == Some(0));
        assert!(INF_POS.rem(&TWO.neg(), rm).is_nan());
        assert!(INF_NEG.rem(&TWO.neg(), rm).is_nan());
        assert!(INF_POS.rem(&INF_POS, rm).is_nan());
        assert!(INF_POS.rem(&INF_NEG, rm).is_nan());
        assert!(INF_NEG.rem(&INF_NEG, rm).is_nan());
        assert!(INF_NEG.rem(&INF_POS, rm).is_nan());
        assert!(INF_POS.rem(&BigFloat::new(rand_p()), rm).is_nan());
        assert!(INF_NEG.rem(&BigFloat::new(rand_p()), rm).is_nan());
        assert!(BigFloat::new(rand_p()).rem(&INF_POS, rm).is_zero());
        assert!(BigFloat::new(rand_p()).rem(&INF_NEG, rm).is_zero());

        for op in [BigFloat::add, BigFloat::sub, BigFloat::mul, BigFloat::div, BigFloat::rem] {
            assert!(op(&NAN, &ONE, rm).is_nan());
            assert!(op(&ONE, &NAN, rm).is_nan());
            assert!(op(&NAN, &INF_POS, rm).is_nan());
            assert!(op(&INF_POS, &NAN, rm).is_nan());
            assert!(op(&NAN, &INF_NEG, rm).is_nan());
            assert!(op(&INF_NEG, &NAN, rm).is_nan());
            assert!(op(&NAN, &NAN, rm).is_nan());
        }

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
        assert!(ONE.cmp(&NAN).is_none());
        assert!(NAN.cmp(&ONE).is_none());
        assert!(INF_POS.cmp(&NAN).is_none());
        assert!(NAN.cmp(&INF_POS).is_none());
        assert!(INF_NEG.cmp(&NAN).is_none());
        assert!(NAN.cmp(&INF_NEG).is_none());
        assert!(NAN.cmp(&NAN).is_none());

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

        assert!(ONE.pow(&ONE, rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(BigFloat::new(DEFAULT_P)
            .pow(&INF_POS, rm, &mut cc)
            .is_zero());
        assert!(BigFloat::new(DEFAULT_P)
            .pow(&INF_NEG, rm, &mut cc)
            .is_zero());
        assert!(ONE.pow(&INF_POS, rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(ONE.pow(&INF_NEG, rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(TWO.pow(&INF_POS, rm, &mut cc).is_inf_pos());
        assert!(TWO.pow(&INF_NEG, rm, &mut cc).is_inf_neg());
        assert!(INF_POS.pow(&ONE, rm, &mut cc).is_inf_pos());
        assert!(INF_NEG.pow(&ONE, rm, &mut cc).is_inf_neg());
        assert!(INF_NEG.pow(&TWO, rm, &mut cc).is_inf_pos());
        assert!(INF_NEG
            .pow(&BigFloat::from_f64(10.2, DEFAULT_P), rm, &mut cc)
            .is_inf_pos());
        assert!(INF_NEG
            .pow(&BigFloat::from_f64(3.0, DEFAULT_P), rm, &mut cc)
            .is_inf_neg());
        assert!(INF_POS.pow(&ONE.neg(), rm, &mut cc).is_zero());
        assert!(INF_NEG.pow(&ONE.neg(), rm, &mut cc).is_zero());
        assert!(
            INF_POS
                .pow(&BigFloat::new(DEFAULT_P), rm, &mut cc)
                .cmp(&ONE)
                == Some(0)
        );
        assert!(
            INF_NEG
                .pow(&BigFloat::new(DEFAULT_P), rm, &mut cc)
                .cmp(&ONE)
                == Some(0)
        );
        assert!(INF_POS.pow(&INF_POS, rm, &mut cc).is_inf_pos());
        assert!(INF_NEG.pow(&INF_POS, rm, &mut cc).is_inf_pos());
        assert!(INF_POS.pow(&INF_NEG, rm, &mut cc).is_zero());
        assert!(INF_NEG.pow(&INF_NEG, rm, &mut cc).is_zero());

        let half = ONE.div(&TWO, rm);
        assert!(TWO.log(&TWO, rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(TWO.log(&INF_POS, rm, &mut cc).is_zero());
        assert!(TWO.log(&INF_NEG, rm, &mut cc).is_nan());
        assert!(INF_POS.log(&TWO, rm, &mut cc).is_inf_pos());
        assert!(INF_NEG.log(&TWO, rm, &mut cc).is_nan());
        assert!(half.log(&half, rm, &mut cc).cmp(&ONE) == Some(0));
        assert!(half.log(&INF_POS, rm, &mut cc).is_zero());
        assert!(half.log(&INF_NEG, rm, &mut cc).is_nan());
        assert!(INF_POS.log(&half, rm, &mut cc).is_inf_neg());
        assert!(INF_NEG.log(&half, rm, &mut cc).is_nan());
        assert!(INF_POS.log(&INF_POS, rm, &mut cc).is_nan());
        assert!(INF_POS.log(&INF_NEG, rm, &mut cc).is_nan());
        assert!(INF_NEG.log(&INF_POS, rm, &mut cc).is_nan());
        assert!(INF_NEG.log(&INF_NEG, rm, &mut cc).is_nan());
        assert!(TWO.log(&ONE, rm, &mut cc).is_inf_pos());
        assert!(half.log(&ONE, rm, &mut cc).is_inf_pos());
        assert!(ONE.log(&ONE, rm, &mut cc).is_nan());

        assert!(BigFloat::from_f32(f32::NAN, DEFAULT_P).is_nan());
        assert!(BigFloat::from_f32(f32::INFINITY, DEFAULT_P).is_inf_pos());
        assert!(BigFloat::from_f32(f32::NEG_INFINITY, DEFAULT_P).is_inf_neg());
        assert!(!BigFloat::from_f32(1.0, DEFAULT_P).is_nan());
        assert!(BigFloat::from_f64(f64::NAN, DEFAULT_P).is_nan());
        assert!(BigFloat::from_f64(f64::INFINITY, DEFAULT_P).is_inf_pos());
        assert!(BigFloat::from_f64(f64::NEG_INFINITY, DEFAULT_P).is_inf_neg());
        assert!(!BigFloat::from_f64(1.0, DEFAULT_P).is_nan());

        assert!(ONE.pow(&NAN, rm, &mut cc).is_nan());
        assert!(NAN.pow(&ONE, rm, &mut cc).is_nan());
        assert!(INF_POS.pow(&NAN, rm, &mut cc).is_nan());
        assert!(NAN.pow(&INF_POS, rm, &mut cc).is_nan());
        assert!(INF_NEG.pow(&NAN, rm, &mut cc).is_nan());
        assert!(NAN.pow(&INF_NEG, rm, &mut cc).is_nan());
        assert!(NAN.pow(&NAN, rm, &mut cc).is_nan());

        assert!(NAN.powi(2, rand_p(), rm).is_nan());
        assert!(NAN.powi(0, rand_p(), rm).is_nan());
        assert!(INF_POS.powi(2, rand_p(), rm).is_inf_pos());
        assert!(INF_POS.powi(3, rand_p(), rm).is_inf_pos());
        assert!(INF_NEG.powi(4, rand_p(), rm).is_inf_pos());
        assert!(INF_NEG.powi(5, rand_p(), rm).is_inf_neg());
        assert!(INF_POS.powi(0, rand_p(), rm).cmp(&ONE) == Some(0));
        assert!(INF_NEG.powi(0, rand_p(), rm).cmp(&ONE) == Some(0));

        assert!(TWO.log(&NAN, rm, &mut cc).is_nan());
        assert!(NAN.log(&TWO, rm, &mut cc).is_nan());
        assert!(INF_POS.log(&NAN, rm, &mut cc).is_nan());
        assert!(NAN.log(&INF_POS, rm, &mut cc).is_nan());
        assert!(INF_NEG.log(&NAN, rm, &mut cc).is_nan());
        assert!(NAN.log(&INF_NEG, rm, &mut cc).is_nan());
        assert!(NAN.log(&NAN, rm, &mut cc).is_nan());

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

        assert!(INF_NEG.sqrt(rm).is_nan());
        assert!(INF_POS.sqrt(rm).is_inf_pos());
        assert!(NAN.sqrt(rm).is_nan());

        assert!(INF_NEG.cbrt(rm).is_inf_neg());
        assert!(INF_POS.cbrt(rm).is_inf_pos());
        assert!(NAN.cbrt(rm).is_nan());

        for op in [BigFloat::ln, BigFloat::log2, BigFloat::log10] {
            assert!(op(&INF_NEG, rm, &mut cc).is_nan());
            assert!(op(&INF_POS, rm, &mut cc).is_inf_pos());
            assert!(op(&NAN, rm, &mut cc).is_nan());
        }

        assert!(INF_NEG.exp(rm, &mut cc).is_inf_neg());
        assert!(INF_POS.exp(rm, &mut cc).is_inf_pos());
        assert!(NAN.exp(rm, &mut cc).is_nan());

        assert!(INF_NEG.sin(rm, &mut cc).is_nan());
        assert!(INF_POS.sin(rm, &mut cc).is_nan());
        assert!(NAN.sin(rm, &mut cc).is_nan());

        assert!(INF_NEG.cos(rm, &mut cc).is_nan());
        assert!(INF_POS.cos(rm, &mut cc).is_nan());
        assert!(NAN.cos(rm, &mut cc).is_nan());

        assert!(INF_NEG.tan(rm, &mut cc).is_nan());
        assert!(INF_POS.tan(rm, &mut cc).is_nan());
        assert!(NAN.tan(rm, &mut cc).is_nan());

        assert!(INF_NEG.asin(rm, &mut cc).is_nan());
        assert!(INF_POS.asin(rm, &mut cc).is_nan());
        assert!(NAN.asin(rm, &mut cc).is_nan());

        assert!(INF_NEG.acos(rm, &mut cc).is_nan());
        assert!(INF_POS.acos(rm, &mut cc).is_nan());
        assert!(NAN.acos(rm, &mut cc).is_nan());

        let p = rand_p();
        let mut half_pi: BigFloat = cc.pi(p, rm).unwrap().into();
        half_pi.set_exponent(1);
        assert!(INF_NEG.atan(rm, p, &mut cc).cmp(&half_pi.neg()) == Some(0));
        assert!(INF_POS.atan(rm, p, &mut cc).cmp(&half_pi) == Some(0));
        assert!(NAN.atan(rm, rand_p(), &mut cc).is_nan());

        assert!(INF_NEG.sinh(rm).is_inf_neg());
        assert!(INF_POS.sinh(rm).is_inf_pos());
        assert!(NAN.sinh(rm).is_nan());

        assert!(INF_NEG.cosh(rm).is_inf_pos());
        assert!(INF_POS.cosh(rm).is_inf_pos());
        assert!(NAN.cosh(rm).is_nan());

        assert!(INF_NEG.tanh(rm, rand_p(), &mut cc).cmp(&ONE.neg()) == Some(0));
        assert!(INF_POS.tanh(rm, rand_p(), &mut cc).cmp(&ONE) == Some(0));
        assert!(NAN.tanh(rm, rand_p(), &mut cc).is_nan());

        assert!(INF_NEG.asinh(rm, &mut cc).is_inf_neg());
        assert!(INF_POS.asinh(rm, &mut cc).is_inf_pos());
        assert!(NAN.asinh(rm, &mut cc).is_nan());

        assert!(INF_NEG.acosh(rm, &mut cc).is_zero());
        assert!(INF_POS.acosh(rm, &mut cc).is_zero());
        assert!(NAN.acosh(rm, &mut cc).is_nan());

        assert!(INF_NEG.atanh(rm, &mut cc).is_zero());
        assert!(INF_POS.atanh(rm, &mut cc).is_zero());
        assert!(NAN.atanh(rm, &mut cc).is_nan());

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
    }

    #[test]
    pub fn test_ops() {
        let d1 = ONE.clone();
        let d2 = BigFloat::new(rand_p());
        assert!(d1.clone() - d2.clone() == d1);
        assert!(d1.clone() + d2 == d1);
        let d3 = TWO.clone();
        assert!(TWO.clone() == d3);
        assert!(ONE.clone() < d3);
        assert!(ONE.clone() == (d3.clone() / d3.clone()).get_value());

        assert!(d3.is_positive());
        let d1 = -d3;
        assert!(d1.is_negative());

        let d1 = ONE.clone();
        let d2 = BigFloat::new(rand_p());
        assert!(&d1 - &d2 == d1);
        assert!(&d1 + &d2 == d1);
        let d3 = TWO.clone();
        assert!(ONE.clone() == (d3.clone() / &d3).get_value());

        let d1 = -&(TWO.clone());
        assert!(d1.is_negative());

        let d1 = BigFloat::parse(
            "0.0123456789012345678901234567890123456789",
            Radix::Dec,
            DEFAULT_P,
            RoundingMode::None,
        )
        .unwrap();

        let d1str = format!("{}", d1);
        assert_eq!(&d1str, "1.23456789012345678901234567890123456789e-2");
        assert!(BigFloat::from_str(&d1str).unwrap() == d1);

        let d1 = BigFloat::parse(
            "-123.4567890123456789012345678901234567895",
            Radix::Dec,
            DEFAULT_P,
            RoundingMode::None,
        )
        .unwrap();
        let d1str = format!("{}", d1);
        assert_eq!(&d1str, "-1.23456789012345678901234567890123456789153e+2");
        assert_eq!(BigFloat::from_str(&d1str).unwrap(), d1);

        let d1str = format!("{}", INF_POS);
        assert!(d1str == "Inf");

        let d1str = format!("{}", INF_NEG);
        assert!(d1str == "-Inf");

        let d1str = format!("{}", NAN);
        assert!(d1str == "NaN");

        assert!(BigFloat::from_str("abc").unwrap_err().is_nan());

        let arr = [TWO.clone(), ONE.clone(), TWO.clone()];
        assert!(arr.into_iter().product::<BigFloat>() == (TWO.clone() * TWO.clone()).get_value());
        let arr = [TWO.clone(), ONE.clone(), TWO.clone()];
        assert!(
            arr.into_iter().sum::<BigFloat>()
                == (TWO.clone() + ONE.clone() + TWO.clone()).get_value()
        );

        let p = DEFAULT_P;
        let rm = RoundingMode::ToEven;
        assert!(
            BigFloat::from_i8(-123, p) == BigFloat::parse("-1.23e+2", Radix::Dec, p, rm).unwrap()
        );
        assert!(
            BigFloat::from_u8(123, p) == BigFloat::parse("1.23e+2", Radix::Dec, p, rm).unwrap()
        );
        assert!(
            BigFloat::from_i16(-12312, p)
                == BigFloat::parse("-1.2312e+4", Radix::Dec, p, rm).unwrap()
        );
        assert!(
            BigFloat::from_u16(12312, p)
                == BigFloat::parse("1.2312e+4", Radix::Dec, p, rm).unwrap()
        );
        assert!(
            BigFloat::from_i32(-123456789, p)
                == BigFloat::parse("-1.23456789e+8", Radix::Dec, p, rm).unwrap()
        );
        assert!(
            BigFloat::from_u32(123456789, p)
                == BigFloat::parse("1.23456789e+8", Radix::Dec, p, rm).unwrap()
        );
        assert!(
            BigFloat::from_i64(-1234567890123456789, p)
                == BigFloat::parse("-1.234567890123456789e+18", Radix::Dec, p, rm).unwrap()
        );
        assert!(
            BigFloat::from_u64(1234567890123456789, p)
                == BigFloat::parse("1.234567890123456789e+18", Radix::Dec, p, rm).unwrap()
        );
        assert!(
            BigFloat::from_i128(-123456789012345678901234567890123456789, p)
                == BigFloat::parse(
                    "-1.23456789012345678901234567890123456789e+38",
                    Radix::Dec,
                    p,
                    rm
                )
                .unwrap()
        );
        assert!(
            BigFloat::from_u128(123456789012345678901234567890123456789, p)
                == BigFloat::parse(
                    "1.23456789012345678901234567890123456789e+38",
                    Radix::Dec,
                    p,
                    rm
                )
                .unwrap()
        );
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
