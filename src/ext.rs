//! BigFloat including finite numbers, `NaN`, and `Inf`. 

use crate::BigFloatNumber;
use crate::Consts;
use crate::Error;
use crate::Radix;
use crate::RoundingMode;
use crate::Sign;
use crate::common::consts::ONE;
use crate::defs::SignedWord;
use crate::defs::WORD_BIT_SIZE;
use core::num::FpCategory;
use core::fmt::Write;
use core::cell::RefCell;

pub const NAN: BigFloat = BigFloat {inner: Flavor::NaN };
pub const INF_POS: BigFloat = BigFloat {inner: Flavor::Inf(Sign::Pos) };
pub const INF_NEG: BigFloat = BigFloat {inner: Flavor::Inf(Sign::Neg) };

/// Global context contains default parameters for all operations.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct GlobalContext {
    pub precision: usize,
    pub rounding_mode: RoundingMode,
}

thread_local! {
    static CC: RefCell<Consts>  = RefCell::new(Consts::new().expect("Constant cache initialized"));
    static GCTX: RefCell<GlobalContext> = RefCell::new(GlobalContext {
        precision: WORD_BIT_SIZE * 2,
        rounding_mode: RoundingMode::ToEven,
    });
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
    Inf(Sign)         // signed Inf
}

impl BigFloat {

    /// Returns a new BigFloat with the value of zero and precision `p`.
    pub fn new(p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::new(p), false, true)
    }
 
    /// Creates a BigFloat from f64.
    /// The conversion is not guaranteed to be lossless since BigFloat and f64 have different bases.
    pub fn from_f64(f: f64, p: usize) -> Self {
        Self::result_to_ext(BigFloatNumber::from_f64(p, f), false, true)
    }

    /// Creates a BigFloat from f32.
    /// The conversion is not guaranteed to be lossless since BigFloat and f64 have different bases.
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
        match &self.inner {
            Flavor::Value(v1) => {
                match &d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.add(v2, rm), v1.is_zero(), v1.get_sign() == v2.get_sign())
                    },
                    Flavor::Inf(s2) => {
                        BigFloat { inner: Flavor::Inf(*s2) }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match &d2.inner {
                    Flavor::Value(_) => {
                        BigFloat { inner: Flavor::Inf(*s1) }
                    },
                    Flavor::Inf(s2) => {
                        if *s1 != *s2 {
                            NAN
                        } else {
                            BigFloat { inner: Flavor::Inf(*s2) }
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Subtracts `d2` from `self` and return the result of the subtraction.
    pub fn sub(&self, d2: &Self, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.sub(&v2, rm), v1.is_zero(), v1.get_sign() == v2.get_sign())
                    },
                    Flavor::Inf(s2) => {
                        if s2.is_positive() {
                            INF_NEG
                        } else {
                            INF_POS
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match &d2.inner {
                    Flavor::Value(_) => {
                        BigFloat { inner: Flavor::Inf(*s1) }
                    },
                    Flavor::Inf(s2) => {
                        if *s1 == *s2 {
                            NAN
                        } else {
                            BigFloat { inner: Flavor::Inf(*s1) }
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Multiplies `self` by `d2` and returns the result of the multiplication.
    pub fn mul(&self, d2: &Self, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.mul(&v2, rm), v1.is_zero(), v1.get_sign() == v2.get_sign())
                    },
                    Flavor::Inf(s2) => {
                        if v1.is_zero() { // 0*inf
                            NAN
                        } else {
                            let s = if v1.get_sign() == *s2 {
                                Sign::Pos
                            } else {
                                Sign::Neg
                            };
                            BigFloat { inner: Flavor::Inf(s) }
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match &d2.inner {
                    Flavor::Value(v2) => {
                        if v2.is_zero() { // inf*0
                            NAN
                        } else {
                            let s = if v2.get_sign() == *s1 {
                                Sign::Pos
                            } else {
                                Sign::Neg
                            };
                            BigFloat { inner: Flavor::Inf(s) }
                        }
                    },
                    Flavor::Inf(s2) => {
                        let s = if s1 == s2 {
                            Sign::Pos
                        } else {
                            Sign::Neg
                        };
                        BigFloat { inner: Flavor::Inf(s) }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Divides `self` by `d2` and returns the result of the division.
    pub fn div(&self, d2: &Self, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.div(&v2, rm), v1.is_zero(), v1.get_sign() == v2.get_sign())
                    },
                    Flavor::Inf(_) => {
                        Self::new(v1.get_mantissa_max_bit_len())
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match &d2.inner {
                    Flavor::Value(v) => {
                        if *s1 == v.get_sign() {
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

    /// Returns the remainder of division of `self` by `d1`.
    pub fn rem(&self, d2: &Self, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d2.inner {
                    Flavor::Value(v2) => {
                        Self::result_to_ext(v1.rem(&v2, rm), v1.is_zero(), v1.get_sign() == v2.get_sign())
                    },
                    Flavor::Inf(_) => {
                        Self::new(v1.get_mantissa_max_bit_len())
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match &d2.inner {
                    Flavor::Value(v) => {
                        if *s1 == v.get_sign() {
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

    /// Compares `self` to `d2`.
    /// Returns positive if `self` > `d2`, negative if `self` < `d2`, zero if `self` == `d2`, None if `self` or `d2` is NaN.
    pub fn cmp(&self, d2: &BigFloat) -> Option<SignedWord> {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d2.inner {
                    Flavor::Value(v2) => {
                        Some(v1.cmp(&v2))
                    }
                    Flavor::Inf(s2) => {
                        if *s2 == Sign::Pos {
                            Some(-1)
                        } else {
                            Some(1)
                        }
                    },
                    Flavor::NaN => None,
                }
            },
            Flavor::Inf(s1) => {
                match &d2.inner {
                    Flavor::Value(_) => {
                        Some(*s1 as SignedWord)
                    }
                    Flavor::Inf(s2) => {
                        Some(*s1 as SignedWord - *s2 as SignedWord)
                    },
                    Flavor::NaN => None,
                }
            },
            Flavor::NaN => None,
        }
    }

    /// Reverses the sign of `self`.
    pub fn inv_sign(&mut self) {
        match &mut self.inner {
            Flavor::Value(v1) => {
                v1.inv_sign()
            },
            Flavor::Inf(s) => self.inner = Flavor::Inf(s.invert()),
            Flavor::NaN => {},
        }
    }

    /// Returns `self` to the power of `d1`.
    pub fn pow(&self, d1: &Self, rm: RoundingMode) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &d1.inner {
                    Flavor::Value(v2) => {
                        CC.with(|cc| {
                            Self::result_to_ext(v1.pow(&v2, rm, &mut cc.borrow_mut()), v1.is_zero(), v1.get_sign() == v2.get_sign())
                        })
                    },
                    Flavor::Inf(s2) => {
                        // v1^inf
                        let val = v1.cmp(&ONE);
                        if val > 0 {
                            BigFloat { inner: Flavor::Inf(*s2) }
                        } else if val < 0 {
                            Self::new(v1.get_mantissa_max_bit_len())
                        } else {
                            Self::from_u8(1)
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::Inf(s1) => {
                match &d1.inner {
                    Flavor::Value(v2) => {
                        // inf ^ v2
                        if v2.is_zero() {
                            Self::from_u8(1)
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
                    },
                    Flavor::Inf(s2) => {
                        // inf^inf
                        if s2.is_positive() {
                            INF_POS
                        } else {
                            Self::new(1)
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
            Flavor::NaN => NAN,
        }
    }

    /// Returns the logarithm base `b` of a number.
    pub fn log(&self, b: &Self) -> Self {
        match &self.inner {
            Flavor::Value(v1) => {
                match &b.inner {
                    Flavor::Value(v2) => {
                        let rm = GCTX.with(|x| x.borrow().rounding_mode);
                        CC.with(|cc| {
                            Self::result_to_ext(v1.log(&v2, rm, &mut cc.borrow_mut()), false, true)
                        })
                    },
                    Flavor::Inf(s2) => {
                        // v1.log(inf)
                        if s2.is_positive() {
                            Self::new(v1.get_mantissa_max_bit_len())
                        } else {
                            NAN
                        }
                    },
                    Flavor::NaN => NAN,
                }
            },
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
                        },
                        Flavor::Inf(_) => NAN, // +inf.log(inf)
                        Flavor::NaN => NAN,
                    }
                }
            },
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
            return v.is_subnormal()
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
            NAN
        } else if self.cmp(min).unwrap() < 0 {
            min.clone()
        } else if self.cmp(max).unwrap() > 0 {
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
            let mut ret = Self::from_u8(1);
            ret.inv_sign();
            ret
        } else {
            Self::from_u8(1)
        }
    }


    /// Parses a number from the string `s`.
    /// The function expects `s` to be a number in scientific format in base 10, or +-Inf, or NaN.
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
                Some(Self::result_to_ext(BigFloatNumber::convert_from_radix(s, m, e, rdx, p, rm), false, true))
            }
        } else {
            None
        }
    }

    #[allow(dead_code)]
    pub(crate) fn write_str<T: Write>(&self, w: &mut T, rdx: Radix) -> Result<(), core::fmt::Error> {
        match &self.inner {
            Flavor::Value(v) => {
                let rm = GCTX.with(|x| x.borrow().rounding_mode);
                let s = v.format(rdx, rm).unwrap();
                w.write_str(&s)
            },
            Flavor::Inf(sign) => {
                let s = if sign.is_negative() {
                    "-Inf"
                } else {
                    "Inf"
                };
                w.write_str(s)
            },
            crate::ext::Flavor::NaN => {
                w.write_str("NaN")
            },
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
    #[cfg(feature = "rand")]
    pub fn random_normal(exp_from: i8, exp_to: i8) -> Result<Self, Error> {

        if exp_from > exp_to {
            return Err(Error::InvalidArgument);
        }

        // build mantissa
        let mut mantissa = [0i16; DECIMAL_PARTS];
        for v in mantissa.iter_mut() {
            *v = (random::<u16>() % crate::defs::DECIMAL_BASE as u16) as i16;
        }

        if mantissa[DECIMAL_PARTS - 1] == 0 {
            mantissa[DECIMAL_PARTS - 1] = (crate::defs::DECIMAL_BASE - 1) as i16;
        }

        while mantissa[DECIMAL_PARTS - 1] / 1000 == 0 {
            mantissa[DECIMAL_PARTS - 1] *= 10;
        }

        // sign & exponent
        let sign = if random::<i8>() & 1 == 0 { Sign::Pos } else { Sign::Neg };
        let exp_range = exp_to as i32 - exp_from  as i32;
        let exp = (if exp_range != 0 { random::<i32>().abs() % exp_range } else { 0 } + exp_from as i32) as i8;

        Ok(BigFloat::from_raw_parts(mantissa, DECIMAL_POSITIONS as i16, sign, exp))
    }

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
            },
            Flavor::Inf(_) => FpCategory::Infinite,
            Flavor::NaN => FpCategory::Nan,
        }
    }

    /// Returns the arctangent of `self`. The result is an angle in radians ranging from -pi/2 to pi/2.
    pub fn atan(&self, rm: RoundingMode, p: usize) -> Self {
        match &self.inner {
            Flavor::Value(v) => {
                CC.with(|cc| {
                    Self::result_to_ext(v.atan(rm, &mut cc.borrow_mut()), v.is_zero(), true)
                })
            },
            Flavor::Inf(s) => {
                Self::result_to_ext(Self::half_pi(*s, p, rm), false, true)
            }
            Flavor::NaN => NAN,
        }
    }

    fn half_pi(s: Sign, p: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {

        let mut half_pi = CC.with(|cc| {
            cc.borrow_mut().pi(p, rm)
        })?;

        half_pi.set_exponent(1);
        half_pi.set_sign(s);

        Ok(half_pi)
    }

    fn result_to_ext(res: Result<BigFloatNumber, Error>, is_dividend_zero: bool, is_same_sign: bool) -> BigFloat {
        match res {
            Err(e) => match e {
                Error::ExponentOverflow(s) => if s.is_positive() { INF_POS } else { INF_NEG },
                Error::DivisionByZero => {
                    if is_dividend_zero {
                        NAN
                    } else if is_same_sign {
                        INF_POS
                    } else {
                        INF_NEG
                    }
                },
                Error::MemoryAllocation(_) => panic!("Memory allocation for BigFloat failed"),
                Error::InvalidArgument => NAN,
            },
            Ok(v) => BigFloat {inner: Flavor::Value(v)},
        }
    }
}

impl Clone for BigFloat {

    fn clone(&self) -> Self {
        match &self.inner {
            Flavor::Value(v) => {
                Self::result_to_ext(v.clone(), false, true)
            },
            Flavor::Inf(s) => {
                if s.is_positive() { INF_POS } else { INF_NEG }
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
        pub fn $fname(&self$(,$arg: $arg_type)*, rm: RoundingMode) -> $ret {
            match &self.inner {
                Flavor::Value(v) => {
                    CC.with(|cc| {
                        Self::result_to_ext(v.$fname($($arg,)* rm, &mut cc.borrow_mut()), v.is_zero(), true)
                    })
                },
                Flavor::Inf(s) => if s.is_positive() $pos_inf else $neg_inf,
                Flavor::NaN => NAN,
            }
        }
    };
}


impl BigFloat {

    gen_wrapper_arg!("Returns the absolute value of `self`.", abs, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper_arg!("Returns the integer part of `self`.", int, Self, {NAN}, {NAN},);
    gen_wrapper_arg!("Returns the fractional part of `self`.", fract, Self, {NAN}, {NAN},);
    gen_wrapper_arg!("Returns the smallest integer greater than or equal to `self`.", ceil, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper_arg!("Returns the largest integer less than or equal to `self`.", floor, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper_arg_rm!("Returns a rounded number with `n` decimal positions in the fractional part of the number using the rounding mode `rm`.", round, Self, {INF_POS}, {INF_NEG}, n, usize);

    gen_wrapper_arg_rm!("Returns the square root of `self`.", sqrt, Self, {INF_POS}, {NAN},);
    gen_wrapper_arg_rm!("Returns the cube root of `self`.", cbrt, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper_arg_rm_cc!("Returns the natural logarithm of `self`.", ln, Self, {INF_POS}, {NAN},);
    gen_wrapper_arg_rm_cc!("Returns the logarithm base 2 of `self`.", log2, Self, {INF_POS}, {NAN},);
    gen_wrapper_arg_rm_cc!("Returns the logarithm base 10 of `self`.", log10, Self, {INF_POS}, {NAN},);
    gen_wrapper_arg_rm_cc!("Returns `e` to the power of `self`.", exp, Self, {INF_POS}, {INF_NEG},);

    gen_wrapper_arg_rm_cc!("Returns the sine of `self`. The function takes an angle in radians as an argument.", sin, Self, {NAN}, {NAN},);
    gen_wrapper_arg_rm_cc!("Returns the cosine of `self`. The function takes an angle in radians as an argument.", cos, Self, {NAN}, {NAN},);
    gen_wrapper_arg_rm_cc!("Returns the tangent of `self`. The function takes an angle in radians as an argument.", tan, Self, {NAN}, {NAN},);
    gen_wrapper_arg_rm_cc!("Returns the arcsine of `self`. The result is an angle in radians ranging from -pi/2 to pi/2.", asin, Self, {NAN}, {NAN},);
    gen_wrapper_arg_rm_cc!("Returns the arccosine of `self`. The result is an angle in radians ranging from 0 to pi.", acos, Self, {NAN}, {NAN},);

    gen_wrapper_arg_rm!("Returns the hyperbolic sine of `self`.", sinh, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper_arg_rm!("Returns the hyperbolic cosine of `self`.", cosh, Self, {INF_POS}, {INF_POS},);
    gen_wrapper_arg_rm_cc!("Returns the hyperbolic tangent of `self`.", tanh, Self, {BigFloat::from_u8(1)}, {BigFloat::from_i8(-1)},);
    gen_wrapper_arg_rm_cc!("Returns the inverse hyperbolic sine of `self`.", asinh, Self, {INF_POS}, {INF_NEG},);
    gen_wrapper_arg_rm_cc!("Returns the inverse hyperbolic cosine of `self`.", acosh, Self, {BigFloat::new(1)}, {BigFloat::new(1)},);
    gen_wrapper_arg_rm_cc!("Returns the inverse hyperbolic tangent of `self`.", atanh, Self, {BigFloat::new(1)}, {BigFloat::new(1)},);
}


macro_rules! impl_int_conv {
    ($s:ty, $from_s:ident) => {

        impl BigFloat {
            /// Construct BigFloat from integer value.
            pub fn $from_s(i: $s) -> Self {
                let p = GCTX.with(|x| x.borrow().precision);
                Self::result_to_ext(BigFloatNumber::$from_s(i, p), false, true)
            }
        }

        #[cfg(feature = "std")]
        impl From<$s> for BigFloat {
            fn from(i: $s) -> Self {
                BigFloat::$from_s(i)
            }
        }

        #[cfg(not(feature = "std"))]
        impl core::convert::From<$s> for BigFloat {
            fn from(i: $s) -> Self {
                BigFloat::$from_s(i)
            }
        }
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


/* 
/// Standard library features
pub mod ops {

    use crate::ONE;
    use crate::ZERO;
    use crate::NAN;
    use crate::BigFloat;

    #[cfg(feature = "std")]
    use std::{
        iter::Product,
        iter::Sum,
        ops::Add,
        ops::AddAssign,
        ops::Div,
        ops::DivAssign,
        ops::Mul,
        ops::MulAssign,
        ops::Neg,
        ops::Sub,
        ops::SubAssign,
        cmp::PartialEq,
        cmp::Eq,
        cmp::PartialOrd,
        cmp::Ordering,
        fmt::Display,
        fmt::Formatter,
        str::FromStr,
        ops::Rem
    };


    #[cfg(not(feature = "std"))]
    use core::{
        iter::Product,
        iter::Sum,
        ops::Add,
        ops::AddAssign,
        ops::Div,
        ops::DivAssign,
        ops::Mul,
        ops::MulAssign,
        ops::Neg,
        ops::Sub,
        ops::SubAssign,
        cmp::PartialEq,
        cmp::Eq,
        cmp::PartialOrd,
        cmp::Ordering,
        fmt::Display,
        fmt::Formatter,
        str::FromStr,
        ops::Rem
    };

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

    impl Rem for BigFloat {
        type Output = Self;
        fn rem(self, rhs: Self) -> Self::Output {
            BigFloat::rem(&self, &rhs)
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

    impl Neg for &BigFloat {
        type Output = BigFloat;
        fn neg(self) -> Self::Output {
            (*self).inv_sign()
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

        #[cfg(feature="std")]
        fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
            self.write_str(f)
        }

        #[cfg(not(feature="std"))]
        fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
            self.write_str(f)
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

#[cfg(test)]
mod tests {

    use crate::defs::{DECIMAL_PARTS, RoundingMode, I64_MAX, I64_MIN, U64_MAX, I128_MAX, I128_MIN, U128_MAX};
    use crate::ext::Flavor;
    use super::*;

    #[cfg(feature = "std")]
    use std::str::FromStr;

    #[cfg(not(feature = "std"))]
    use core::str::FromStr;

    #[test]
    fn test_ext() {

        // Inf & NaN
        let d1 = BigFloat::from_u8(1);
        assert!(!d1.is_inf());
        assert!(!d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.is_positive());

        let d1 = d1.div(&BigFloat::new());
        assert!(d1.is_inf());
        assert!(!d1.is_nan());
        assert!(d1.is_inf_pos());
        assert!(!d1.is_inf_neg());
        assert!(d1.is_positive());

        let d1 = d1.inv_sign();
        assert!(d1.is_inf());
        assert!(!d1.is_nan());
        assert!(!d1.is_inf_pos());
        assert!(d1.is_inf_neg());
        assert!(d1.is_negative());

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
        assert!(d1.to_i64() == Some(1));
        assert!(d1.to_u64() == Some(1));
        assert!(d1.to_i128() == Some(1));
        assert!(d1.to_u128() == Some(1));
        let d1 = BigFloat::new().div(&BigFloat::new());
        assert!(d1.to_f64().is_nan());
        assert!(d1.to_f32().is_nan());
        assert!(d1.to_i64().is_none());
        assert!(d1.to_u64().is_none());
        assert!(d1.to_i128().is_none());
        assert!(d1.to_u128().is_none());
        let d1 = ONE.div(&BigFloat::new());
        assert!(d1.to_f64().is_infinite());
        assert!(d1.to_f32().is_infinite());
        assert!(d1.to_f64().is_sign_positive());
        assert!(d1.to_f32().is_sign_positive());
        assert!(d1.to_i64().is_none());
        assert!(d1.to_u64().is_none());
        assert!(d1.to_i128().is_none());
        assert!(d1.to_u128().is_none());
        let d1 = d1.inv_sign();
        assert!(d1.to_f64().is_sign_negative());
        assert!(d1.to_f32().is_sign_negative());
        assert!(d1.to_f64().is_infinite());
        assert!(d1.to_f32().is_infinite());
        assert!(d1.to_i64().is_none());
        assert!(d1.to_u64().is_none());
        assert!(d1.to_i128().is_none());
        assert!(d1.to_u128().is_none());

        let d1 = BigFloat { inner: Flavor::Value(I64_MAX) };
        assert!(d1.to_i64() == Some(i64::MAX));
        assert!(d1.add(&ONE).to_i64() == None);
        let d1 = BigFloat { inner: Flavor::Value(I64_MIN) };
        assert!(d1.to_i64() == Some(i64::MIN));
        assert!(d1.sub(&ONE).to_i64() == None);
        let d1 = BigFloat { inner: Flavor::Value(U64_MAX) };
        assert!(d1.to_u64() == Some(u64::MAX));
        assert!(d1.add(&ONE).to_u64() == None);
        let d1 = BigFloat { inner: Flavor::Value(I128_MAX) };
        assert!(d1.to_i128() == Some(i128::MAX));
        assert!(d1.add(&ONE).to_i128() == None);
        let d1 = BigFloat { inner: Flavor::Value(I128_MIN) };
        assert!(d1.to_i128() == Some(i128::MIN));
        assert!(d1.sub(&ONE).to_i128() == None);
        let d1 = BigFloat { inner: Flavor::Value(U128_MAX) };
        assert!(d1.to_u128() == Some(u128::MAX));
        assert!(d1.add(&ONE).to_u128() == None);

        for _ in 0..1000 {
            let i = rand::random::<i64>();
            let d1 = BigFloat::from_i64(i);
            assert!(d1.to_i64() == Some(i));

            let i = rand::random::<u64>();
            let d1 = BigFloat::from_u64(i);
            assert!(d1.to_u64() == Some(i));

            let i = rand::random::<i128>();
            let d1 = BigFloat::from_i128(i);
            assert!(d1.to_i128() == Some(i));

            let i = rand::random::<u128>();
            let d1 = BigFloat::from_u128(i);
            assert!(d1.to_u128() == Some(i));
        }

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

        for rm in [RoundingMode::Up, RoundingMode::Down, RoundingMode::ToZero, 
                RoundingMode::FromZero, RoundingMode::ToEven, RoundingMode::ToOdd] {
            assert!(INF_NEG.round(0, rm).is_inf_neg());
            assert!(INF_POS.round(0, rm).is_inf_pos());
            assert!(NAN.round(0, rm).is_nan());
        }

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

    #[test]
    pub fn test_ops() {

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

        let d1 = -TWO;
        assert!(d1.is_negative());

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

        let d1 = -&TWO;
        assert!(d1.is_negative());

        let d1 = BigFloat::from_f64(0.0123456789);

        let mut buf = [0u8; 256];
        let wblen = fmt_to_str(&d1, &mut buf).len();
        let d1str = core::str::from_utf8(&buf[..wblen]).unwrap();
        assert_eq!(d1str, "1.234567890000000000000000000000000000000e-2");
        assert!(BigFloat::from_str(d1str).unwrap() == d1);

        let d1 = BigFloat::from_f64(-123.456789);
        let wblen = fmt_to_str(&d1, &mut buf).len();
        let d1str = core::str::from_utf8(&buf[..wblen]).unwrap();
        assert!(d1str == "-1.234567890000000000000000000000000000000e+2");
        assert!(BigFloat::from_str(d1str).unwrap() == d1);

        let wblen = fmt_to_str(&INF_POS, &mut buf).len();
        let d1str = core::str::from_utf8(&buf[..wblen]).unwrap();
        assert!(d1str == "Inf");

        let wblen = fmt_to_str(&INF_NEG, &mut buf).len();
        let d1str = core::str::from_utf8(&buf[..wblen]).unwrap();
        assert!(d1str == "-Inf");

        let wblen = fmt_to_str(&NAN, &mut buf).len();
        let d1str = core::str::from_utf8(&buf[..wblen]).unwrap();
        assert!(d1str == "NaN");

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

    fn fmt_to_str<'a>(f: &BigFloat, buf: &'a mut [u8]) -> WritableBuf<'a> {
        buf.fill(0);
        let mut strepr = WritableBuf::new(buf);
        write!(strepr, "{}", f).unwrap();
        strepr
    }
}


#[cfg(feature="serde")]
#[cfg(test)]
mod serde_tests {

    use super::*;

    #[test]
    fn test_serde() {

        let d1 = E;

        let json = serde_json::to_string(&d1).unwrap();

        assert_eq!("{\"inner\":{\"Value\":{\"sign\":1,\"e\":-39,\"n\":40,\"m\":[7757,6249,3526,7471,6028,2353,9045,2845,2818,2718]}}}", json);

        let json = "{
            \"inner\": {
                \"Value\": {
                    \"sign\": -1,
                    \"e\": -39,
                    \"n\": 40,
                    \"m\": [7757, 6249, 3526, 7471, 6028, 2353, 9045, 2845, 2818, 2718]
                }
            }
        }";

        let d1 = d1.inv_sign();
        let d2: BigFloat = serde_json::from_str(json).unwrap();

        assert!(d1.cmp(&d2).unwrap() == 0);
    }
}

#[cfg(feature="rand")]
#[cfg(test)]
mod rand_tests {

    use super::*;

    #[test]
    fn test_rand() {

        for _ in 0..1000 {

            let exp_from = rand::random::<i8>();
            let exp_shift = if DECIMAL_MAX_EXPONENT > exp_from {
                rand::random::<u8>() % (DECIMAL_MAX_EXPONENT as i16 - exp_from as i16) as u8
            } else {
                0
            };
            let exp_to = (exp_from as i16 + exp_shift as i16) as i8;

            let n = BigFloat::random_normal(exp_from, exp_to).unwrap();

            assert!(!n.is_subnormal());
            assert!(n.get_exponent() >= exp_from && n.get_exponent() <= exp_to);
        }
    }
}
 */