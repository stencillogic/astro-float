//! All operations on numbers are performed in some context.

use crate::defs::DEFAULT_P;
use crate::defs::DEFAULT_RM;
use crate::BigFloat;
use crate::Consts;
use crate::RoundingMode;
use core::cell::RefCell;

#[cfg(not(feature = "std"))]
use alloc::rc::Rc;

#[cfg(feature = "std")]
use std::rc::Rc;

/// Context contains default parameters for all operations.
#[derive(Clone)]
pub struct Context {
    cc: Rc<RefCell<Consts>>,
    p: usize,
    rm: RoundingMode,
    value: BigFloat,
}

impl Context {
    /// Create a new context with default parameters.
    ///
    /// ## Panics
    ///
    /// The function call panics if memory allocation failed.
    pub fn new() -> Self {
        Context {
            cc: Rc::new(RefCell::new(Consts::new().expect("Memory allocation"))),
            p: DEFAULT_P,
            rm: DEFAULT_RM,
            value: BigFloat::new(DEFAULT_P),
        }
    }

    /// Sets the precision of the context.
    pub fn precision(&mut self, p: usize) -> &mut Self {
        self.p = p;
        self
    }

    /// Sets the rounding mode of the context.
    pub fn rounding_mode(&mut self, rm: RoundingMode) -> &mut Self {
        self.rm = rm;
        self
    }

    /// Sets the constant cache of the context.
    pub fn constant_cache(&mut self, cc: Rc<RefCell<Consts>>) -> &mut Self {
        self.cc = cc;
        self
    }

    /// Sets the current value of the context.
    pub fn value(&mut self, value: BigFloat) -> &mut Self {
        self.value = value;
        self
    }

    /// Returns the precision of the context.
    pub fn get_precision(&self) -> usize {
        self.p
    }

    /// Returns the rounding mode of the context.
    pub fn get_rounding_mode(&self) -> RoundingMode {
        self.rm
    }

    /// Returns the constant cache of the context.
    pub fn get_consts(&self) -> Rc<RefCell<Consts>> {
        self.cc.clone()
    }

    /// Returns the current value of the context.
    pub fn get_value(&self) -> BigFloat {
        self.value.clone()
    }

    /// Returns `self` to the power of `n`.
    pub fn powi(&mut self, n: usize) -> &mut Self {
        let val = self.value.powi(n, self.p, self.rm);
        self.value(val);
        self
    }
}

macro_rules! impl_fun_rm {
    // unwrap error, function requires self as argument
    ($comment:literal, $fname:ident) => {
        #[doc=$comment]
        pub fn $fname(&mut self) -> &mut Self {
            let val = self.value.$fname(self.rm);
            self.value(val);
            self
        }
    };
}

macro_rules! impl_fun_rm_cc {
    // unwrap error, function requires self as argument
    ($comment:literal, $fname:ident) => {
        #[doc=$comment]
        pub fn $fname(&mut self) -> &mut Self {
            let val = self.value.$fname(self.rm, &mut self.cc.borrow_mut());
            self.value(val);
            self
        }
    };
}

macro_rules! impl_fun_arg_rm_cc {
    // unwrap error, function requires self as argument
    ($comment:literal, $fname:ident) => {
        #[doc=$comment]
        pub fn $fname(&mut self, arg: &BigFloat) -> &mut Self {
            let val = self.value.$fname(arg, self.rm, &mut self.cc.borrow_mut());
            self.value(val);
            self
        }
    };
}

macro_rules! impl_fun_rm_p_cc {
    // unwrap error, function requires self as argument
    ($comment:literal, $fname:ident) => {
        #[doc=$comment]
        pub fn $fname(&mut self) -> &mut Self {
            let val = self
                .value
                .$fname(self.rm, self.p, &mut self.cc.borrow_mut());
            self.value(val);
            self
        }
    };
}

impl Context {
    impl_fun_rm!("Returns the square root of a number.", sqrt);
    impl_fun_rm!("Returns the cube root of a number.", cbrt);
    impl_fun_rm_cc!("Returns the natural logarithm of a number.", ln);
    impl_fun_rm_cc!("Returns the exponent of a number.", exp);
    impl_fun_rm_cc!("Returns the logarithm base two of a number.", log2);
    impl_fun_rm_cc!("Returns the logarithm base ten of a number.", log10);
    impl_fun_arg_rm_cc!("Returns the logarithm of a number.", log);
    impl_fun_arg_rm_cc!("Returns the power of a number.", pow);

    impl_fun_rm_cc!("Returns the cosine of a number.", cos);
    impl_fun_rm_cc!("Returns the arccosine of a number.", acos);
    impl_fun_rm_cc!("Returns the sine of a number.", sin);
    impl_fun_rm_cc!("Returns the arcsine of a number.", asin);
    impl_fun_rm_cc!("Returns the tangent of a number.", tan);
    impl_fun_rm_p_cc!("Returns the arctangent of a number.", atan);

    impl_fun_rm!("Returns the hyperbolic cosine of a number.", cosh);
    impl_fun_rm_cc!("Returns the hyperbolic arccosine of a number.", acosh);
    impl_fun_rm!("Returns the hyperbolic sine of a number.", sinh);
    impl_fun_rm_cc!("Returns the hyperbolic arcsine of a number.", asinh);
    impl_fun_rm_p_cc!("Returns the hyperbolic tangent of a number.", tanh);
    impl_fun_rm_cc!("Returns the hyperbolic arctangent of a number.", atanh);
}

/// Create a new context with precision `p`.
///
/// ## Panics
///
/// The function call panics if memory allocation failed.
pub fn with_precision(p: usize) -> Context {
    Context {
        cc: Rc::new(RefCell::new(Consts::new().expect("Memory allocation"))),
        p,
        rm: DEFAULT_RM,
        value: BigFloat::new(p),
    }
}

/// Create a new context with rounding mode `rm`.
///
/// ## Panics
///
/// The function call panics if memory allocation failed.
pub fn with_rounding_mode(rm: RoundingMode) -> Context {
    Context {
        cc: Rc::new(RefCell::new(Consts::new().expect("Memory allocation"))),
        p: DEFAULT_P,
        rm,
        value: BigFloat::new(DEFAULT_P),
    }
}

/// Create a new context with constant cache `cc`.
pub fn with_consts(cc: Rc<RefCell<Consts>>) -> Context {
    Context {
        cc,
        p: DEFAULT_P,
        rm: DEFAULT_RM,
        value: BigFloat::new(DEFAULT_P),
    }
}

/// Create a new context with a given value.
pub fn with_value(value: BigFloat) -> Context {
    Context {
        cc: Rc::new(RefCell::new(Consts::new().expect("Memory allocation"))),
        p: value.get_precision().unwrap_or(DEFAULT_P),
        rm: DEFAULT_RM,
        value,
    }
}

pub mod ops {

    use super::{with_value, Context, DEFAULT_P, DEFAULT_RM};
    use crate::{BigFloat, Radix, NAN};

    use core::{
        cmp::Ordering, cmp::PartialEq, cmp::PartialOrd, fmt::Display, fmt::Formatter,
        iter::Product, iter::Sum, ops::Add, ops::AddAssign, ops::Div, ops::DivAssign, ops::Mul,
        ops::MulAssign, ops::Neg, ops::Rem, ops::Sub, ops::SubAssign, str::FromStr,
    };

    //
    // ops traits
    //

    impl Add<BigFloat> for Context {
        type Output = Self;
        fn add(self, rhs: BigFloat) -> Self::Output {
            with_value(BigFloat::add(&self.value, &rhs, self.rm))
        }
    }

    impl AddAssign<BigFloat> for Context {
        fn add_assign(&mut self, rhs: BigFloat) {
            self.value(BigFloat::add(&self.value, &rhs, self.rm));
        }
    }

    impl Div<BigFloat> for Context {
        type Output = Self;
        fn div(self, rhs: BigFloat) -> Self::Output {
            with_value(BigFloat::div(&self.value, &rhs, self.rm))
        }
    }

    impl DivAssign<BigFloat> for Context {
        fn div_assign(&mut self, rhs: BigFloat) {
            self.value(BigFloat::div(&self.value, &rhs, self.rm));
        }
    }

    impl Rem<BigFloat> for Context {
        type Output = Self;
        fn rem(self, rhs: BigFloat) -> Self::Output {
            with_value(BigFloat::rem(&self.value, &rhs, self.rm))
        }
    }

    impl Mul<BigFloat> for Context {
        type Output = Self;
        fn mul(self, rhs: BigFloat) -> Self::Output {
            with_value(BigFloat::mul(&self.value, &rhs, self.rm))
        }
    }

    impl MulAssign<BigFloat> for Context {
        fn mul_assign(&mut self, rhs: BigFloat) {
            self.value(BigFloat::mul(&self.value, &rhs, self.rm));
        }
    }

    impl Neg for Context {
        type Output = Self;
        fn neg(mut self) -> Self::Output {
            self.value.inv_sign();
            self
        }
    }

    impl<'a> Neg for &'a mut Context {
        type Output = Self;
        fn neg(self) -> Self::Output {
            self.value.inv_sign();
            self
        }
    }

    impl Sub<BigFloat> for Context {
        type Output = Self;
        fn sub(self, rhs: BigFloat) -> Self::Output {
            with_value(BigFloat::sub(&self.value, &rhs, self.rm))
        }
    }

    impl SubAssign<BigFloat> for Context {
        fn sub_assign(&mut self, rhs: BigFloat) {
            self.value(BigFloat::sub(&self.value, &rhs, self.rm));
        }
    }

    impl Add<&BigFloat> for Context {
        type Output = Self;
        fn add(self, rhs: &BigFloat) -> Self::Output {
            with_value(BigFloat::add(&self.value, rhs, self.rm))
        }
    }

    impl AddAssign<&BigFloat> for Context {
        fn add_assign(&mut self, rhs: &BigFloat) {
            self.value(BigFloat::add(&self.value, rhs, self.rm));
        }
    }

    impl Div<&BigFloat> for Context {
        type Output = Self;
        fn div(self, rhs: &BigFloat) -> Self::Output {
            with_value(BigFloat::div(&self.value, rhs, self.rm))
        }
    }

    impl DivAssign<&BigFloat> for Context {
        fn div_assign(&mut self, rhs: &BigFloat) {
            self.value(BigFloat::div(&self.value, rhs, self.rm));
        }
    }

    impl Mul<&BigFloat> for Context {
        type Output = Self;
        fn mul(self, rhs: &BigFloat) -> Self::Output {
            with_value(BigFloat::mul(&self.value, rhs, self.rm))
        }
    }

    impl MulAssign<&BigFloat> for Context {
        fn mul_assign(&mut self, rhs: &BigFloat) {
            self.value(BigFloat::mul(&self.value, rhs, self.rm));
        }
    }

    impl Sub<&BigFloat> for Context {
        type Output = Self;
        fn sub(self, rhs: &BigFloat) -> Self::Output {
            with_value(BigFloat::sub(&self.value, rhs, self.rm))
        }
    }

    impl SubAssign<&BigFloat> for Context {
        fn sub_assign(&mut self, rhs: &BigFloat) {
            self.value(BigFloat::sub(&self.value, rhs, self.rm));
        }
    }

    //
    // ordering traits
    //

    impl PartialEq<BigFloat> for Context {
        fn eq(&self, other: &BigFloat) -> bool {
            let cmp_result = BigFloat::cmp(&self.value, other);
            matches!(cmp_result, Some(0))
        }
    }

    impl PartialOrd<BigFloat> for Context {
        fn partial_cmp(&self, other: &BigFloat) -> Option<Ordering> {
            let cmp_result = BigFloat::cmp(&self.value, other);
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

    impl From<f64> for Context {
        fn from(f: f64) -> Self {
            with_value(BigFloat::from_f64(f, DEFAULT_P))
        }
    }

    impl From<f32> for Context {
        fn from(f: f32) -> Self {
            with_value(BigFloat::from_f32(f, DEFAULT_P))
        }
    }

    impl Display for Context {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
            self.value.write_str(f, Radix::Dec, self.rm)
        }
    }

    impl Default for Context {
        fn default() -> Self {
            Context::new()
        }
    }

    impl FromStr for Context {
        type Err = Context;

        /// Returns parsed number or NAN in case of error.
        fn from_str(src: &str) -> Result<Context, Self::Err> {
            BigFloat::parse(src, Radix::Dec, DEFAULT_P, DEFAULT_RM)
                .map(with_value)
                .ok_or_else(|| -> Context { with_value(NAN) })
        }
    }

    impl Product<BigFloat> for Context {
        fn product<I: Iterator<Item = BigFloat>>(mut iter: I) -> Self {
            if let Some(v) = iter.next() {
                let mut ctx = with_value(v);
                for v in iter {
                    ctx *= v;
                }
                ctx
            } else {
                Context::new()
            }
        }
    }

    impl Sum<BigFloat> for Context {
        fn sum<I: Iterator<Item = BigFloat>>(mut iter: I) -> Self {
            if let Some(v) = iter.next() {
                let mut ctx = with_value(v);
                for v in iter {
                    ctx += v;
                }
                ctx
            } else {
                Context::new()
            }
        }
    }

    impl<'a> Product<&'a BigFloat> for Context {
        fn product<I: Iterator<Item = &'a BigFloat>>(mut iter: I) -> Self {
            if let Some(v) = iter.next() {
                let mut ctx = with_value(v.clone());
                for v in iter {
                    ctx *= v;
                }
                ctx
            } else {
                Context::new()
            }
        }
    }

    impl<'a> Sum<&'a BigFloat> for Context {
        fn sum<I: Iterator<Item = &'a BigFloat>>(mut iter: I) -> Self {
            if let Some(v) = iter.next() {
                let mut ctx = with_value(v.clone());
                for v in iter {
                    ctx += v;
                }
                ctx
            } else {
                Context::new()
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use core::ops::{Add, Div, Mul, Neg, Sub};

    use super::*;

    #[test]
    fn test_ctx() {
        // context building
        let p = 256;
        let rm = RoundingMode::ToZero;
        let cc = Rc::new(RefCell::new(Consts::new().unwrap()));
        let val = BigFloat::from_i8(123, DEFAULT_P);

        let mut ctx = Context::new();
        ctx.precision(p)
            .rounding_mode(rm)
            .constant_cache(cc.clone())
            .value(val.clone());

        assert_eq!(ctx.get_precision(), p);
        assert_eq!(ctx.get_rounding_mode(), rm);
        assert_eq!(Rc::strong_count(&ctx.get_consts()), Rc::strong_count(&cc));
        assert_eq!(ctx.get_value(), val);

        // functions
        let refval = ctx.get_value();
        let logbase = BigFloat::from_i8(3, DEFAULT_P);
        let powi = 2;

        let ret = ctx
            .powi(powi)
            .sqrt()
            .cbrt()
            .pow(&logbase)
            .ln()
            .log2()
            .exp()
            .log10()
            .log(&logbase)
            .cos()
            .acos()
            .sin()
            .asin()
            .tan()
            .atan()
            .cosh()
            .acosh()
            .sinh()
            .asinh()
            .tanh()
            .atanh()
            .get_value();

        let refval =
            refval
                .powi(powi, p, rm)
                .sqrt(rm)
                .cbrt(rm)
                .pow(&logbase, rm, &mut cc.borrow_mut());
        let refval = refval.ln(rm, &mut cc.borrow_mut());
        let refval = refval.log2(rm, &mut cc.borrow_mut());
        let refval = refval.exp(rm, &mut cc.borrow_mut());
        let refval = refval.log10(rm, &mut cc.borrow_mut());
        let refval = refval.log(&logbase, rm, &mut cc.borrow_mut());
        let refval = refval.cos(rm, &mut cc.borrow_mut());
        let refval = refval.acos(rm, &mut cc.borrow_mut());
        let refval = refval.sin(rm, &mut cc.borrow_mut());
        let refval = refval.asin(rm, &mut cc.borrow_mut());
        let refval = refval.tan(rm, &mut cc.borrow_mut());
        let refval = refval.atan(rm, p, &mut cc.borrow_mut()).cosh(rm);
        let refval = refval.acosh(rm, &mut cc.borrow_mut()).sinh(rm);
        let refval = refval.asinh(rm, &mut cc.borrow_mut());
        let refval = refval.tanh(rm, p, &mut cc.borrow_mut());
        let refval = refval.atanh(rm, &mut cc.borrow_mut());

        assert_eq!(refval, ret);

        // ops by ref
        let rhs = BigFloat::from_i8(10, DEFAULT_P);
        ctx = ctx.add(&rhs).mul(&rhs).sub(&rhs).div(&rhs);
        ctx += &rhs;
        ctx -= &rhs;
        ctx *= &rhs;
        ctx /= &rhs;

        let mut ctxref = &mut ctx;
        ctxref = ctxref.neg();

        let refval = BigFloat::add(&refval, &rhs, rm);
        let refval = BigFloat::mul(&refval, &rhs, rm);
        let refval = BigFloat::sub(&refval, &rhs, rm);
        let refval = BigFloat::div(&refval, &rhs, rm);
        let refval = refval.neg();

        assert_eq!(refval, ctxref.get_value());

        // ops by val
        ctx = ctx
            .add(rhs.clone())
            .mul(rhs.clone())
            .sub(rhs.clone())
            .div(rhs.clone());

        let refval = BigFloat::add(&refval, &rhs, rm);
        let refval = BigFloat::mul(&refval, &rhs, rm);
        let refval = BigFloat::sub(&refval, &rhs, rm);
        let refval = BigFloat::div(&refval, &rhs, rm);

        assert_eq!(refval, ctx.get_value());
    }
}
