//! Context for operations on BigFloat.

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

/// Context allows to perform operations using predefined parameters.
///
/// Context can be used to pass arguments, like precision and rounding mode, to each operation indirectly.
///
/// ## Examples
///
/// ``` rust
/// use astro_float::with_consts;
/// use astro_float::Consts;
/// use astro_float::RoundingMode;
/// use astro_float::BigFloat;
/// use std::rc::Rc;
/// use std::cell::RefCell;
///
/// // Shared constants cache.
/// let cc = Rc::new(RefCell::new(Consts::new().unwrap()));
///
/// // Create context with precision 1024+8, rounding mode RoundingMode::ToEven,
/// // constant cache cc, and default value 0.
/// let mut ctx = with_consts(cc.clone())
///     .precision(1024 + 8)
///     .rounding_mode(RoundingMode::ToEven);
///
/// // Compute pi: pi = 6*arctan(1/sqrt(3))
/// let mut pi = ctx.add(&3u8.into())
///     .sqrt()
///     .reciprocal()
///     .atan()
///     .mul(&6u8.into())
///     .get_value().clone();       // return the value
///
/// pi.set_precision(1024, RoundingMode::ToEven).unwrap();
///
/// // Use library's constant for verifying the result
/// let pi_lib: BigFloat = cc.borrow_mut().pi(1024, RoundingMode::ToEven).unwrap().into();
///
/// assert_eq!(pi_lib, pi);
/// ```
#[derive(Clone, Debug)]
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
    /// The function call panics if memory allocation for constants cache has failed.
    pub fn new() -> Self {
        Context {
            cc: Rc::new(RefCell::new(Consts::new().expect("Memory allocation"))),
            p: DEFAULT_P,
            rm: DEFAULT_RM,
            value: BigFloat::new(DEFAULT_P),
        }
    }

    /// Sets the precision of the context and returns the modified context.
    pub fn precision(mut self, p: usize) -> Self {
        self.set_precision(p);
        self
    }

    /// Sets the rounding mode of the context and returns the modified context.
    pub fn rounding_mode(mut self, rm: RoundingMode) -> Self {
        self.set_rounding_mode(rm);
        self
    }

    /// Sets the constant cache of the context and returns the modified context.
    pub fn consts(mut self, cc: Rc<RefCell<Consts>>) -> Self {
        self.set_consts(cc);
        self
    }

    /// Sets the current value of the context and returns the modified context.
    pub fn value(mut self, value: BigFloat) -> Self {
        self.set_value(value);
        self
    }

    /// Sets the precision of the context.
    pub fn set_precision(&mut self, p: usize) {
        self.p = p;
    }

    /// Sets the rounding mode of the context.
    pub fn set_rounding_mode(&mut self, rm: RoundingMode) {
        self.rm = rm;
    }

    /// Sets the constant cache of the context.
    pub fn set_consts(&mut self, cc: Rc<RefCell<Consts>>) {
        self.cc = cc;
    }

    /// Sets the current value of the context and returns context.
    pub fn set_value(&mut self, value: BigFloat) {
        self.value = value;
    }

    /// Returns the precision of the context.
    pub fn precision(&self) -> usize {
        self.p
    }

    /// Returns the rounding mode of the context.
    pub fn rounding_mode(&self) -> RoundingMode {
        self.rm
    }

    /// Returns the constant cache of the context.
    pub fn consts(&self) -> Rc<RefCell<Consts>> {
        self.cc.clone()
    }

    /// Returns the current value of the context.
    pub fn value(&self) -> &BigFloat {
        &self.value
    }

    /// Returns `self` to the power of `n`.
    pub fn powi(&mut self, n: usize) -> &mut Self {
        let val = self.value.powi(n, self.p, self.rm);
        self.set_value(val);
        self
    }

    /// Returns the remainder of division of the current value of the context by a given BigFloat.
    pub fn rem(&mut self, arg: &BigFloat) -> &mut Self {
        let val = self.value.rem(arg);
        self.set_value(val);
        self
    }
}

macro_rules! impl_fun_rm {
    ($comment:literal, $fname:ident) => {
        #[doc=$comment]
        pub fn $fname(&mut self) -> &mut Self {
            let val = self.value.$fname(self.p, self.rm);
            self.set_value(val);
            self
        }
    };
}

macro_rules! impl_fun_rm_cc {
    ($comment:literal, $fname:ident) => {
        #[doc=$comment]
        pub fn $fname(&mut self) -> &mut Self {
            let val = self
                .value
                .$fname(self.p, self.rm, &mut self.cc.borrow_mut());
            self.set_value(val);
            self
        }
    };
}

macro_rules! impl_fun_arg_rm_cc {
    ($comment:literal, $fname:ident) => {
        #[doc=$comment]
        pub fn $fname(&mut self, arg: &BigFloat) -> &mut Self {
            let val = self
                .value
                .$fname(arg, self.p, self.rm, &mut self.cc.borrow_mut());
            self.set_value(val);
            self
        }
    };
}

macro_rules! impl_fun_arg_rm_p {
    ($comment:literal, $fname:ident) => {
        #[doc=$comment]
        pub fn $fname(&mut self, arg: &BigFloat) -> &mut Self {
            let val = self.value.$fname(arg, self.p, self.rm);
            self.set_value(val);
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
                .$fname(self.p, self.rm, &mut self.cc.borrow_mut());
            self.set_value(val);
            self
        }
    };
}

impl Context {
    impl_fun_arg_rm_p!("Adds BigFloat to the current value of the context.", add);
    impl_fun_arg_rm_p!(
        "Subtracts BigFloat from the current value of the context.",
        sub
    );
    impl_fun_arg_rm_p!(
        "Multiplies BigFloat by the current value of the context.",
        mul
    );
    impl_fun_arg_rm_p!(
        "Divides the current value of the context by the BigFloat.",
        div
    );

    impl_fun_rm!("Returns the reciprocal of a number.", reciprocal);

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

    impl_fun_rm_cc!("Returns the hyperbolic cosine of a number.", cosh);
    impl_fun_rm_cc!("Returns the hyperbolic arccosine of a number.", acosh);
    impl_fun_rm_cc!("Returns the hyperbolic sine of a number.", sinh);
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

    use super::{with_value, Context};
    use crate::BigFloat;

    use core::{
        cmp::Ordering,
        cmp::PartialEq,
        cmp::PartialOrd,
        fmt::Display,
        fmt::{Binary, Formatter, Octal, UpperHex},
        ops::Add,
        ops::AddAssign,
        ops::Div,
        ops::Mul,
        ops::MulAssign,
        ops::Neg,
        ops::Rem,
        ops::Sub,
        ops::SubAssign,
        ops::{DivAssign, RemAssign},
        str::FromStr,
    };

    //
    // ops traits
    //

    impl Rem<BigFloat> for &mut Context {
        type Output = Self;
        fn rem(self, rhs: BigFloat) -> Self::Output {
            self.set_value(BigFloat::rem(&self.value, &rhs));
            self
        }
    }

    impl Rem<&BigFloat> for &mut Context {
        type Output = Self;
        fn rem(self, rhs: &BigFloat) -> Self::Output {
            self.set_value(BigFloat::rem(&self.value, rhs));
            self
        }
    }

    impl Rem<BigFloat> for Context {
        type Output = Self;
        fn rem(self, rhs: BigFloat) -> Self::Output {
            let val = BigFloat::rem(&self.value, &rhs);
            self.value(val)
        }
    }

    impl Rem<&BigFloat> for Context {
        type Output = Self;
        fn rem(self, rhs: &BigFloat) -> Self::Output {
            let val = BigFloat::rem(&self.value, rhs);
            self.value(val)
        }
    }

    impl RemAssign<BigFloat> for Context {
        fn rem_assign(&mut self, rhs: BigFloat) {
            self.set_value(BigFloat::rem(&self.value, &rhs));
        }
    }

    impl RemAssign<&BigFloat> for Context {
        fn rem_assign(&mut self, rhs: &BigFloat) {
            self.set_value(BigFloat::rem(&self.value, rhs));
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

    macro_rules! impl_arith_op {
        ($trait:ty, $rhs:ty, $fn:ident, $ct:ty) => {
            impl $trait for $ct {
                type Output = Self;
                fn $fn(self, rhs: $rhs) -> Self::Output {
                    self.set_value(BigFloat::$fn(&self.value, &rhs, self.p, self.rm));
                    self
                }
            }
        };
    }

    macro_rules! impl_arith_op2 {
        ($trait:ty, $rhs:ty, $fn:ident, $ct:ty) => {
            impl $trait for $ct {
                type Output = Self;
                fn $fn(self, rhs: $rhs) -> Self::Output {
                    let val = self.value.$fn(&rhs, self.p, self.rm);
                    self.value(val)
                }
            }
        };
    }

    impl_arith_op!(Add<BigFloat>, BigFloat, add, &mut Context);
    impl_arith_op!(Sub<BigFloat>, BigFloat, sub, &mut Context);
    impl_arith_op!(Mul<BigFloat>, BigFloat, mul, &mut Context);
    impl_arith_op!(Div<BigFloat>, BigFloat, div, &mut Context);

    impl_arith_op!(Add<&BigFloat>, &BigFloat, add, &mut Context);
    impl_arith_op!(Sub<&BigFloat>, &BigFloat, sub, &mut Context);
    impl_arith_op!(Mul<&BigFloat>, &BigFloat, mul, &mut Context);
    impl_arith_op!(Div<&BigFloat>, &BigFloat, div, &mut Context);

    impl_arith_op2!(Add<BigFloat>, BigFloat, add, Context);
    impl_arith_op2!(Sub<BigFloat>, BigFloat, sub, Context);
    impl_arith_op2!(Mul<BigFloat>, BigFloat, mul, Context);
    impl_arith_op2!(Div<BigFloat>, BigFloat, div, Context);

    impl_arith_op2!(Add<&BigFloat>, &BigFloat, add, Context);
    impl_arith_op2!(Sub<&BigFloat>, &BigFloat, sub, Context);
    impl_arith_op2!(Mul<&BigFloat>, &BigFloat, mul, Context);
    impl_arith_op2!(Div<&BigFloat>, &BigFloat, div, Context);

    macro_rules! impl_arith_assign_op {
        ($trait:ty, $rhs:ty, $op:ident, $fn:ident, $ct:ty) => {
            impl $trait for $ct {
                fn $op(&mut self, rhs: $rhs) {
                    self.set_value(BigFloat::$fn(&self.value, &rhs, self.p, self.rm));
                }
            }
        };
    }

    impl_arith_assign_op!(AddAssign<BigFloat>, BigFloat, add_assign, add, Context);
    impl_arith_assign_op!(SubAssign<BigFloat>, BigFloat, sub_assign, sub, Context);
    impl_arith_assign_op!(MulAssign<BigFloat>, BigFloat, mul_assign, mul, Context);
    impl_arith_assign_op!(DivAssign<BigFloat>, BigFloat, div_assign, div, Context);

    impl_arith_assign_op!(AddAssign<&BigFloat>, &BigFloat, add_assign, add, Context);
    impl_arith_assign_op!(SubAssign<&BigFloat>, &BigFloat, sub_assign, sub, Context);
    impl_arith_assign_op!(MulAssign<&BigFloat>, &BigFloat, mul_assign, mul, Context);
    impl_arith_assign_op!(DivAssign<&BigFloat>, &BigFloat, div_assign, div, Context);

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

    macro_rules! impl_format_rdx {
        ($trait:ty, $trait_fun:path, $rdx:path) => {
            impl $trait for Context {
                fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
                    $trait_fun(&self.value, f)
                }
            }
        };
    }

    impl_format_rdx!(Binary, Binary::fmt, Radix::Bin);
    impl_format_rdx!(Octal, Octal::fmt, Radix::Oct);
    impl_format_rdx!(Display, Display::fmt, Radix::Dec);
    impl_format_rdx!(UpperHex, UpperHex::fmt, Radix::Hex);

    impl Default for Context {
        fn default() -> Self {
            Context::new()
        }
    }

    impl FromStr for Context {
        type Err = ();

        /// Returns parsed number or NAN in case of error.
        fn from_str(src: &str) -> Result<Context, Self::Err> {
            BigFloat::from_str(src).map(with_value)
        }
    }
}

#[cfg(test)]
mod tests {

    use core::ops::{Add, Div, Mul, Neg, Sub};

    use crate::common::util::rand_p;

    use super::*;

    #[test]
    fn test_ctx() {
        // context building
        let p = rand_p();
        let rm = RoundingMode::ToZero;
        let cc = Rc::new(RefCell::new(Consts::new().unwrap()));
        let val = BigFloat::from_i8(123, DEFAULT_P);

        let mut ctx = Context::new()
            .precision(p)
            .rounding_mode(rm)
            .consts(cc.clone())
            .value(val.clone());

        assert_eq!(ctx.get_precision(), p);
        assert_eq!(ctx.get_rounding_mode(), rm);
        assert_eq!(Rc::strong_count(&ctx.get_consts()), Rc::strong_count(&cc));
        assert_eq!(ctx.get_value(), &val);

        // functions
        let refval = ctx.get_value().clone();
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
            .get_value()
            .clone();

        let refval = refval.powi(powi, p, rm).sqrt(p, rm).cbrt(p, rm).pow(
            &logbase,
            p,
            rm,
            &mut cc.borrow_mut(),
        );
        let refval = refval.ln(p, rm, &mut cc.borrow_mut());
        let refval = refval.log2(p, rm, &mut cc.borrow_mut());
        let refval = refval.exp(p, rm, &mut cc.borrow_mut());
        let refval = refval.log10(p, rm, &mut cc.borrow_mut());
        let refval = refval.log(&logbase, p, rm, &mut cc.borrow_mut());
        let refval = refval.cos(p, rm, &mut cc.borrow_mut());
        let refval = refval.acos(p, rm, &mut cc.borrow_mut());
        let refval = refval.sin(p, rm, &mut cc.borrow_mut());
        let refval = refval.asin(p, rm, &mut cc.borrow_mut());
        let refval = refval.tan(p, rm, &mut cc.borrow_mut());
        let refval = refval.atan(p, rm, &mut cc.borrow_mut());
        let refval = refval.cosh(p, rm, &mut cc.borrow_mut());
        let refval = refval.acosh(p, rm, &mut cc.borrow_mut());
        let refval = refval.sinh(p, rm, &mut cc.borrow_mut());
        let refval = refval.asinh(p, rm, &mut cc.borrow_mut());
        let refval = refval.tanh(p, rm, &mut cc.borrow_mut());
        let refval = refval.atanh(p, rm, &mut cc.borrow_mut());

        assert_eq!(refval, ret);

        // ops by ref
        let rhs = BigFloat::from_i8(10, DEFAULT_P);
        let mut ctx = ctx.add(&rhs).mul(&rhs).sub(&rhs).div(&rhs);
        ctx += &rhs;
        ctx -= &rhs;
        ctx *= &rhs;
        ctx /= &rhs;

        let mut ctxref = &mut ctx;
        ctxref = ctxref.neg();

        let refval = BigFloat::add(&refval, &rhs, p, rm);
        let refval = BigFloat::mul(&refval, &rhs, p, rm);
        let refval = BigFloat::sub(&refval, &rhs, p, rm);
        let refval = BigFloat::div(&refval, &rhs, p, rm);
        let refval = BigFloat::add(&refval, &rhs, p, rm);
        let refval = BigFloat::sub(&refval, &rhs, p, rm);
        let refval = BigFloat::mul(&refval, &rhs, p, rm);
        let refval = BigFloat::div(&refval, &rhs, p, rm);
        let refval = refval.neg();

        assert_eq!(refval, ctxref.get_value());

        // ops by val
        let ctx = ctx
            .add(rhs.clone())
            .mul(rhs.clone())
            .sub(rhs.clone())
            .div(rhs.clone());

        let refval = BigFloat::add(&refval, &rhs, p, rm);
        let refval = BigFloat::mul(&refval, &rhs, p, rm);
        let refval = BigFloat::sub(&refval, &rhs, p, rm);
        let refval = BigFloat::div(&refval, &rhs, p, rm);

        assert_eq!(refval, ctx.get_value());
    }
}
