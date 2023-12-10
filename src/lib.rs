//! Astro-float (astronomically large floating point numbers) is a library that implements arbitrary precision floating point numbers.
//!
//! ## Introduction
//!
//! **Numbers**
//!
//!
//! The number is defined by the data type `BigFloat`.
//! Each finite number consists of an array of words representing the mantissa, exponent, and sign.
//! `BigFloat` can also be `Inf` (positive infinity), `-Inf` (negative infinity) or `NaN` (not-a-number).
//!
//!
//! `BigFloat` creation operations take bit precision as an argument.
//! Precision is always rounded up to the nearest word.
//! For example, if you specify a precision of 1 bit, then it will be converted to 64 bits when one word has a size of 64 bits.
//! If you specify a precision of 65 bits, the resulting precision will be 128 bits (2 words), and so on.
//!
//!
//! Most operations take the rounding mode as an argument.
//! The operation will typically internally result in a number with more precision than necessary.
//! Before the result is returned to the user, the result is rounded according to the rounding mode and reduced to the expected precision.
//!
//!
//! The result of an operation is marked as inexact if some of the bits were rounded when producing the result,
//! or if any of the operation's arguments were marked as inexact. The information about exactness is used to achieve correct rounding.
//!
//!
//! `BigFloat` can be parsed from a string and formatted into a string using binary, octal, decimal, or hexadecimal representation.
//!
//!
//! Numbers can be subnormal. Usually any number is normalized: the most significant bit of the mantissa is set to 1.
//! If the result of the operation has the smallest possible exponent, then normalization cannot be performed,
//! and some significant bits of the mantissa may become 0. This allows for a more gradual transition to zero.
//!
//! **Error handling**
//!
//! In case of an error, such as memory allocation error, `BigFloat` takes the value `NaN`.
//! `BigFloat::err()` can be used to get the associated error in this situation.
//!
//! **Constants**
//!
//! Constants such as pi or the Euler number have arbitrary precision and are evaluated lazily and then cached in the constants cache.
//! Some functions expect constants cache as parameter.
//!
//! **Correctness**
//!
//! Results of all arithmetic operations, mathematical functions, radix conversion, and constant values are correctly rounded
//! (a correctly rounded number is a number that is identical to a number computed to infinite precision and then rounded, reflecting no information loss during rounding).
//!
//! ## Examples
//!
//! The example below computes value of Pi with precision 1024 rounded to the nearest even number using `expr!` macro.
//! Macro simplifies syntax and takes care of the error.
//!
//! ```
//! use astro_float::Consts;
//! use astro_float::RoundingMode;
//! use astro_float::ctx::Context;
//! use astro_float::expr;
//!
//! // Create a context with precision 1024, rounding to the nearest even,
//! // and exponent range from -100000 to 100000.
//! let mut ctx = Context::new(1024, RoundingMode::ToEven,
//!     Consts::new().expect("Constants cache initialized"),
//!     -100000, 100000);
//!
//! // Compute pi: pi = 6*arctan(1/sqrt(3))
//! let pi = expr!(6 * atan(1 / sqrt(3)), &mut ctx);
//!
//! // Use library's constant value for verifying the result.
//! let pi_lib = ctx.const_pi();
//!
//! // Compare computed constant with library's constant
//! assert_eq!(pi.cmp(&pi_lib), Some(0));
//!
//! // Print using decimal radix.
//! println!("{}", pi);
//!
//! // output: 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458699748e+0
//! ```
//!
//! The example below computes value of Pi with precision 1024 rounded to the nearest even number using `BigFloat` directly.
//! We will take care of the error in this case.
//!
//! ``` rust
//! use astro_float::BigFloat;
//! use astro_float::Consts;
//! use astro_float::RoundingMode;
//!
//! // Precision with some space for error.
//! let p = 1024 + 8;
//!
//! // The results of computations will not be rounded.
//! // That will be more performant, even though it may give an incorrectly rounded result.
//! let rm = RoundingMode::None;
//!
//! // Initialize mathematical constants cache
//! let mut cc = Consts::new().expect("An error occured when initializing constants");
//!
//! // Compute pi: pi = 6*arctan(1/sqrt(3))
//! let six = BigFloat::from_word(6, 1);
//! let three = BigFloat::from_word(3, p);
//!
//! let n = three.sqrt(p, rm);
//! let n = n.reciprocal(p, rm);
//! let n = n.atan(p, rm, &mut cc);
//! let mut pi = six.mul(&n, p, rm);
//!
//! // Reduce precision to 1024 and round to the nearest even number.
//! pi.set_precision(1024, RoundingMode::ToEven).expect("Precision updated");
//!
//! // Use library's constant for verifying the result
//! let pi_lib = cc.pi(1024, RoundingMode::ToEven);
//!
//! // Compare computed constant with library's constant
//! assert_eq!(pi.cmp(&pi_lib), Some(0));
//!
//! // Print using decimal radix.
//! println!("{}", pi);
//!
//! // output: 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196442881097566593344612847564823378678316527120190914564856692346034861045432664821339360726024914127372458699748e+0
//! ```
//!
//! ## Performance recommendations
//!
//! When small error is acceptable because of rounding it is recommended to do all computations with `RoundingMode::None`, and use `BigFloat::set_precision` or `BigFloat::round` with a specific rounding mode just once for the final result.
//!
//! ## no_std
//!
//! The library can work without the standard library provided there is a memory allocator. The standard library dependency is activated by the feature `std`.
//! The feature `std` is active by default and must be excluded when specifying dependency, e.g.:
//!
//! ``` toml
//! [dependencies]
//! astro-float = { version = "0.7.2", default-features = false }
//! ```
//!

#![deny(missing_docs)]
#![deny(clippy::suspicious)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

/// Computes an expression with the specified precision and rounding mode.
/// Macro takes into account 2 aspects.
///
/// 1. Code simplification. Macro simplifies code and improves its readability by allowing to specify simple and concise expression
/// and process input arguments transparently.
///
/// 2. Error compensation. Macro compensates error caused by [catastrophic cancellation](https://en.wikipedia.org/wiki/Catastrophic_cancellation)
/// and some other situations where precision can be lost by automatically increasing the working precision internally.
///
/// The macro does not take care of correct rounding, because the completion of the rounding algorithm in finite time depends on the macro's input.
///
/// The macro accepts an expression to compute and a context.
/// The expression can include:
///
///  - Path expressions: variable names, constant names, etc.
///  - Integer literals, e.g. `123`, `-5`.
///  - Floating point literals, e.g. `1.234e-567`.
///  - String literals, e.g. `"-1.234_e-567"`.
///  - Binary operators.
///  - Unary `-` operator.
///  - Mathematical functions.
///  - Grouping with `(` and `)`.
///  - Constants `pi`, `e`, `ln_2`, and `ln_10`.
///
/// Binary operators:
///
///  - `+`: addition.
///  - `-`: subtraction.
///  - `*`: multiplication.
///  - `/`: division.
///  - `%`: modular division.
///
/// Mathematical functions:
///
///  - `recip(x)`: reciprocal of `x`.
///  - `sqrt(x)`: square root of `x`.
///  - `cbrt(x)`: cube root of `x`.
///  - `ln(x)`: natural logarithm of `x`.
///  - `log2(x)`: logarithm base 2 of `x`.
///  - `log10(x)`: logarithm base 10 of `x`.
///  - `log(x, b)`: logarithm with base `b` of `x`.
///  - `exp(x)`: `e` to the power of `x`.
///  - `pow(b, x)`: `b` to the power of `x`.
///  - `sin(x)`: sine of `x`.
///  - `cos(x)`: cosine of `x`.
///  - `tan(x)`: tangent of `x`.
///  - `asin(x)`: arcsine of `x`.
///  - `acos(x)`: arccosine of `x`.
///  - `atan(x)`: arctangent of `x`.
///  - `sinh(x)`: hyperbolic sine of `x`.
///  - `cosh(x)`: hyperbolic cosine of `x`.
///  - `tanh(x)`: hyperbolic tangent of `x`.
///  - `asinh(x)`: hyperbolic arcsine of `x`.
///  - `acosh(x)`: hyperbolic arccosine of `x`.
///  - `atanh(x)`: hyperbolic arctangent of `x`.
///
/// Constants:
///  - `pi`: pi number.
///  - `e`: Euler number.
///  - `ln_2`: natural logarithm of 2.
///  - `ln_10`: natural logarithm of 10.
///
/// The context determines the precision, the rounding mode of the result, and also contains the cache of constants.
///
/// Also, the macro uses minimum and maximum exponent values from the context to limit possible exponent range of the result and to set the limit of precision required for error compensation.
/// It is recommended to set the smallest values for the exponent range to increase the performance of computations (the internal precision may be as large as the exponent of a number).
///
/// A tuple `(usize, RoundingMode, &mut Consts)`, or `(usize, RoundingMode, &mut Consts, Exponent, Exponent)` can be used as a temporary context (see examples below).
///
/// Any input argument in the expression is interpreted as exact
/// (i.e. if an argument of an expression has type BigFloat and it is an inexact result of a previous computation).
///
/// ## Examples
///
/// ```
/// # use astro_float_macro::expr;
/// # use astro_float::RoundingMode;
/// # use astro_float::Consts;
/// # use astro_float::BigFloat;
/// # use astro_float::ctx::Context;
/// // Precision, rounding mode, constants cache, and exponent range.
/// let p = 128;
/// let rm = RoundingMode::Up;
/// let mut cc = Consts::new().expect("Failed to allocate constants cache");
/// let emin = -10000;
/// let emax = 10000;
///
/// // Create a context.
/// let mut ctx = Context::new(p, rm, cc, emin, emax);
///
/// let x = 123;
/// let y = "2345";
/// let z = 234.5e+1;
///
/// // Compute an expression.
/// let ret = expr!(x + y / z - ("120" - 120), &mut ctx);
///
/// assert_eq!(ret, BigFloat::from(124));
///
/// // Destructure context.
/// let (p, rm, mut cc, emin, emax) = ctx.to_raw_parts();
///
/// // Compute an expression using a temporary context.
/// let ret = expr!(x + y / z, (p, rm, &mut cc, emin, emax));
///
/// assert_eq!(ret, BigFloat::from(124));
/// ```
pub use astro_float_macro::expr;

pub use astro_float_num::*;
