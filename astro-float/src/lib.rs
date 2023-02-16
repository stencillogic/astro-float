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
//! Some functions expect constants cache as parameter because the library does not maintain global state.
//!
//! **Correctness**
//!
//! Results of all arithmetic operations, mathematical functions, and constant values are correctly rounded
//! (A result is correctly rounded if it is equal to the result computed with infinite precision and then rounded).
//!
//!
//! ## Examples
//!
//! The example below computes value of Pi with precision 1024 rounded to even using `expr!` macro.
//! Macro simplifies syntax, takes care of the error and correct rounding of the result.
//! Although, macro has certain pitfalls to avoid. Check the macro documentation for more details.
//!
//! ```
//! use astro_float::Consts;
//! use astro_float::RoundingMode;
//! use astro_float::ctx::Context;
//! use astro_float::expr;
//!
//! // Create a context with precision 1024, and rounding to even.
//! let mut ctx = Context::new(1024, RoundingMode::ToEven,
//!     Consts::new().expect("Contants cache initialized"));
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
//! The example below computes value of Pi with precision 1024 rounded to even using `BigFloat` directly.
//! In this case, we will take care of error, and we will not check wether the resul is correctly rounded.
//!
//! ``` rust
//! use astro_float::BigFloat;
//! use astro_float::Consts;
//! use astro_float::RoundingMode;
//!
//! // Precision with some space for error.
//! let p = 1024 + 8;
//!
//! // Rounding of all operations
//! let rm = RoundingMode::ToEven;
//!
//! // Initialize mathematical constants cache
//! let mut cc = Consts::new().expect("An error occured when initializing contants");
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
//! // Reduce precision to 1024
//! pi.set_precision(1024, rm).expect("Precision updated");
//!
//! // Use library's constant for verifying the result
//! let pi_lib = cc.pi(1024, rm);
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
//! ## no_std
//!
//! The library can work without the standard library provided there is a memory allocator. The standard library dependency is activated by the feature `std`.
//! The feature `std` is active by default and must be excluded when specifying dependency, e.g.:
//!
//! ``` toml
//! [dependencies]
//! astro-float = { version = "0.6.1", default-features = false }
//! ```
//!

#![deny(missing_docs)]
#![deny(clippy::suspicious)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

/// Computes an expression with the specified precision and rounding mode.
///
/// The macro accepts an expression to compute and a context.
/// In the expression you can specify:
///
///  - Path expressions: variable names, constant names, etc.
///  - Integer literals, e.g. `123`, `-5`.
///  - Floating point literals, e.g. `1.234e-567`.
///  - String literals, e.g. `"-1.234_e-567"`.
///  - Binary operators.
///  - Unary `-` operator.
///  - Mathematical functions.
///  - Grouping with `(` and `)`.
///
/// Supported binary operators:
///
///  - `+`: addition.
///  - `-`: subtraction.
///  - `*`: multiplication.
///  - `/`: division.
///  - `%`: modular division.
///
/// Supported mathematical functions:
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
/// The context determines the precision, the rounding mode of the result, and also contains the cache of constants.
/// Tuple `(usize, RoundingMode, &mut Consts)` can also be used as a temporary context (see example below).
///
/// The macro will determine additional precision needed to compensate error and perform correct rounding.
/// It will also try to eliminate cancellation which may appear when expression is computed.
///
///
/// **Avoid passing expressions which contain mathematical identity if you need correctly rounded result**.
///
/// Examples of such expressions:
///
///  - `expr!(sin(x) - sin(x), ctx)`
///  - `expr!(ln(exp(x)), ctx)`,
///  - `expr!(sin(x) * sin(x) / (1 - cos(x) * cos(x)), ctx)`,
///
/// Macro does not analyze the expression for presense of identity and will increase the precision infinitely and will never return.
///
/// Although, you can specify rounding mode `None`. In this case, macro will return even if you pass an identity expression.
///
/// ## Examples
///
/// ```
/// # use astro_float_macro::expr;
/// # use astro_float::RoundingMode;
/// # use astro_float::Consts;
/// # use astro_float::BigFloat;
/// # use astro_float::ctx::Context;
/// // Precision, rounding mode, and constants cache.
/// let p = 128;
/// let rm = RoundingMode::Up;
/// let mut cc = Consts::new().expect("Failed to allocate constants cache");
///
/// // Create a context.
/// let mut ctx = Context::new(p, rm, cc);
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
/// let (p, rm, mut cc) = ctx.to_raw_parts();
///
/// // Compute an expression using temporary context.
/// let ret = expr!(x + y / z, (p, rm, &mut cc));
///
/// assert_eq!(ret, BigFloat::from(124));
/// ```
pub use astro_float_macro::expr;

pub use astro_float_num::*;
