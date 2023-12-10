# Release notes

**0.9.0**

 - Error compensation in the `expr` macro has been reworked.
 - Exponent range is introduced in the context.
 - Stability improvements.

**0.8.0**

 - Scalable conversion to decimal and from decimal base implemented: conversion and formatting functions now require constants cache.
 - Implementation of traits `FromStr` and `Display` and `serde` feature are now not available in no_std.
 - Mechanism of correct rounding has been removed from the `expr!` macro to increase its stablility.
 - Macro `expr!` now supports constants `pi`, `e`, `ln_2`, and `ln_10` in expressions.
 - New public functions `BigFloat::nan()`, `BigFloat::format()`, new constant `EXPONENT_BIT_SIZE`.
 - Bug fixes and code refinements.
 - Improved portability and stability.

**0.7.0**

 - Improved integration tests.
 - Bug fixes and code refinement.
 - Improved portability.
 - Test coverage badge added.
 - Smallvec replaced with Vec.
 - Unsafe code revisited.

**0.6.0**

 - `expr!` macro implemented.
 - BigFloat stores information about its inexactness.
 - `FromExt` conversion trait added for BigFloat.

**0.5.0**

 - Release notes introduction.
 - Correct rounding of all arithmetic operations, math functions, and constant values.
 - Api compliance with https://rust-lang.github.io/api-guidelines/
