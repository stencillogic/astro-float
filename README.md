![Rust](https://github.com/stencillogic/num-bigfloat/workflows/Rust/badge.svg)

Multiple precision floating point numbers implemented purely in Rust. 

## Rationale

There are several notable implementations of numbers with increased precision for Rust. Among the libraries, one can recall [num-bigint](https://crates.io/crates/num-bigint), [rust_decimal](https://crates.io/crates/rust_decimal).

While these libraries are great in many ways, they don't allow you to perform operations on numbers while still providing fairly high precision.

There are also wrapper libraries ([rug](https://crates.io/crates/rug)) that depend on libraries written in other programming languages.

This library is written in pure Rust, provides more precision than f32, f64, and some other data types with increased precision.

## Number characteristics

Currently, floating point numbers in this library have the following predefined characteristics:

| Name                          | Value  |
|:------------------------------|-------:|
| Decimal positions in mantissa |     40 |
| Exponent minimum value        |   -128 |
| Exponent maximum value        |    127 |

## no_std

Library can be used without the standard Rust library. This can be achieved by turning off `std` feature.
