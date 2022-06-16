![Rust](https://github.com/stencillogic/num-bigfloat/workflows/Rust/badge.svg)

Multiple precision floating point numbers implemented purely in Rust. 

## Rationale

There are several notable implementations of numbers with increased precision for Rust. Among the libraries, one can recall [num-bigint](https://crates.io/crates/num-bigint), [rust_decimal](https://crates.io/crates/rust_decimal).

While these libraries are great in many ways, they don't allow you to perform operations on numbers while still providing fairly high precision.

There are also wrapper libraries that depend on libraries written in other programming languages.

This library fills this gap. It is written in pure Rust, provides more precision than f32, f64, and other data types with increased precision.

## Characteristics

| Name                          | Value  |
|:------------------------------|-------:|
| Decimal positions in mantissa |     40 |
| Exponent minimum value        |   -128 |
| Exponent maximum value        |    127 |

The implementation does not rely heavily on the capabilities of the standard library, and can be adapted for use without the standard library.

