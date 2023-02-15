![Rust](https://github.com/stencillogic/astro-float/workflows/Rust/badge.svg)
![Minimum rustc version](https://img.shields.io/badge/rustc-1.62.1+-lightgray.svg)

Astro-float (astronomically large floating point numbers) is a library that implements arbitrary precision floating point numbers with correct rounding purely in Rust.

The library implements the basic operations and functions. It uses classical algorithms such as Karatsuba, Toom-Cook, Schönhage-Strassen algorithm, and others.

The library can work without the standard library provided there is a memory allocator.

## What's new

Information about the latest changes is available in [Release notes](https://github.com/stencillogic/astro-float/blob/main/RELEASE_NOTES.md)

## Usage

Below is an example of using the library.
For more information please refer to the library documentation: https://docs.rs/astro-float/latest/astro_float/


Calculate Pi with 1024 bit precision rounded to even.

``` rust
use astro_float::Consts;
use astro_float::RoundingMode;
use astro_float::ctx::Context;
use astro_float_macro::expr;

// Create a context with precision 1024, and rounding to even.
let mut ctx = Context::new(1024, RoundingMode::ToEven, 
    Consts::new().expect("Contants cache initialized"));

// Compute pi: pi = 6*arctan(1/sqrt(3))
let pi = expr!(6 * atan(1 / sqrt(3)), &mut ctx);

// Use library's constant value for verifying the result.
let pi_lib = ctx.const_pi();

// Compare computed constant with library's constant
assert_eq!(pi.cmp(&pi_lib), Some(0));
```

## Performance

Benchmark can be found here: https://github.com/stencillogic/bigfloat-bench.

## Contributing

Issues regarding bugs or new features can be opened here: https://github.com/stencillogic/astro-float/issues 