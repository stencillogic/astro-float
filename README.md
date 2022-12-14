![Rust](https://github.com/stencillogic/astro-float/workflows/Rust/badge.svg)
![Minimum rustc version](https://img.shields.io/badge/rustc-1.62.1+-lightgray.svg)

Astro-float (astronomically large floating point numbers) is a library that implements arbitrary precision floating point numbers purely in Rust.

The library implements the basic operations and functions. It uses classical algorithms such as Karatsuba, Toom-Cook, Schönhage-Strassen algorithm, and others.

The library can work without the standard library provided there is a memory allocator.

## Usage

Below is an example of using the library.
For more information please refer to the library documentation: https://docs.rs/astro-float/latest/astro_float/


Calculate Pi with 1024 bit precision:

``` rust
use astro_float::BigFloatNumber;
use astro_float::Consts;
use astro_float::RoundingMode;
use astro_float::Radix;
use astro_float::Error;

// Precision with some space for error.
let p = 1024 + 8;

// Rounding of all operations
let rm = RoundingMode::ToEven;

// Initialize mathematical constants cache
let mut cc = Consts::new().unwrap();

// Compute pi: pi = 6*arctan(1/sqrt(3))
let six = BigFloatNumber::from_word(6, 1).unwrap();
let three = BigFloatNumber::from_word(3, p).unwrap();

let n = three.sqrt(p, rm).unwrap();
let n = n.reciprocal(p, rm).unwrap();
let n = n.atan(p, rm, &mut cc).unwrap();
let mut pi = six.mul(&n, p, rm).unwrap();

// Reduce precision to 1024
pi.set_precision(1024, rm).unwrap();

// Use library's constant for verifying the result
let pi_lib = cc.pi(1024, rm).unwrap();

// Compare computed constant with library's constant
assert!(pi.cmp(&pi_lib) == 0);

// Print computed result as decimal number
let s = pi.format(Radix::Dec, rm).unwrap();
println!("{}", s);
```

## Performance

Benchmark can be found here: https://github.com/stencillogic/bigfloat-bench.

## Roadmap

Future improvements include the implementation of faster mathematical function algorithms for arguments with large precision, such as AGM implementation for calculating the logarithm, and faster trigonometric functions.

## Contributing

The library is still young and may lack some features or contain bugs. Issues for these or other cases can be opened here: https://github.com/stencillogic/astro-float/issues 