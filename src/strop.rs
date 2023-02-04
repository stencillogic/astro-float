//! BigFloatNumber formatting.

use crate::defs::Error;
use crate::defs::Radix;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::parser;
use crate::Exponent;
use crate::Sign;

#[cfg(feature = "std")]
use std::fmt::Write;

#[cfg(not(feature = "std"))]
use {alloc::string::String, core::fmt::Write};

const DIGIT_CHARS: [char; 16] =
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'];

impl BigFloatNumber {
    /// Parses the number from the string `s` using radix `rdx`, precision `p`, and rounding mode `rm`.
    /// Note, since hexadecimal digits include the character "e", the exponent part is separated
    /// from the mantissa by "_".
    /// For example, a number with mantissa `123abcdef` and exponent `123` would be formatted as `123abcdef_e+123`.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: failed to parse input or precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    pub fn parse(s: &str, rdx: Radix, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        Self::p_assertion(p)?;

        let ps = parser::parse(s, rdx)?;

        if ps.is_nan() || ps.is_inf() {
            Err(Error::InvalidArgument)
        } else {
            let (m, s, e) = ps.raw_parts();
            BigFloatNumber::convert_from_radix(s, m, e, rdx, p, rm)
        }
    }

    /// Formats the number using radix `rdx` and rounding mode `rm`.
    /// Note, since hexadecimal digits include the character "e", the exponent part is separated
    /// from the mantissa by "_".
    /// For example, a number with mantissa `123abcdef` and exponent `123` would be formatted as `123abcdef_e+123`.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    pub fn format(&self, rdx: Radix, rm: RoundingMode) -> Result<String, Error> {
        let (s, m, e) = self.convert_to_radix(rdx, rm)?;

        let mut mstr = String::new();
        let mstr_sz = 8
            + (self.mantissa_max_bit_len() + core::mem::size_of::<Exponent>() * 8)
                / match rdx {
                    Radix::Bin => 1,
                    Radix::Oct => 3,
                    Radix::Dec => 3,
                    Radix::Hex => 4,
                };

        // TODO: replace SmallVec with Vec.
        mstr.try_reserve_exact(mstr_sz)?;

        if s == Sign::Neg {
            mstr.push('-');
        }

        if m.is_empty() {
            mstr.push_str("0.0");
        } else {
            let mut iter = m.iter();

            if self.is_subnormal() {
                mstr.push('0');
            } else {
                mstr.push(DIGIT_CHARS[*iter.next().unwrap() as usize]); // m is not empty as checked above, hence unwrap
            }

            mstr.push('.');

            iter.map(|&d| DIGIT_CHARS[d as usize])
                .for_each(|v| mstr.push(v));

            if rdx == Radix::Hex {
                let _ = write!(mstr, "_");
            }

            if e < 1 {
                let val = if self.is_subnormal() {
                    e.unsigned_abs() as usize
                } else {
                    (e as isize - 1).unsigned_abs()
                };

                let _ = match rdx {
                    Radix::Bin => write!(mstr, "e-{:b}", val),
                    Radix::Oct => write!(mstr, "e-{:o}", val),
                    Radix::Dec => write!(mstr, "e-{}", val),
                    Radix::Hex => write!(mstr, "e-{:x}", val),
                };
            } else {
                let _ = match rdx {
                    Radix::Bin => write!(mstr, "e+{:b}", e as isize - 1),
                    Radix::Oct => write!(mstr, "e+{:o}", e as isize - 1),
                    Radix::Dec => write!(mstr, "e+{}", e as isize - 1),
                    Radix::Hex => write!(mstr, "e+{:x}", e as isize - 1),
                };
            };
        }

        Ok(mstr)
    }
}

#[cfg(test)]
mod tests {

    use rand::random;

    use crate::{
        common::util::random_subnormal, Exponent, EXPONENT_MAX, EXPONENT_MIN, WORD_BIT_SIZE,
    };

    use super::*;

    #[test]
    fn test_strop() {
        let mut eps = BigFloatNumber::from_word(1, 192).unwrap();
        let rm = RoundingMode::ToEven;

        for i in 0..1000 {
            let p1 = (random::<usize>() % 32 + 3) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % 32 + 3) * WORD_BIT_SIZE;
            let p = p1.min(p2);

            for rdx in [Radix::Bin, Radix::Oct, Radix::Hex, Radix::Dec] {
                let mut n = if i & 1 == 0 {
                    BigFloatNumber::random_normal(p1, EXPONENT_MIN, EXPONENT_MAX).unwrap()
                } else {
                    random_subnormal(p1)
                };
                let s = n.format(rdx, rm).unwrap();
                let mut d = BigFloatNumber::parse(&s, rdx, p2, rm).unwrap();

                if rdx == Radix::Dec {
                    //println!("\n{:?}\n{:?}\n{:?}", s, n, d);
                    if i & 1 == 0 {
                        eps.set_exponent(n.exponent() - p as Exponent + 3);
                        assert!(
                            d.sub(&n, d.mantissa_max_bit_len(), rm)
                                .unwrap()
                                .abs()
                                .unwrap()
                                .cmp(&eps)
                                < 0
                        );
                    } else {
                        let mut eps2 = BigFloatNumber::min_positive(p).unwrap();
                        eps2.set_exponent(eps2.exponent() + 2);
                        assert!(
                            d.sub(&n, d.mantissa_max_bit_len(), rm)
                                .unwrap()
                                .abs()
                                .unwrap()
                                .cmp(&eps2)
                                < 0
                        );
                    }
                } else {
                    if p2 < p1 {
                        n.set_precision(p, rm).unwrap();
                    } else if p2 > p1 {
                        d.set_precision(p, rm).unwrap();
                    }
                    //println!("\n{:?}\n{:?}\n{:?}", s, n, d);
                    assert!(d.cmp(&n) == 0);
                }
            }
        }

        // MIN, MAX, min_positive
        let p1 = (random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
        let p = p1.min(p2);

        for rdx in [Radix::Bin, Radix::Oct, Radix::Dec, Radix::Hex] {
            // min, max
            // for p2 < p1 rounding will cause overflow, for p2 >= p1 no rounding is needed.
            let rm = RoundingMode::None;
            for mut n in
                [BigFloatNumber::max_value(p1).unwrap(), BigFloatNumber::min_value(p1).unwrap()]
            {
                //println!("\n{:?} {} {}", rdx, p1, p2);
                //println!("{:?}", n);

                let s = n.format(rdx, rm).unwrap();
                let mut g = BigFloatNumber::parse(&s, rdx, p2, rm).unwrap();

                //println!("{:?}", g);

                if rdx == Radix::Dec {
                    eps.set_exponent(n.exponent() - p as Exponent + 3);
                    assert!(n.sub(&g, p, rm).unwrap().abs().unwrap().cmp(&eps) <= 0);
                } else {
                    if p2 < p1 {
                        n.set_precision(p, rm).unwrap();
                    } else if p2 > p1 {
                        g.set_precision(p, rm).unwrap();
                    }

                    assert!(n.cmp(&g) == 0);
                }
            }

            // min subnormal
            let rm = RoundingMode::ToEven;

            let mut n = BigFloatNumber::min_positive(p1).unwrap();
            let s = n.format(rdx, rm).unwrap();
            let mut g = BigFloatNumber::parse(&s, rdx, p2, rm).unwrap();

            if rdx == Radix::Dec {
                let mut eps = BigFloatNumber::min_positive(p).unwrap();
                eps.set_exponent(eps.exponent() + 2);
                assert!(n.sub(&g, p, rm).unwrap().abs().unwrap().cmp(&eps) < 0);
            } else {
                if p2 < p1 {
                    n.set_precision(p, rm).unwrap();
                } else if p2 > p1 {
                    g.set_precision(p, rm).unwrap();
                }
                assert!(n.cmp(&g) == 0);
            }
        }
    }
}
