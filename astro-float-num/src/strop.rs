//! BigFloatNumber formatting.

use crate::defs::Error;
use crate::defs::Radix;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::Consts;
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
    #[cfg(test)]
    pub fn parse(
        s: &str,
        rdx: Radix,
        p: usize,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<Self, Error> {
        let ps = crate::parser::parse(s, rdx)?;

        if ps.is_nan() || ps.is_inf() {
            Err(Error::InvalidArgument)
        } else {
            let (m, s, e) = ps.raw_parts();
            BigFloatNumber::convert_from_radix(s, m, e, rdx, p, rm, cc)
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
    pub fn format(&self, rdx: Radix, rm: RoundingMode, cc: &mut Consts) -> Result<String, Error> {
        let (s, m, e) = self.convert_to_radix(rdx, rm, cc)?;

        let mut mstr = String::new();
        let mstr_sz = 8
            + (self.mantissa_max_bit_len() + core::mem::size_of::<Exponent>() * 8)
                / match rdx {
                    Radix::Bin => 1,
                    Radix::Oct => 3,
                    Radix::Dec => 3,
                    Radix::Hex => 4,
                };

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
        let mut cc = Consts::new().unwrap();

        for i in 0..1000 {
            let p1 = (random::<usize>() % 32 + 3) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % 32 + 3) * WORD_BIT_SIZE;
            let p = p1.min(p2);

            let n = if i & 1 == 0 {
                BigFloatNumber::random_normal(p1, EXPONENT_MIN + p as Exponent, EXPONENT_MAX)
                    .unwrap()
            } else {
                random_subnormal(p1)
            };

            for rdx in [Radix::Bin, Radix::Oct, Radix::Hex] {
                let rm = match random::<u8>() % 7 {
                    0 => RoundingMode::ToEven,
                    1 => RoundingMode::Up,
                    2 => RoundingMode::Down,
                    3 => RoundingMode::FromZero,
                    4 => RoundingMode::ToZero,
                    5 => RoundingMode::ToOdd,
                    6 => RoundingMode::None,
                    _ => unreachable!(),
                };

                let s = n.format(rdx, rm, &mut cc).unwrap();
                let d = BigFloatNumber::parse(&s, rdx, p2, rm, &mut cc).unwrap();

                if p2 < p1 {
                    let mut x = n.clone().unwrap();
                    x.set_precision(p, rm).unwrap();
                    assert!(x.cmp(&d) == 0);
                } else {
                    assert!(n.cmp(&d) == 0);
                }
            }

            let s = n.format(Radix::Dec, RoundingMode::ToEven, &mut cc).unwrap();
            let d =
                BigFloatNumber::parse(&s, Radix::Dec, p2, RoundingMode::ToEven, &mut cc).unwrap();

            if i & 1 == 0 {
                eps.set_exponent(n.exponent() - p as Exponent + 4);
                assert!(
                    d.sub(&n, p, RoundingMode::None)
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
                    d.sub(&n, p, RoundingMode::None)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps2)
                        < 0
                );
            }
        }

        // MIN, MAX, min_positive
        let p1 = (random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
        let p = p1.min(p2);
        let rm = RoundingMode::None;

        for rdx in [Radix::Bin, Radix::Oct, Radix::Dec, Radix::Hex] {
            // min, max
            // for p2 < p1 rounding will cause overflow, for p2 >= p1 no rounding is needed.
            for mut n in
                [BigFloatNumber::max_value(p1).unwrap(), BigFloatNumber::min_value(p1).unwrap()]
            {
                //println!("\n{:?} {} {}", rdx, p1, p2);
                //println!("{:?}", n);

                let s = n.format(rdx, rm, &mut cc).unwrap();
                let mut g = BigFloatNumber::parse(&s, rdx, p2, rm, &mut cc).unwrap();

                //println!("{:?}", g);

                if rdx == Radix::Dec {
                    eps.set_exponent(n.exponent() - p as Exponent + 4); // 4, since rm is none
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
            let mut n = BigFloatNumber::min_positive(p1).unwrap();
            let s = n.format(rdx, rm, &mut cc).unwrap();
            let mut g = BigFloatNumber::parse(&s, rdx, p2, rm, &mut cc).unwrap();

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
