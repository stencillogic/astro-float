use crate::defs::DIGIT_BIT_SIZE;
use crate::defs::DIGIT_MAX;
use crate::defs::DIGIT_SIGNIFICANT_BIT;
/// BigFloatNumber formatting.

use crate::defs::Exponent;
use crate::defs::Radix;
use crate::defs::Error;
use crate::defs::Digit;
use crate::defs::RoundingMode;
use crate::parser::parse;
use crate::num::BigFloatNumber;


impl BigFloatNumber {
/*
    pub fn parse_base_10(s: &str) -> Result<Self, Error> {
        let ps = parse(s);
        if ps.is_valid() {
            if ps.is_inf() {
                Err(Error::ExponentOverflow(ps.sign()))
            } else if ps.is_nan() {
                Err(Error::InvalidArgument)
            } else {
                let (m, s, n) = ps.raw_parts();
                // input: u = f*10^n, f, n are integers.
                // output: v = m*2^e, where u is not precisely, but equal to v
                // Lets consider: v = f * 2^n * 5^n
                // 5^n is the only component that will introduce error, while f*2^n will result in precise number.
                // 5^n always ends with 1 for positive n and is periodic for negative n, so, though the rounded value of 5^n is not precise, 
                // we know the sticky bit is always 1 when doing rounding.
                // let a = 5^n = (x + err1)*2^n, and let b = f*2^n.
                // Assume |err1| <= 0.5
                // let a*b = (z + err2)*2^q
                // As per lemma 2 from "How to Read Floating Point Numbers Accurately", William D Clinger: 
                // |err2| < 0.5 + 2*err1 < 1.5
                // We want |err2| <= 0.5, so increasing precision by 2 (1.5/4 = 0.375)
                let rdx_num = Self::number_for_radix(Radix::Dec)?;
                let p = Self::precision_10_to_2(m.len());
                let mut digit: u32 = 0;
                let mut f = Self::new(p + 2)?;
                for d in m {
                    let d = *d as u32;
                    if digit <= core::u32::MAX - d {
                        digit *= 10;
                        digit += d;
                    } else {
                        let d2 = Self::from_u32(digit)?;
                        f = f.mul(&rdx_num)?;
                        f = f.add(&d2)?;
                        digit = 0;
                    }
                }
                if digit != 0 {
                    let d2 = Self::from_u32(digit)?;
                    f = f.mul(&rdx_num)?;
                    f = f.add(&d2)?;
                }
                let n = Self::from_u32(n)?;
                let fpn = Self::from_u8(5, p+2)?.pow(&n)?;
                let mut ret = fpn.mul(&f).round_mantissa(p)?;
                ret.set_exponent(ret.get_exponent() + e);
                Ok(ret)
            }
        } else {
            Err(Error::InvalidArgument)
        }
    }

    fn precision_10_to_2(len: usize) -> usize {
        if len == 0 {
            return 0;
        }
        const LG2_10: usize = 332192809488736234787031942948939017586;
        const DIV_FACTOR_MAX: usize = 100000000000000000000000000000000000000;
        let mut c = DIV_FACTOR_MAX;
        for _ in 1..len {
            c /= 10;
        }
        (LG2_10/c + 1)*len
    }

    /// Formats the number using radix `r`.
    pub fn format(&self, rdx: Radix) -> Result<String, Error> {
        // let self = m*2^e, m < 1, 
        // then self = m*2^e * rdx^n / rdx^n, where n = floor(e*log_r(2))
        // let f = m / rdx^n,
        // then resulting number is: F = f * rdx^n
        // F then will be printed with FP(3) from "How to Print Floating-Point Numbers Accurately", Guy L. Steele Jr., John L. White, 1990.
        Ok("".to_owned())
    }
*/

    // TODO: remove pub when printing is implemented.
    pub(super) fn fp3(&self, rdx: Radix, rm: RoundingMode) -> Result<Vec<u8>, Error> {
        let mut ret = Vec::new();
        ret.push(0);
        if !self.is_zero() {
            let mut r = self.clone()?;
            let one = Self::from_digit(1, 1)?;
            let mut m = one.clone()?;
            m.set_exponent(-(self.get_mantissa_max_bit_len() as Exponent + 1));
            let rdx_num = Self::number_for_radix(rdx)?;
            let mut digit;
            loop {
                let d = r.mul(&rdx_num, rm).unwrap();
                r = d.fract()?;
                digit = d.get_int_as_digit();
                m = m.mul(&rdx_num, rm).unwrap();
                ret.push(digit as u8);
                if r.cmp(&m) < 0 || r.cmp(&one.sub(&m, rm).unwrap()) > 0 {
                    break;
                }
            }
            if !r.round(0, RoundingMode::ToEven).unwrap().is_zero() {
                digit += 1;
                let rdx_digit = Self::digit_for_radix(rdx);
                if digit == rdx_digit {
                    ret.push(0);
                    let mut i = ret.len() - 2;
                    while i > 0 && ret[i] + 1 == rdx_digit as u8 {
                        ret[i] = 0;
                        i -= 1;
                    }
                    ret[i] += 1;
                } else {
                    ret.push(digit as u8);
                }
            }
        }
        Ok(ret)
    }

    fn digit_for_radix(rdx: Radix) -> Digit {
        match rdx {
            Radix::Bin => 2,
            Radix::Oct => 8,
            Radix::Dec => 10,
            Radix::Hex => 16,
        }
    }

    fn number_for_radix(rdx: Radix) -> Result<Self, Error> {
        let rdx_num = Self::digit_for_radix(rdx);
        Self::from_digit(rdx_num, 1)
    }
}


#[cfg(test)]
mod tests {

    use crate::{defs::{EXPONENT_MIN, EXPONENT_MAX}, Sign};

    use super::*;

    #[test]
    fn test_format() {

        let n = BigFloatNumber::from_f64(160, 0.03125f64).unwrap();
        println!("{:?}", n.fp3(Radix::Dec, RoundingMode::ToEven).unwrap());
    }
}
