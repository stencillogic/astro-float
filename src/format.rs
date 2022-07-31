/// BigFloatNumber formatting.

use crate::defs::Exponent;
use crate::defs::Radix;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;


impl BigFloatNumber {

    /// Formats the number using radix `r`.
    pub fn format(&self, rdx: Radix) -> Result<String, Error> {
        // let self = m*2^e, m < 1, 
        // then self = m*2^e * rdx^n / rdx^n, where n = floor(e*log_r(2))
        // let f = m / rdx^n,
        // then resulting number is: F = f * rdx^n
        // F then will be printed with FP(3) from "How to Print Floating-Point Numbers Accurately", Guy L. Steele Jr., John L. White, 1990.
        Ok("".to_owned())
    }

    fn fp3(&self, rdx: Radix) -> Result<String, Error> {
        let mut ret = String::new();
        if self.is_zero() {
            ret = "0.0".to_owned();
        } else {
            let mut r = self.clone()?;
            let one = Self::one(1)?;
            let mut m = one.clone()?;
            m.set_exponent(-(self.get_mantissa_max_bit_len() as Exponent + 1));
            let rdx_num = Self::number_for_radix(rdx)?;
            let mut digit;
            loop {
                let d = r.mul(&rdx_num).unwrap();
                r = d.fract()?;
                digit = d.get_int_as_digit();
                m = m.mul(&rdx_num).unwrap();
                if r.cmp(&m) < 0 || r.cmp(&one.sub(&m).unwrap()) > 0 {
                    break;
                }
                ret.push(std::char::from_digit(digit as u32, rdx as u32).unwrap());
            }
            if !r.round(0, RoundingMode::ToEven).unwrap().is_zero() {
                digit += 1;
            }
            ret.push(std::char::from_digit(digit as u32, rdx as u32).unwrap());
        }
        Ok(ret)
    }

    fn number_for_radix(rdx: Radix) -> Result<Self, Error> {
        match rdx {
            Radix::Bin => Self::one_shifted(1),
            Radix::Oct => Self::one_shifted(3),
            Radix::Dec => Self::ten(4),
            Radix::Hex => Self::one_shifted(4),
        }
    }

    fn one_shifted(n: Exponent) -> Result<Self, Error> {
        let one = Self::one(1)?;
        let mut ret = one.clone()?;
        ret.set_exponent(one.get_exponent() + n); 
        Ok(ret)
    }
}


#[cfg(test)]
mod tests {

    use crate::defs::{EXPONENT_MIN, EXPONENT_MAX};

    use super::*;

    #[test]
    fn test_format() {
        let n = BigFloatNumber::from_f64(160, 0.3).unwrap();
        println!("{}", n.fp3(Radix::Dec).unwrap());
    }
}
