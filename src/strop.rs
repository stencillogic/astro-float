//! BigFloatNumber formatting.

use crate::Sign;
use crate::defs::Radix;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::parser;
use crate::num::BigFloatNumber;
use std::fmt::Write;


const DIGIT_CHARS: [char; 16] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', ];

impl BigFloatNumber {

    /// Parses the number from the string `s` using radix `r`, precision `p`, and rounding mode `rm`.
    pub fn parse(s: &str, rdx: Radix, p: usize, rm: RoundingMode) -> Result<Self, Error> {

        let ps = parser::parse(s, rdx);

        if ps.is_valid() {
            let (m, s, e) = ps.raw_parts();
            BigFloatNumber::convert_from_radix(s, m, e, rdx, p, rm)
        } else {
            Err(Error::InvalidArgument)
        }
    }

    /// Formats the number using radix `r`.
    pub fn format(&self, rdx: Radix, rm: RoundingMode) -> Result<String, Error> {

        let (s, m, e) = self.convert_to_radix(rdx, rm)?;

        let mut mstr = if s == Sign::Neg {
            "-".to_owned()
        } else {
            String::new()
        };

        if m.is_empty() {

            mstr.push_str("0.0");

        } else {

            mstr.push(DIGIT_CHARS[m[0] as usize]);
            mstr.push('.');
            mstr.push_str(&m.iter().skip(1).map(|d| { DIGIT_CHARS[*d as usize] }).collect::<String>());

            if rdx == Radix::Hex {
                let _ = write!(mstr, "_");
            }

            if e < 1 {
                let _ = match rdx {
                    Radix::Bin => write!(mstr, "e-{:b}", (e - 1).unsigned_abs()),
                    Radix::Oct => write!(mstr, "e-{:o}", (e - 1).unsigned_abs()),
                    Radix::Dec => write!(mstr, "e-{}", (e - 1).unsigned_abs()),
                    Radix::Hex => write!(mstr, "e-{:x}", (e - 1).unsigned_abs()),
                };    
            } else {
                let _ = match rdx {
                    Radix::Bin => write!(mstr, "e+{:b}", e - 1),
                    Radix::Oct => write!(mstr, "e+{:o}", e - 1),
                    Radix::Dec => write!(mstr, "e+{}", e - 1),
                    Radix::Hex => write!(mstr, "e+{:x}", e - 1),
                };
            };
        }

        Ok(mstr)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_strop() {

        let mut eps = BigFloatNumber::from_word(1, 192).unwrap();

        for _ in 0..10000 {
            for rdx in [Radix::Bin, Radix::Oct, Radix::Hex, Radix::Dec] {

                let n = BigFloatNumber::random_normal(192, -2, -2).unwrap();
                let s = n.format(rdx, RoundingMode::ToEven).unwrap();
                let d = BigFloatNumber::parse(&s, rdx, 200, RoundingMode::ToEven).unwrap();
        
                if rdx == Radix::Dec {
                    //println!("\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}", n, s, d, n.format(Radix::Hex, RoundingMode::ToEven), d.format(Radix::Hex, RoundingMode::ToEven));
                    eps.set_exponent(n.get_exponent() - 160);
                    assert!(d.sub(&n, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);
                } else {
                    assert!(d.cmp(&n) == 0);
                }
            }
        }
    }
}
