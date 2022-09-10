
use crate::Sign;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_MAX;
use crate::defs::WORD_SIGNIFICANT_BIT;
/// BigFloatNumber formatting.

use crate::defs::Exponent;
use crate::defs::Radix;
use crate::defs::Error;
use crate::defs::Word;
use crate::defs::RoundingMode;
use crate::parser::parse;
use crate::num::BigFloatNumber;
use crate::common::consts::ONE;
use crate::common::consts::TWO;
use crate::common::consts::EIGHT;
use crate::common::consts::TEN;
use crate::common::consts::SIXTEEN;
use std::fmt::Write;


const DIGIT_CHARS: [char; 16] = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', ];

impl BigFloatNumber {

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

            if e < 1 {
                let _ = write!(mstr, "e-{}", (e - 1).unsigned_abs());
            } else {
                let _ = write!(mstr, "e+{}", e - 1);
            }
        }

        Ok(mstr)
    }
}


#[cfg(test)]
mod tests {

    use crate::{defs::{EXPONENT_MIN, EXPONENT_MAX}, Sign};

    use super::*;

    #[test]
    fn test_format() {

        let n = BigFloatNumber::from_f64(160, 0.03f64).unwrap();
        let s = n.format(Radix::Dec, RoundingMode::None).unwrap();
        //println!("{}", s);
    }
}
