//! Exponentiation.

use crate::{
    num::BigFloatNumber, 
    RoundingMode, 
    defs::{Error, EXPONENT_MIN, EXPONENT_MAX, Word, WORD_SIGNIFICANT_BIT, WORD_BIT_SIZE},
};


impl BigFloatNumber {

    /// Compute `e` to the power of self.
    pub fn exp(&self, rm: RoundingMode) -> Result<Self, Error> {

        if self.is_zero() {
            return Self::from_word(1, 1);
        }

        // compute separately for int and fract parts, then combine the results.
        let int = self.get_int_as_usize()?;
        let e_int = self.powi(int, rm)?;
        let fract = self.fract()?;
        let e_fract = fract.expf(rm)?;

        let ret = e_int.mul(&e_fract, rm)?;
        if self.is_negative() {
            ret.reciprocal(rm)
        } else {
            Ok(ret)
        }
    }

    /// Compute power of self to the integer.
    pub fn powi(&self, mut i: usize, rm: RoundingMode) -> Result<Self, Error> {

        if self.is_zero() || i == 1 {
            return self.clone();
        }

        if i == 0 {
            return Self::from_word(1, 1);
        }

        let mut bit_pos = WORD_BIT_SIZE;
        while bit_pos > 0 {
            bit_pos -= 1;
            i <<= 1;
            if i & WORD_SIGNIFICANT_BIT as usize != 0 {
                bit_pos -= 1;
                i <<= 1;
                break;
            }
        }

        // TODO: consider windowing and precomputed values.
        let mut ret = self.clone()?;
        while bit_pos > 0 {
            bit_pos -= 1;
            ret = ret.mul(&ret, rm)?;
            if i & WORD_SIGNIFICANT_BIT as usize != 0 {
                ret = ret.mul(self, rm)?;
            }
            i <<= 1;
        }

        Ok(ret)
    }

    // e^self for |self| < 1.
    fn expf(&self, rm: RoundingMode) -> Result<Self, Error> {
        let sh = Self::sinh(self, rm)?; // faster convergence than direct series
        // e = sh + sqrt(sh^2 + 1)
        let one = Self::from_word(1, 1)?;
        let sq = sh.mul(&sh, rm)?;
        let sq2 = sq.add(&one, rm)?;
        let sq3 = sq2.sqrt(rm)?;
        sq3.add(&sh, rm)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_pow() {

    }
}