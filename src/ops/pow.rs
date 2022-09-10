//! Exponentiation.

use crate::{
    num::BigFloatNumber, 
    RoundingMode, 
    defs::{Error, WORD_SIGNIFICANT_BIT, WORD_BIT_SIZE}, 
    common::consts::ONE, Sign,
};
use crate::ops::consts::std::E;


impl BigFloatNumber {

    /// Compute `e` to the power of self.
    pub fn exp(&self, rm: RoundingMode) -> Result<Self, Error> {

        if self.is_zero() {
            return Self::from_word(1, self.get_mantissa_max_bit_len());
        }

        // compute separately for int and fract parts, then combine the results.
        let int = self.get_int_as_usize()?;
        let e_int = if int > 0 {

            let e_const = E.with(|v| -> Result<Self, Error> {
                v.borrow_mut().for_prec(self.get_mantissa_max_bit_len() + 2, RoundingMode::None)
            })?;

            e_const.powi(int, RoundingMode::None)
        } else {
            ONE.clone()
        }?;

        let mut fract = self.fract()?;
        fract.set_precision(fract.get_mantissa_max_bit_len() + 4, RoundingMode::None)?;
        fract.set_sign(Sign::Pos);
        let e_fract = fract.expf(RoundingMode::None)?;

        let mut ret = e_int.mul(&e_fract, RoundingMode::None)?;
        if self.is_negative() {
            ret = ret.reciprocal(RoundingMode::None)?;
        };

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }

    /// Compute power of self to the integer.
    pub fn powi(&self, mut i: usize, rm: RoundingMode) -> Result<Self, Error> {

        if self.is_zero() || i == 1 {
            return self.clone();
        }

        if i == 0 {
            return Self::from_word(1, self.get_mantissa_max_bit_len());
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

        let sh = self.sinh_series(rm)?; // faster convergence than direct series

        // e = sh + sqrt(sh^2 + 1)
        let sq = sh.mul(&sh, rm)?;
        let sq2 = sq.add(&ONE, rm)?;
        let sq3 = sq2.sqrt(rm)?;
        sq3.add(&sh, rm)
    }
}

