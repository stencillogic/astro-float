//! Exponentiation.

use crate::{
    num::BigFloatNumber, 
    RoundingMode, 
    defs::{Error, WORD_SIGNIFICANT_BIT, WORD_BIT_SIZE}, 
    common::consts::ONE, Sign,
};
use crate::ops::consts::Consts;


impl BigFloatNumber {

    /// Computes `e` to the power of `self`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn exp(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        if self.is_zero() {
            return Self::from_word(1, self.get_mantissa_max_bit_len());
        }

        if self.e as isize > WORD_BIT_SIZE as isize {
            return Err(Error::ExponentOverflow(self.get_sign()));
        }

        // compute separately for int and fract parts, then combine the results.
        let int = self.get_int_as_usize()?;
        let e_int = if int > 0 {

            let e_const = cc.e(self.get_mantissa_max_bit_len() + 2 + 2*core::mem::size_of::<usize>(), RoundingMode::None)?;

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

    /// Compute the power of `self` to the integer `i`. The result is rounded using the rounding mode `rm`.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
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
    fn expf(self, rm: RoundingMode) -> Result<Self, Error> {

        let sh = self.sinh_series(rm)?; // faster convergence than direct series

        // e = sh + sqrt(sh^2 + 1)
        let sq = sh.mul(&sh, rm)?;
        let sq2 = sq.add(&ONE, rm)?;
        let sq3 = sq2.sqrt(rm)?;
        sq3.add(&sh, rm)
    }

    /// Compute the power of `self` to the `n`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: `self` is negative.
    pub fn pow(&self, n: &Self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        if self.is_negative() {
            return Err(Error::InvalidArgument);
        }

        if self.is_zero() {
            return if n.is_negative() {
                Err(Error::ExponentOverflow(Sign::Pos))
            } else if n.is_zero() {
                Self::from_word(1, self.get_mantissa_max_bit_len())
            } else {
                self.clone()
            };
        }

        // self^n = e^(n * ln(self))

        let mut x = self.clone()?;
        x.set_precision(x.get_mantissa_max_bit_len() + 1, RoundingMode::None)?;

        let ln = x.ln(RoundingMode::None, cc)?;
        let m = n.mul(&ln, RoundingMode::None)?;
        let mut ret = m.exp(RoundingMode::None, cc)?;

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }

}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn test_pow() {

        let mut cc = Consts::new().unwrap();

        // near 1
        let d1 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC4872DC85F7E77EC487_e-1", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let d2 = d1.exp(RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse("2.B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A5496AF9D95160A40F47A2ECF1C6AEA0", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        let d1 = BigFloatNumber::parse("1.00000000000000000000000000000000000000000000000000000000000000002DC85F7E77EC487C", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let d2 = d1.exp(RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse("2.B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEFAEC1BE22DDEADB48", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);
    }
}