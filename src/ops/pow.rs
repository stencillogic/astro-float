//! Exponentiation.

use crate::common::util::round_p;
use crate::ops::consts::Consts;
use crate::{
    common::consts::ONE,
    defs::{Error, WORD_BIT_SIZE, WORD_SIGNIFICANT_BIT},
    num::BigFloatNumber,
    RoundingMode, Sign,
};

impl BigFloatNumber {
    /// Computes `e` to the power of `self` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn exp(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        let mut ret = if self.is_negative() {
            let x = match self.exp_positive_arg(p, cc) {
                Ok(v) => Ok(v),
                Err(e) => match e {
                    Error::ExponentOverflow(_) => Self::new(p),
                    Error::DivisionByZero => Err(Error::DivisionByZero),
                    Error::InvalidArgument => Err(Error::InvalidArgument),
                    Error::MemoryAllocation(a) => Err(Error::MemoryAllocation(a)),
                },
            }?;

            if x.is_zero() {
                Ok(x)
            } else {
                x.reciprocal(x.get_mantissa_max_bit_len(), RoundingMode::None)
            }
        } else {
            self.exp_positive_arg(p, cc)
        }?;

        if rm as u32 & 0b11110 != 0 && ret.get_exponent() == 1 && ret.cmp(&ONE) == 0 {
            ret = ret.add_correction(self.is_negative())?;
        }

        ret.set_precision(p, rm)?;

        Ok(ret)
    }

    // exp for positive argument
    fn exp_positive_arg(&self, p: usize, cc: &mut Consts) -> Result<Self, Error> {
        if self.is_zero() {
            return Self::from_word(1, p);
        }

        if self.e as isize > WORD_BIT_SIZE as isize {
            return Err(Error::ExponentOverflow(self.get_sign()));
        }

        let p_work = p + 4;

        // compute separately for int and fract parts, then combine the results.
        let int = self.get_int_as_usize()?;
        let e_int = if int > 0 {
            let e_const = cc.e(p_work, RoundingMode::None)?;

            e_const.powi(int, p_work, RoundingMode::None)
        } else {
            ONE.clone()
        }?;

        let mut fract = self.fract()?;
        fract.set_precision(p_work, RoundingMode::None)?;
        fract.set_sign(Sign::Pos);
        let e_fract = fract.expf(RoundingMode::None)?;

        e_int.mul(&e_fract, p_work, RoundingMode::None)
    }

    /// Compute the power of `self` to the integer `n` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn powi(&self, n: usize, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        let mut i = n;
        if self.is_zero() || i == 1 {
            let mut ret = self.clone()?;
            ret.set_precision(p, rm)?;
            return Ok(ret);
        }

        if i == 0 {
            return Self::from_word(1, p);
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

        let p = round_p(p);

        let mut x = self.clone()?;

        let p_x = p + bit_pos * 2;
        x.set_precision(p_x, RoundingMode::None)?;

        let mut ret = || -> Result<Self, Error> {
            // TODO: consider windowing and precomputed values.
            while bit_pos > 0 {
                bit_pos -= 1;
                x = x.mul(&x, p_x, RoundingMode::None)?;
                if i & WORD_SIGNIFICANT_BIT as usize != 0 {
                    x = x.mul(self, p_x, RoundingMode::None)?;
                }
                i <<= 1;
            }

            Ok(x)
        }()
        .map_err(|e| -> Error {
            if let Error::ExponentOverflow(_) = e {
                Error::ExponentOverflow(if self.is_negative() && (n & 1 == 1) {
                    Sign::Neg
                } else {
                    Sign::Pos
                })
            } else {
                e
            }
        })?;

        ret.set_precision(p, rm)?;

        Ok(ret)
    }

    // e^self for |self| < 1.
    fn expf(self, rm: RoundingMode) -> Result<Self, Error> {
        let p = self.get_mantissa_max_bit_len();

        let sh = self.sinh_series(p, rm, false)?; // faster convergence than direct series

        // e = sh + sqrt(sh^2 + 1)
        let sq = sh.mul(&sh, p, rm)?;
        let sq2 = sq.add(&ONE, p, rm)?;
        let sq3 = sq2.sqrt(p, rm)?;
        sq3.add(&sh, p, rm)
    }

    /// Compute the power of `self` to the `n` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: `self` is negative, or the precision is incorrect.
    pub fn pow(
        &self,
        n: &Self,
        p: usize,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<Self, Error> {
        if self.is_negative() {
            return Err(Error::InvalidArgument);
        } else if self.is_zero() {
            return if n.is_negative() {
                Err(Error::ExponentOverflow(Sign::Pos))
            } else if n.is_zero() {
                Self::from_word(1, p)
            } else {
                Self::new(p)
            };
        } else if self.get_exponent() == 1 && self.cmp(&ONE) == 0 {
            return Self::from_word(1, p);
        } else if n.get_exponent() == 1 && n.abs_cmp(&ONE) == 0 {
            if n.is_positive() {
                let mut ret = self.clone()?;
                ret.set_precision(p, rm)?;
                return Ok(ret);
            } else {
                return self.reciprocal(p, rm);
            }
        }

        let p = round_p(p);

        // self^n = e^(n * ln(self))

        let p_ext = p + 1;
        let mut x = self.clone()?;
        x.set_precision(p_ext, RoundingMode::None)?;

        let ln = x.ln(p_ext, RoundingMode::None, cc)?;

        let m = match n.mul(&ln, p_ext, RoundingMode::None) {
            Ok(v) => Ok(v),
            Err(e) => match e {
                Error::ExponentOverflow(Sign::Neg) => {
                    return Self::new(p);
                }
                Error::ExponentOverflow(Sign::Pos) => Err(Error::ExponentOverflow(Sign::Pos)),
                Error::DivisionByZero => Err(Error::DivisionByZero),
                Error::InvalidArgument => Err(Error::InvalidArgument),
                Error::MemoryAllocation(a) => Err(Error::MemoryAllocation(a)),
            },
        }?;

        m.exp(p, rm, cc)
    }
}

#[cfg(test)]
mod test {

    use crate::common::{consts::TWO, util::random_subnormal};

    use super::*;

    #[test]
    fn test_power() {
        let mut cc = Consts::new().unwrap();

        // near 1
        let p = 320;
        let d1 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC4872DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.exp(p, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse(
            "2.B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A5496AF9D95160A40F47A2ECF1C6AEA0",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        let d1 = BigFloatNumber::parse(
            "1.00000000000000000000000000000000000000000000000000000000000000002DC85F7E77EC487C",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.exp(p, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse(
            "2.B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEFAEC1BE22DDEADB48",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        // random subnormal
        let d1 = random_subnormal(p);
        assert!(d1.exp(p, RoundingMode::ToEven, &mut cc).unwrap().cmp(&ONE) == 0);

        // pow(small, small)
        let p = 256;
        let mut d1 = BigFloatNumber::parse("1.10010100010011110010001011101010010101111000010101010100010010111001000100011101010111011010110011011111110000010010101000110001001000000101000010101111001100110111100011101000110001001000000101000010101111001100110111100011101010011101101", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d1.set_exponent(-123456);
        let mut d2 = BigFloatNumber::parse("1.00110001001000010100001010111100110011011110001110101001110110100000101000010010101111000010110010100010011110010001011101010101010001001011100110111111100100010001110101011101101011000001001010100101111001100110111100011101000110001001000", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d2.set_exponent(-123);
        let d3 = d1.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap();
        let d4 = BigFloatNumber::parse("1.111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111100111000110010011110111100111111100111010011001110010010110010100100110010110111110110100011010000110110011010111101110000011100011010100110100000001e-1", crate::Radix::Bin, p, RoundingMode::None).unwrap();

        assert!(d4.cmp(&d3) == 0);

        // pow(large, small)
        let mut d1 = BigFloatNumber::parse("1.10010100010011110010001011101010010101111000010101010100010010111001000100011101010111011010110011011111110000010010101000110001001000000101000010101111001100110111100011101000110001001000000101000010101111001100110111100011101010011101101", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d1.set_exponent(123456);
        let mut d2 = BigFloatNumber::parse("1.00110001001000010100001010111100110011011110001110101001110110100000101000010010101111000010110010100010011110010001011101010101010001001011100110111111100100010001110101011101101011000001001010100101111001100110111100011101000110001001000", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d2.set_exponent(-123);
        let d3 = d1.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap();
        let d4 = BigFloatNumber::parse("1.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110001110011010111001000101100100101011011111001101101011011010100101111001001000010000010100110110011000001011011111000000000010111010000010110111", crate::Radix::Bin, p, RoundingMode::None).unwrap();

        assert!(d4.cmp(&d3) == 0);

        // pow(>~1, large)
        let d1 = BigFloatNumber::parse("1.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110001110011010111001000101100100101011011111001101101011011010100101111001001000010000010100110110011000001011011111000000000010111010000010110111", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        let mut d2 = BigFloatNumber::parse("1.00110001001000010100001010111100110011011110001110101001110110100000101000010010101111000010110010100010011110010001011101010101010001001011100110111111100100010001110101011101101011000001001010100101111001100110111100011101000110001001000", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d2.set_exponent(123);
        let d3 = d1.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap();
        let d4 = BigFloatNumber::parse("1.000011101011111010010100111000101101011001100110110100101011001110100110011011100100100101011100010100011101011111010011100011010000110001100111001011000001111110001110000110000000101101011001010001000011011001000010001110000100110000110011111100000001e+1010101101000111", crate::Radix::Bin, p, RoundingMode::None).unwrap();

        assert!(d4.cmp(&d3) == 0);

        // pow(<~1, large)
        let d1 = BigFloatNumber::parse("0.1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110001110011010111001000101100100101011011111001101101011011010100101111001001000010000010100110110011000001011011111000000000010111010000010110111", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        let mut d2 = BigFloatNumber::parse("1.00110001001000010100001010111100110011011110001110101001110110100000101000010010101111000010110010100010011110010001011101010101010001001011100110111111100100010001110101011101101011000001001010100101111001100110111100011101000110001001000", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d2.set_exponent(123);
        let d3 = d1.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap();
        let d4 = BigFloatNumber::parse("1.010011011001100100100000101011101001110011001100011001011011010010101111101100111101011010101101101111100111001001001101000111110001010010111101110010011100001011011111001111001001001100100111010100100010010111011011110010110101110000100111001100100000011e-110000110100111100", crate::Radix::Bin, p, RoundingMode::None).unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        assert!(d4.cmp(&d3) == 0);

        // max, min, subnormal
        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();
        let d3 = BigFloatNumber::min_positive(p).unwrap();

        assert!(
            d1.exp(p, RoundingMode::ToEven, &mut cc).unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        assert!(
            d1.pow(&d1, p, RoundingMode::ToEven, &mut cc).unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        assert!(d1
            .pow(&d2, p, RoundingMode::ToEven, &mut cc)
            .unwrap()
            .is_zero());
        assert!(
            d1.pow(&d3, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );

        assert!(d2.exp(p, RoundingMode::ToEven, &mut cc).unwrap().is_zero());

        assert!(d3.exp(p, RoundingMode::ToEven, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(d3
            .pow(&d1, p, RoundingMode::ToEven, &mut cc)
            .unwrap()
            .is_zero());
        assert!(
            d3.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        assert!(
            d3.pow(&d3, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );

        assert!(
            d1.pow(&ONE, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&d1)
                == 0
        );
        assert!(
            d3.pow(&ONE, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&d3)
                == 0
        );
        assert!(
            ONE.pow(&d1, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );
        assert!(
            ONE.pow(&d2, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );
        assert!(
            ONE.pow(&d3, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );

        let rm = RoundingMode::ToOdd;
        let d1 = TWO.pow(&ONE.neg().unwrap(), p, rm, &mut cc).unwrap();
        let d2 = TWO.reciprocal(p, rm).unwrap();

        assert!(d1.cmp(&d2) == 0);
    }
}
