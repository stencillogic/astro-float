//! Hyperbolic sine.

use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::util::compute_small_exp;
use crate::Consts;
use crate::Sign;
use crate::WORD_BIT_SIZE;

impl BigFloatNumber {
    /// Computes the hyperbolic sine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache cc for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn sinh(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            let mut ret = Self::new(p)?;
            ret.set_sign(self.get_sign());
            return Ok(ret);
        }

        compute_small_exp!(self, self.get_exponent() as isize - 2, false, p, rm);

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        loop {
            let mut x = self.clone()?;
            x.set_precision(p_wrk + 4, RoundingMode::None)?;

            x.set_sign(Sign::Pos);

            let mut ret = if (x.get_exponent() as isize - 1) / 2
                > x.get_mantissa_max_bit_len() as isize + 2
            {
                // e^|x| / 2 * signum(x)

                x.exp(p_wrk, RoundingMode::None, cc)
            } else {
                // (e^x - e^(-x)) / 2

                let ex = x.exp(p_wrk, RoundingMode::None, cc)?;

                let xe = ex.reciprocal(p_wrk, RoundingMode::None)?;

                ex.sub(&xe, p_wrk, RoundingMode::None)
            }
            .map_err(|e| -> Error {
                if let Error::ExponentOverflow(_) = e {
                    Error::ExponentOverflow(self.get_sign())
                } else {
                    e
                }
            })?;

            ret.div_by_2(RoundingMode::None);

            ret.set_sign(self.get_sign());

            if ret.try_set_precision(p, rm, p_wrk)? {
                break Ok(ret);
            }

            p_wrk += p_inc;
            p_inc = round_p(p_wrk / 5);
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::{common::util::random_subnormal, Sign};

    use super::*;

    #[test]
    fn test_sinh() {
        let p = 32000;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, 1).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.sinh(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.fp3(crate::Radix::Dec, rm).unwrap());

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();

        assert!(d1.sinh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        assert!(d2.sinh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Neg));

        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();
        let n1 = random_subnormal(p);

        assert!(d3.sinh(p, rm, &mut cc).unwrap().cmp(&d3) == 0);
        assert!(zero.sinh(p, rm, &mut cc).unwrap().is_zero());
        assert!(n1.sinh(p, rm, &mut cc).unwrap().cmp(&n1) == 0);
    }
}
