//! Hyperbolic cocosine.

use crate::common::consts::ONE;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::util::compute_small_exp;
use crate::Consts;
use crate::Sign;
use crate::WORD_BIT_SIZE;

impl BigFloatNumber {
    /// Computes the hyperbolic cosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache cc for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn cosh(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            let mut ret = Self::from_word(1, p)?;
            ret.set_inexact(self.inexact());
            return Ok(ret);
        }

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p.max(self.mantissa_max_bit_len());

        compute_small_exp!(ONE, self.exponent() as isize * 2 - 1, false, p_wrk, p, rm);

        p_wrk += p_inc;

        let mut x = self.clone()?;
        x.set_inexact(false);

        loop {
            let p_x = p_wrk + 4;
            x.set_precision(p_x, RoundingMode::None)?;

            x.set_sign(Sign::Pos);

            let mut ret = if (x.exponent() as isize - 1) * 2 > x.mantissa_max_bit_len() as isize + 2
            {
                // e^x / 2

                x.exp(p_x, RoundingMode::None, cc)
            } else {
                // (e^x + e^(-x)) / 2

                let ex = x.exp(p_x, RoundingMode::None, cc)?;

                let xe = ex.reciprocal(p_x, RoundingMode::None)?;

                ex.add(&xe, p_x, RoundingMode::None)
            }?;

            ret.div_by_2(RoundingMode::None);

            if ret.try_set_precision(p, rm, p_wrk)? {
                ret.set_inexact(ret.inexact() | self.inexact());
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
    fn test_cosh() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, p).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.cosh(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        // asymptotic & extrema testing
        let p = 640;
        let n1 = BigFloatNumber::parse(
            "1.0111001e-1000000",
            crate::Radix::Bin,
            p,
            RoundingMode::None,
            &mut cc,
        )
        .unwrap();
        let n2 = n1.cosh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.000000000000000000000000000000010B6200000000000000000000000000002E8B9840AAAAAAAAAAAAAAAAAAAAAAAAADE85C5950B78E38E38E38E38E38E38E3902814A92D7C21CDB6DB6DB6DB6DB6E_e+0", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();

        assert!(n2.cmp(&n3) == 0);

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();

        assert!(d1.cosh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        assert!(d2.cosh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Pos));

        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();
        let d4 = random_subnormal(p);

        assert!(d3.cosh(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(zero.cosh(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(d4.cosh(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn cosh_perf() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, -20, 20).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.cosh(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
