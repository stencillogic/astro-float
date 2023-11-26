//! Hyperbolic arctangent.

use crate::common::consts::ONE;
use crate::common::util::count_leading_ones;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::ops::util::compute_small_exp;
use crate::WORD_BIT_SIZE;

impl BigFloatNumber {
    /// Computes the hyperbolic arctangent of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: when |`self`| > 1, or the precision is incorrect.
    pub fn atanh(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            let mut ret = self.clone()?;
            ret.set_precision(p, RoundingMode::None)?;
            return Ok(ret);
        }

        if self.exponent() == 1 {
            if self.abs_cmp(&ONE) == 0 {
                return Err(Error::ExponentOverflow(self.sign()));
            } else {
                return Err(Error::InvalidArgument);
            }
        } else if self.exponent() > 1 {
            return Err(Error::InvalidArgument);
        }

        compute_small_exp!(self, self.exponent() as isize * 2 - 1, false, p, rm);

        // 0.5 * ln((1 + x) / (1 - x))

        let mut additional_prec = 4;
        if self.exponent() < 0 {
            additional_prec += self.exponent().unsigned_abs() as usize;
        } else {
            additional_prec += count_leading_ones(self.mantissa().digits());
        }

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p.max(self.mantissa_max_bit_len()) + p_inc;

        let mut x = self.clone()?;

        loop {
            let p_x = p_wrk + additional_prec;
            x.set_precision(p_x, RoundingMode::None)?;

            let d1 = ONE.add(&x, p_x, RoundingMode::None)?;
            let d2 = ONE.sub(&x, p_x, RoundingMode::None)?;

            let d3 = d1.div(&d2, p_x, RoundingMode::None)?;

            let mut ret = d3.ln(p_x, RoundingMode::None, cc)?;

            ret.div_by_2(RoundingMode::None);

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
    fn test_atanh() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, p).unwrap();
        n1.set_exponent(-34);
        let _n2 = n1.atanh(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        let mut n1 = BigFloatNumber::from_word(1, p).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.atanh(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        // asymptotic & extrema testing
        let p = 640;
        let n1 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8EE51946EC87F86A7E6DA4D8C6ED8DFAE4D7B7FF0B8356E63EF277C97F2E2111AECCBE8F2DF4EFE48F618B1E75C7CBBDCFCE32604DE9F240_e-1", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();
        let n2 = n1.atanh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("4.34C10E83FA43CA88E0A3A0125990D4B8BC2CF39E0695A6B9F73DE8F43C00767B966992C0A98F96AAC882152114C2FE89AD58DA3BA9E2013CAD88370B80F7D9AD4D9B6494C0591D3CAA382BF6FBD88730_e+1", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();

        assert!(n2.cmp(&n3) == 0);

        // small value
        let p = 320;
        let n1 = BigFloatNumber::parse("7.C3A95633A7BFB754F49F839BCFDED202E43C4EEB4E6CC1292F4751559BBC55E859642CBB19881B10_e-F", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();
        let n2 = n1.atanh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("7.C3A95633A7BFB754F49F839BCFDF6E088C51BE9FAF9B30BC9499ABD8AFDA2F9E0F9B97FBDB228480_e-f", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Bin, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();

        assert!(d1.atanh(p, rm, &mut cc).unwrap_err() == Error::InvalidArgument);
        assert!(d2.atanh(p, rm, &mut cc).unwrap_err() == Error::InvalidArgument);

        // subnormal
        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();

        assert!(d3.atanh(p, rm, &mut cc).unwrap().cmp(&d3) == 0);
        assert!(zero.atanh(p, rm, &mut cc).unwrap().is_zero());

        assert!(ONE.atanh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        assert!(
            ONE.neg().unwrap().atanh(p, rm, &mut cc).unwrap_err()
                == Error::ExponentOverflow(Sign::Neg)
        );

        let n1 = random_subnormal(p);
        assert!(n1.atanh(p, rm, &mut cc).unwrap().cmp(&n1) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn atanh_perf() {
        let p = 160;
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.atanh(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
