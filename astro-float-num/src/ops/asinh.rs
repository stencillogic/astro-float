//! Hyperbolic arcsine.

use crate::common::consts::ONE;
use crate::common::util::invert_rm_for_sign;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::util::compute_small_exp;
use crate::Consts;
use crate::Sign;
use crate::EXPONENT_MAX;
use crate::WORD_BIT_SIZE;

impl BigFloatNumber {
    /// Computes the hyperbolic arcsine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn asinh(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            return Self::new2(p, self.sign(), self.inexact());
        }

        compute_small_exp!(self, self.exponent() as isize * 2 - 2, true, p, rm);

        let mut x = self.clone()?;

        x.set_sign(Sign::Pos);

        let rm = if self.is_negative() { invert_rm_for_sign(rm) } else { rm };

        let mut ret =
            if (self.exponent() as isize - 1) / 2 > self.mantissa_max_bit_len() as isize + 2 {
                // asinh(x) = ln(2 * |x|) * signum(x)

                if self.exponent() == EXPONENT_MAX {
                    // ln(2 * |x|) = ln(2) + ln(|x|)
                    let mut p_inc = WORD_BIT_SIZE;
                    let mut p_wrk = p.max(self.mantissa_max_bit_len()) + p_inc;

                    loop {
                        let p_x = p_wrk + 2;

                        let lnx = x.ln(p_x, RoundingMode::None, cc)?;

                        let ln2 = cc.ln_2_num(p_x, RoundingMode::None)?;

                        let mut ret = ln2.add(&lnx, p_x, RoundingMode::None)?;

                        if ret.try_set_precision(p, rm, p_wrk)? {
                            break Ok(ret);
                        }

                        p_wrk += p_inc;
                        p_inc = round_p(p_wrk / 5);
                    }
                } else {
                    x.set_exponent(x.exponent() + 1);

                    x.ln(p, rm, cc)
                }
            } else {
                // ln(|x| + sqrt(x*x + 1)) * signum(x)

                let mut p_inc = WORD_BIT_SIZE;
                let mut p_wrk = p.max(self.mantissa_max_bit_len()) + p_inc;

                loop {
                    let p_x = p_wrk + self.exponent().unsigned_abs() as usize + 5;
                    x.set_precision(p_x, RoundingMode::None)?;

                    let xx = x.mul(&x, p_x, RoundingMode::None)?;

                    let d1 = xx.add(&ONE, p_x, RoundingMode::None)?;

                    let d2 = d1.sqrt(p_x, RoundingMode::None)?;

                    let d3 = d2.add(&x, p_x, RoundingMode::FromZero)?;

                    let mut ret = d3.ln(p_x, RoundingMode::None, cc)?;

                    if ret.try_set_precision(p, rm, p_wrk)? {
                        break Ok(ret);
                    }

                    p_wrk += p_inc;
                    p_inc = round_p(p_wrk / 5);
                }
            }?;

        ret.set_sign(self.sign());

        Ok(ret)
    }
}

#[cfg(test)]
mod tests {

    use crate::{common::util::random_subnormal, Exponent};

    use super::*;

    #[test]
    fn test_asinh() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, p).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.asinh(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // near zero
        let n1 = BigFloatNumber::parse("-6.2625AC139402BE3D18693E64BFF93D122A9FB2295D654817665874F984C1D9E32B6C42F068F33020_e-13", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();
        let n2 = n1.asinh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("-6.2625AC139402BE3D18693E64BFF93D122A9F8B69858A068F649D78ADAF2C51C59A22D727857055D8_e-13", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Hex, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // large exp
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e+1000", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();
        let n2 = n1.asinh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("2.C5DAB0AF9025886C3364C7B6D6741EB19D4FB009D3F92CA21B77498D9F0666363C665F2F324EAEC8_e+3", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Bin, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();
        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();

        let mut eps = ONE.clone().unwrap();
        eps.set_exponent(
            d1.exponent() - p as Exponent + core::mem::size_of::<Exponent>() as Exponent * 8,
        );

        let mut d4 = d1.asinh(p, rm, &mut cc).unwrap();
        // avoid overflow using sinh(x) = 2 * sinh(x/2)^2
        d4.set_exponent(d4.exponent() - 1);
        let tmp = d4.sinh(p + 1, RoundingMode::None, &mut cc).unwrap();
        let mut d5 = tmp.mul(&tmp, p, rm).unwrap();
        d5.set_exponent(d5.exponent() + 1);

        assert!(
            d1.sub(&d5, p, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );

        let mut d4 = d2.asinh(p, rm, &mut cc).unwrap();
        // avoid overflow using sinh(x) = 2 * sinh(x/2)^2
        d4.set_exponent(d4.exponent() - 1);
        let tmp = d4.sinh(p + 1, RoundingMode::None, &mut cc).unwrap();
        let mut d5 = tmp.mul(&tmp, p, rm).unwrap();
        d5.set_exponent(d5.exponent() + 1);
        d5.set_sign(Sign::Neg);

        eps.set_exponent(
            d2.exponent() - p as Exponent + core::mem::size_of::<Exponent>() as Exponent * 8,
        );

        assert!(
            d2.sub(&d5, p, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );

        assert!(d3.asinh(p, rm, &mut cc).unwrap().cmp(&d3) == 0);
        assert!(zero.asinh(p, rm, &mut cc).unwrap().is_zero());

        // subnormal arg
        let n1 = random_subnormal(p);
        assert!(n1.asinh(p, rm, &mut cc).unwrap().cmp(&n1) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn asinh_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        let p = 160;
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.asinh(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
