//! Hyperbolic arcsine.

use crate::common::consts::FOURTY;
use crate::common::consts::ONE;
use crate::common::consts::SIX;
use crate::common::consts::THREE;
use crate::common::util::invert_rm_for_sign;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::Consts;
use crate::Sign;
use crate::EXPONENT_MAX;

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

        let mut x = self.clone()?;

        if self.is_zero() {
            x.set_precision(p, RoundingMode::None)?;
            return Ok(x);
        }

        if self.get_exponent() as isize >= -(p as isize) / 6 {
            if (self.get_exponent() as isize - 1) / 2 > self.get_mantissa_max_bit_len() as isize + 2
            {
                // asinh(x) = ln(2*|x|) * signum(x)
                if self.get_exponent() == EXPONENT_MAX {
                    Err(Error::ExponentOverflow(self.get_sign()))
                } else {
                    let mut x = self.clone()?;
                    x.set_sign(Sign::Pos);
                    x.set_exponent(x.get_exponent() + 1);

                    let rm = if self.is_negative() { invert_rm_for_sign(rm) } else { rm };

                    let mut ret = x.ln(p, rm, cc)?;

                    ret.set_sign(self.get_sign());

                    Ok(ret)
                }
            } else {
                // ln(|x| + sqrt(x*x + 1)) * signum(x)

                let p_x = p + self.get_exponent().unsigned_abs() as usize + 5;
                x.set_precision(p_x, RoundingMode::None)?;
                x.set_sign(Sign::Pos);

                let xx = x.mul(&x, p_x, RoundingMode::None)?;

                let d1 = xx.add(&ONE, p_x, RoundingMode::None)?;

                let d2 = d1.sqrt(p_x, RoundingMode::None)?;

                let d3 = d2.add(&x, p_x, RoundingMode::None)?;

                let mut ret = d3.ln(p_x, RoundingMode::None, cc)?;

                ret.set_sign(self.get_sign());
                ret.set_precision(p, rm)?;

                Ok(ret)
            }
        } else {
            // short series: x - x^3/6 + 3*x^5/40 - 5*x^7/112

            let p_x = p + 4;
            x.set_precision(p_x, RoundingMode::None)?;

            let xx = x.mul(&x, p_x, RoundingMode::None)?;
            let x3 = xx.mul(&x, p_x, RoundingMode::None)?;
            let p1 = x3.div(&SIX, p_x, RoundingMode::None)?;

            let mut ret = if p1.is_zero() {
                if rm as u32 & 0b11110 != 0 {
                    // since p1 it is too small there need to be an ajustment for flooring and ceiling rounding modes.
                    x.add_correction(true)
                } else {
                    Ok(x)
                }
            } else {
                x = x.sub(&p1, p_x, RoundingMode::None)?;

                let x5 = x3.mul(&xx, p_x, RoundingMode::None)?;
                let p2 = x5.mul(&THREE, p_x, RoundingMode::None)?;
                let p2 = p2.div(&FOURTY, p_x, RoundingMode::None)?;

                if p2.is_zero() {
                    if rm as u32 & 0b11110 != 0 {
                        // since p2 it is too small there need to be an ajustment for flooring and ceiling rounding modes.
                        x.add_correction(false)
                    } else {
                        Ok(x)
                    }
                } else {
                    x.add(&p2, p_x, RoundingMode::None)
                }
            }?;

            ret.set_precision(p, rm)?;

            Ok(ret)
        }
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
        let n1 = BigFloatNumber::parse("-6.2625AC139402BE3D18693E64BFF93D122A9FB2295D654817665874F984C1D9E32B6C42F068F33020_e-13", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.asinh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("-6.2625AC139402BE3D18693E64BFF93D122A9F8B69858A068F649D78ADAF2C51C59A22D727857055D8_e-13", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Hex, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // large exp
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e+1000", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.asinh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("2.C5DAB0AF9025886C3364C7B6D6741EB19D4FB009D3F92CA21B77498D9F0666363C665F2F324EAEC8_e+3", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Bin, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        let mut d1 = BigFloatNumber::max_value(p).unwrap();
        let mut d2 = BigFloatNumber::min_value(p).unwrap();
        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();

        assert!(d1.asinh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        assert!(d2.asinh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Neg));

        d1.set_exponent(d1.get_exponent() - 1);
        d2.set_exponent(d2.get_exponent() - 1);

        let mut eps = ONE.clone().unwrap();
        eps.set_exponent(
            d1.get_exponent() - p as Exponent + core::mem::size_of::<Exponent>() as Exponent * 8,
        );

        let d4 = d1.asinh(p, rm, &mut cc).unwrap();
        let d5 = d4.sinh(p, rm, &mut cc).unwrap();

        assert!(
            d1.sub(&d5, p, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );

        let d4 = d2.asinh(p, rm, &mut cc).unwrap();
        let d5 = d4.sinh(p, rm, &mut cc).unwrap();

        eps.set_exponent(
            d2.get_exponent() - p as Exponent + core::mem::size_of::<Exponent>() as Exponent * 8,
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
