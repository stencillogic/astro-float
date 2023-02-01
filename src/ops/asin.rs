//! Arcsine.

use crate::common::consts::FOURTY;
use crate::common::consts::ONE;
use crate::common::consts::SIX;
use crate::common::consts::THREE;
use crate::common::util::count_leading_ones;
use crate::common::util::invert_rm_for_sign;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::WORD_BIT_SIZE;

impl BigFloatNumber {
    /// Computes the arcsine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: argument is greater than 1 or smaller than -1, or the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn asin(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            let mut ret = Self::new(p)?;
            ret.set_sign(self.get_sign());
            return Ok(ret);
        }

        let onecmp = self.abs_cmp(&ONE);
        if onecmp > 0 {
            return Err(Error::InvalidArgument);
        } else if onecmp == 0 {
            let rm = if self.is_negative() { invert_rm_for_sign(rm) } else { rm };

            let mut pi = cc.pi_num(p, rm)?;

            pi.set_exponent(pi.get_exponent() - 1);
            pi.set_sign(self.get_sign());

            return Ok(pi);
        }

        if (self.get_exponent() as isize) < -(p as isize) / 6 {
            // for small input compute directly: x + x^3 / 6 + x^5 * 3 / 40

            let mut x = self.clone()?;

            let p_x = p.max(x.get_mantissa_max_bit_len()) + 8;
            x.set_precision(p_x, RoundingMode::None)?;

            let xx = x.mul(&x, p_x, RoundingMode::None)?;
            let x3 = x.mul(&xx, p_x, RoundingMode::None)?;
            let part = x3.div(&SIX, p_x, RoundingMode::None)?;

            let mut ret = if part.is_zero() {
                // since x != 0, part != 0 when rounding
                x.add_correction(false)
            } else {
                let ret = x.add(&part, p_x, RoundingMode::FromZero)?;

                let x5 = x3.mul(&xx, p_x, RoundingMode::None)?;
                let part = x5.mul(&THREE, p_x, RoundingMode::None)?;
                let part = part.div(&FOURTY, p_x, RoundingMode::None)?;

                if part.is_zero() {
                    ret.add_correction(false)
                } else {
                    ret.add(
                        &part,
                        ret.get_mantissa_max_bit_len() + 1,
                        RoundingMode::FromZero,
                    ) // part is much smaller now, so increase precision
                }
            }?;

            ret.set_precision(p, rm)?;

            Ok(ret)
        } else {
            let mut additional_prec = 2;
            if self.get_exponent() == 0 {
                additional_prec += count_leading_ones(self.get_mantissa_digits());
            }

            let p_inc = WORD_BIT_SIZE;
            let mut p_wrk = p + p_inc;

            loop {
                let mut x = self.clone()?;

                let p_x = p_wrk + additional_prec;
                x.set_precision(p_x, RoundingMode::None)?;

                // arcsin(x) = arctan(x / sqrt(1 - x^2))
                let xx = x.mul(&x, p_x, RoundingMode::None)?;
                let t = ONE.sub(&xx, p_x, RoundingMode::None)?;
                let s = t.sqrt(p_x, RoundingMode::None)?;
                let d = x.div(&s, p_x, RoundingMode::None)?;

                let mut ret = d.atan(p_x, rm, cc)?;

                if ret.try_set_precision(p, rm, p_wrk)? {
                    break Ok(ret);
                }

                p_wrk += p_inc;
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::common::util::random_subnormal;

    use super::*;

    #[test]
    fn test_arcsine() {
        let mut cc = Consts::new().unwrap();

        let rm = RoundingMode::ToEven;
        let p = 64;
        let mut n1 = BigFloatNumber::from_word(4294967295, p).unwrap();
        n1.set_exponent(0);
        //println!("{}", n1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
        let _n2 = n1.asin(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // asymptotic & extrema testing
        let p = 320;
        let n1 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let n2 = n1.asin(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e+0", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        assert!(n2.cmp(&n3) == 0);

        // near zero
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e-10", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.asin(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A2A55DE7312DF295F5AB0362F0A77F89C5756A9380CF056D90_e-10", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        //println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();
        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();

        let mut half_pi = cc.pi_num(p, RoundingMode::ToEven).unwrap();
        half_pi.set_exponent(1);

        assert!(d1.asin(p, rm, &mut cc).is_err());
        assert!(d2.asin(p, rm, &mut cc).is_err());
        assert!(d3.asin(p, rm, &mut cc).unwrap().cmp(&d3) == 0);
        assert!(zero.asin(p, rm, &mut cc).unwrap().is_zero());
        assert!(ONE.asin(p, rm, &mut cc).unwrap().cmp(&half_pi) == 0);
        assert!(
            ONE.neg()
                .unwrap()
                .asin(p, rm, &mut cc)
                .unwrap()
                .cmp(&half_pi.neg().unwrap())
                == 0
        );

        // subnormal arg
        let n1 = random_subnormal(p);
        assert!(n1.asin(p, rm, &mut cc).unwrap().cmp(&n1) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn arcsine_perf() {
        let mut cc = Consts::new().unwrap();
        let p = 160;

        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, -5, 0).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.asin(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
