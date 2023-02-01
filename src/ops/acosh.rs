//! Hyperbolic arccosine.

use crate::common::consts::ONE;
use crate::common::util::count_leading_zeroes_skip_first;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::Consts;
use crate::EXPONENT_MAX;
use crate::WORD_BIT_SIZE;

impl BigFloatNumber {
    /// Computes the hyperbolic arccosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: when `self` < 1, or the precision is incorrect.
    pub fn acosh(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        let cmpone = self.cmp(&ONE);
        if cmpone == 0 {
            return Self::new(p);
        } else if cmpone < 0 {
            return Err(Error::InvalidArgument);
        }

        if (self.get_exponent() as isize - 1) / 2 > self.get_mantissa_max_bit_len() as isize + 2 {
            // acosh(x) = ln(2*x)
            if self.get_exponent() == EXPONENT_MAX {
                // ln(2) + ln(x)

                let p_inc = WORD_BIT_SIZE;
                let mut p_wrk = p + p_inc;

                let mut x = self.clone()?;

                loop {
                    let p_x = p_wrk + 3;
                    x.set_precision(p_x, RoundingMode::None)?;

                    x = x.ln(p_x, RoundingMode::None, cc)?;

                    let ln2 = cc.ln_2_num(p_x, RoundingMode::None)?;

                    let mut ret = ln2.add(&x, p_x, RoundingMode::None)?;

                    if ret.try_set_precision(p, rm, p_wrk)? {
                        break Ok(ret);
                    }

                    p_wrk += p_inc;
                }
            } else {
                let mut x = self.clone()?;
                x.set_exponent(x.get_exponent() + 1);
                x.ln(p, rm, cc)
            }
        } else {
            // ln(x + sqrt(x*x - 1))

            let mut additional_prec = 0;
            if self.get_exponent() == 1 {
                additional_prec = count_leading_zeroes_skip_first(self.m.get_digits());
            }

            let mut x = self.clone()?;

            let p_x = p + 3 + additional_prec;
            x.set_precision(p_x, RoundingMode::None)?;

            let xx = x.mul(&x, p_x, RoundingMode::None)?;

            let d1 = xx.sub(&ONE, p_x, RoundingMode::None)?;

            let d2 = d1.sqrt(p_x, RoundingMode::None)?;

            let d3 = d2.add(&x, p_x, RoundingMode::None)?;

            d3.ln(p, rm, cc)
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::Exponent;

    use super::*;

    #[test]
    fn test_acosh() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let n1 = BigFloatNumber::from_word(2, p).unwrap();
        let _n2 = n1.acosh(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        // near 1
        let p = 448;
        let n1 = BigFloatNumber::parse("1.0000000000000000000000000000000000000000000B56A0EBA6F7D47E21A7B2A7806A698BABAF2F05BC61E2F8FB50FE0B98F55B181AC9C8_e+0", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.acosh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("4.C31368910963B1A1BCFC0EDBD393FB7A5E876F9751D93A20E7E48EC0D16090ADA5F46DF2184D32A19C500088EA09CBD4F23DF713113D8A58_e-16", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Bin, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // large exp
        let p = 320;
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e+1000", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.acosh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("2.C5DAB0AF9025886C3364C7B6D6741EB19D4FB009D3F92CA21B77498D9F0666363C665F2F324EAEC8_e+3", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        //println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();
        let d3 = BigFloatNumber::min_positive(p).unwrap();

        // MAX
        let mut d4 = d1.acosh(p, RoundingMode::Down, &mut cc).unwrap();

        d4.set_exponent(d4.get_exponent() - 1);
        let d5 = d4.cosh(p, rm, &mut cc).unwrap();
        let mut d5 = d5.mul(&d5, p, rm).unwrap();
        d5.set_exponent(d5.get_exponent() + 1);

        let mut eps = ONE.clone().unwrap();
        eps.set_exponent(
            d1.get_exponent() - p as Exponent + core::mem::size_of::<Exponent>() as Exponent * 8,
        );

        assert!(
            d1.sub(&d5, p, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );

        assert!(d2.acosh(p, rm, &mut cc).unwrap_err() == Error::InvalidArgument);
        assert!(d3.acosh(p, rm, &mut cc).unwrap_err() == Error::InvalidArgument);

        assert!(ONE.acosh(p, rm, &mut cc).unwrap().is_zero());
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn acosh_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        let p = 160;
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.acosh(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
