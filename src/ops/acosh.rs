//! Hyperbolic arccosine.

use crate::common::consts::ONE;
use crate::common::util::count_leading_zeroes_skip_first;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::Consts;

impl BigFloatNumber {
    /// Computes the hyperbolic arccosine of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: when `self` < 1.
    pub fn acosh(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        // ln(x + sqrt(x*x - 1))

        // TODO: if x much larger than 1, then acosh(x) = ln(2*x)

        let cmpone = self.cmp(&ONE);
        if cmpone == 0 {
            return Self::new(self.get_mantissa_max_bit_len());
        } else if cmpone < 0 {
            return Err(Error::InvalidArgument);
        }

        let mut additional_prec = 0;
        if self.get_exponent() == 1 {
            additional_prec = count_leading_zeroes_skip_first(self.m.get_digits());
        }

        let mut x = self.clone()?;

        x.set_precision(
            x.get_mantissa_max_bit_len() + 3 + additional_prec,
            RoundingMode::None,
        )?;

        let xx = x.mul(&x, RoundingMode::None)?;

        let d1 = xx.sub(&ONE, RoundingMode::None)?;

        let d2 = d1.sqrt(RoundingMode::None)?;

        let d3 = d2.add(&x, RoundingMode::None)?;

        let mut ret = d3.ln(RoundingMode::None, cc)?;

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_acosh() {
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let n1 = BigFloatNumber::from_word(2, 320).unwrap();
        let _n2 = n1.acosh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        // near 1
        let n1 = BigFloatNumber::parse("1.0000000000000000000000000000000000000000000B56A0EBA6F7D47E21A7B2A7806A698BABAF2F05BC61E2F8FB50FE0B98F55B181AC9C8_e+0", crate::Radix::Hex, 448, RoundingMode::None).unwrap();
        let n2 = n1.acosh(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("4.C31368910963B1A1BCFC0EDBD393FB7A5E876F9751D93A20E7E48EC0D16090ADA5F46DF2184D32A19C500088EA09CBD4F23DF713113D8A58_e-16", crate::Radix::Hex, 448, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Bin, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // large exp
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e+1000", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let n2 = n1.acosh(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("2.C5DAB0AF9025886C3364C7B6D6741EB19D4FB009D3F92CA21B77498D9F0666363C665F2F324EAEC8_e+3", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        //println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn acosh_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(160, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.acosh(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
