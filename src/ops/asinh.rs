//! Hyperbolic arcsine.

use crate::common::consts::FOURTY;
use crate::common::consts::ONE;
use crate::common::consts::SIX;
use crate::common::consts::THREE;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::Consts;

impl BigFloatNumber {
    /// Computes the hyperbolic arcsine of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn asinh(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let mut x = self.clone()?;

        if self.get_exponent() as isize >= -(self.get_mantissa_max_bit_len() as isize) / 6 {
            // ln(x + sqrt(x*x + 1))

            // TODO: if x much larger than 1, then acosh(x) = ln(2*x)

            x.set_precision(
                x.get_mantissa_max_bit_len() + self.get_exponent().unsigned_abs() as usize + 3,
                RoundingMode::None,
            )?;

            let xx = x.mul(&x, RoundingMode::None)?;

            let d1 = xx.add(&ONE, RoundingMode::None)?;

            let d2 = d1.sqrt(RoundingMode::None)?;

            let d3 = d2.add(&x, RoundingMode::None)?;

            let mut ret = d3.ln(RoundingMode::None, cc)?;

            ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

            Ok(ret)
        } else {
            // short series: x - x^3/6 + 3*x^5/40 - 5*x^7/112

            x.set_precision(x.get_mantissa_max_bit_len() + 4, RoundingMode::None)?;

            let xx = x.mul(&x, RoundingMode::None)?;
            let x3 = xx.mul(&x, RoundingMode::None)?;
            let p1 = x3.div(&SIX, RoundingMode::None)?;
            let mut ret = x.sub(&p1, RoundingMode::None)?;

            let x5 = x3.mul(&xx, RoundingMode::None)?;
            let p2 = x5.mul(&THREE, RoundingMode::None)?;
            let p2 = p2.div(&FOURTY, RoundingMode::None)?;
            ret = ret.add(&p2, RoundingMode::None)?;

            ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

            Ok(ret)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_asinh() {
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, 320).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.asinh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // near zero
        let n1 = BigFloatNumber::parse("-6.2625AC139402BE3D18693E64BFF93D122A9FB2295D654817665874F984C1D9E32B6C42F068F33020_e-13", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let n2 = n1.asinh(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("-6.2625AC139402BE3D18693E64BFF93D122A9F8B69858A068F649D78ADAF2C51C59A22D727857055D8_e-13", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Hex, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // large exp
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e+1000", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let n2 = n1.asinh(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("2.C5DAB0AF9025886C3364C7B6D6741EB19D4FB009D3F92CA21B77498D9F0666363C665F2F324EAEC8_e+3", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Bin, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn asinh_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(160, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.asinh(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
