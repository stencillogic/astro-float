//! Arcsine.

use crate::common::consts::ONE;
use crate::common::util::count_leading_ones;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;
use crate::ops::consts::Consts;


impl BigFloatNumber {

    /// Computes the arcsine of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// 
    /// ## Errors
    /// 
    ///  - InvalidArgument: argument is greater than 1 or smaller than -1.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn asin(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        if self.cmp(&ONE) == 0 {
            
            let mut pi = cc.pi(self.get_mantissa_max_bit_len(), rm)?;

            pi.set_exponent(pi.get_exponent() - 1);

            return Ok(pi);
        }

        let mut additional_prec = 2;
        if self.get_exponent() == 0 {
            additional_prec += count_leading_ones(self.get_mantissa_digits());
        }

        let mut x = self.clone()?;
        x.set_precision(self.get_mantissa_max_bit_len() + additional_prec, RoundingMode::None)?;

        // arcsin(x) = arctan(x / sqrt(1 - x^2))
        let xx = x.mul(&x, RoundingMode::None)?;
        let p = ONE.sub(&xx, RoundingMode::None)?;
        let s = p.sqrt(RoundingMode::None)?;
        let d = x.div(&s, RoundingMode::None)?;

        let mut ret = d.atan(RoundingMode::None, cc)?;

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_arcsine() {
        
        let mut cc = Consts::new().unwrap();

        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(4294967295,64).unwrap();
        n1.set_exponent(0);
        //println!("{}", n1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
        let _n2 = n1.asin(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // asymptotic & extrema testing
        let n1 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC487_e-1", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let n2 = n1.asin(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e+0", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        assert!(n2.cmp(&n3) == 0);

        // near zero
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e-10", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let n2 = n1.asin(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A2A55DE7312DF295F5AB0362F0A77F89C5756A9380CF056D90_e-10", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        //println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);
        
    }

    #[ignore]
    #[test]
    #[cfg(feature="std")]
    fn arcsine_perf() {
        let mut cc = Consts::new().unwrap();

        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(160, -5, 0).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.asin(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

}