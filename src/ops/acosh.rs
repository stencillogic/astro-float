//! Hyperbolic arccosine.

use crate::Consts;
use crate::common::consts::ONE;
use crate::common::util::count_leading_zeroes_skip_first;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;


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

        let mut additional_prec = 0;
        if self.get_exponent() == 1 {
            additional_prec = count_leading_zeroes_skip_first(self.m.get_digits());
        }

        let mut x = self.clone()?;

        x.set_precision(x.get_mantissa_max_bit_len() + 3 + additional_prec, RoundingMode::None)?;

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
        let n1 = BigFloatNumber::from_word(2,320).unwrap();
        let _n2 = n1.acosh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        let n1 = BigFloatNumber::parse("1.000000000000000100000000000000010B6200000000000000000000000000002E8B9840AAAAAAAAAAAAAAAAAAAAAAAAADE85C5950B78E38E38E38E38E38E38E3902814A92D7C21CDB6DB6DB6DB6DB6E_e+0", crate::Radix::Hex, 640, RoundingMode::None).unwrap();
        let n2 = n1.acosh(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.6A09E667F3BCC90951E10B153B1BB120561BB6ADA1D9FAE9B777BDA85E1967A167625CACDDAC49AEAED3E7EFBFD6FD6CFC35D50CB80E62AA8503AE9A76869CEAB806819B8816A2A9564506A0C331002E_e-8", crate::Radix::Hex, 640, RoundingMode::None).unwrap();

        assert!(n2.cmp(&n3) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature="std")]
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