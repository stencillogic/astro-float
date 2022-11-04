//! Hyperbolic arccosine.

use crate::Consts;
use crate::common::consts::ONE;
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
    pub fn acosh(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        // ln(x + sqrt(x*x - 1))

        let mut x = self.clone()?;

        x.set_precision(x.get_mantissa_max_bit_len() + 3, RoundingMode::None)?;

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
        let mut n1 = BigFloatNumber::from_word(1,320).unwrap();
        n1.set_exponent(0);
        let n2 = n1.acosh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());
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