//! Tangent.

use crate::Consts;
use crate::common::consts::ONE;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;



impl BigFloatNumber {

    /// Computes the tangent of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn tanh(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        let mut x = self.clone()?;

        x.set_precision(x.get_mantissa_max_bit_len() + 3, RoundingMode::None)?;
        x.set_exponent(x.get_exponent() + 1);

        let x = x.exp(RoundingMode::None, cc)?;

        let d1 = x.sub(&ONE, RoundingMode::None)?;
        let d2 = x.add(&ONE, RoundingMode::None)?;

        let mut ret = d1.div(&d2, RoundingMode::None)?;

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_tanh() {
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1,320).unwrap();
        n1.set_exponent(0);
        let n2 = n1.tanh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());
    }

    #[ignore]
    #[test]
    #[cfg(feature="std")]
    fn tanh_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(160, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.tanh(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

}