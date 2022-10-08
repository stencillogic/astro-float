//! Arcsine.

use crate::common::consts::ONE;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;

impl BigFloatNumber {

    /// Arcsine
    pub fn asin(&self, rm: RoundingMode) -> Result<Self, Error> {

        if self.cmp(&ONE) == 0 {
            return Self::new(self.get_mantissa_max_bit_len());
        }

        let mut x = self.clone()?;
        x.set_precision(self.get_mantissa_max_bit_len() + 2, RoundingMode::None)?;

        // arcsin(x) = arctan(x / sqrt(1 - x^2))
        let xx = x.mul(&x, RoundingMode::None)?;
        let p = ONE.sub(&xx, RoundingMode::None)?;
        let s = p.sqrt(RoundingMode::None)?;
        let d = x.div(&s, RoundingMode::None)?;

        let mut ret = d.atan(RoundingMode::None)?;

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_arcsine() {
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(4294967295,64).unwrap();
        n1.set_exponent(0);
        //println!("{}", n1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
        let _n2 = n1.asin(rm).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());
    }

    #[ignore]
    #[test]
    fn arcsine_perf() {
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(160, -5, 0).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.asin(RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

}