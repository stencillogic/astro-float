//! Hyperbolic tangent.

use crate::Consts;
use crate::common::consts::ONE;
use crate::defs::EXPONENT_MAX;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;


impl BigFloatNumber {

    /// Computes the hyperbolic tangent of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn tanh(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        // (e^(2*x) - 1) / (e^(2*x) + 1)
        let mut x = self.clone()?;

        x.set_precision(x.get_mantissa_max_bit_len() + 640, RoundingMode::None)?;

        if x.get_exponent() == EXPONENT_MAX {
            return Err(Error::ExponentOverflow(self.get_sign()));
        }

        x.set_exponent(x.get_exponent() + 1);

        let xexp = x.exp(RoundingMode::None, cc)?;

        let d1 = xexp.sub(&ONE, RoundingMode::None)?;
        let d2 = xexp.add(&ONE, RoundingMode::None)?;

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
        let _n2 = n1.tanh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        let n1 = BigFloatNumber::parse("8.00000000000000100000000000000010B6200000000000000000000000000002E8B9840AAAAAAAAAAAAAAAAAAAAAAAAADE85C5950B78E38E38E38E38E38E38E3902814A92D7C21CDB6DB6DB6DB6DB6E_e+1", crate::Radix::Hex, 640, RoundingMode::None).unwrap();
        let n2 = n1.tanh(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF3455354A958B21BA74F856FDC3BA2D793AEBE0E1D1ADF118BD9D0B592FF14C815D2C_e-1", crate::Radix::Hex, 640, RoundingMode::None).unwrap();

        assert!(n2.cmp(&n3) == 0);
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