//! Arccosine.

use crate::Exponent;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;
use crate::ops::consts::Consts;

const ACOS_EXP_THRES: Exponent = -32;

impl BigFloatNumber {

    /// Computes the arccosine of a number. The result is rounded using the rounding mode `rm`. 
    /// This function requires constants cache `cc` for computing the result.
    /// 
    /// ## Errors
    /// 
    ///  - InvalidArgument: argument is greater than 1 or smaller than -1.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn acos(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        let mut x = self.clone()?;
        x.set_precision(self.get_mantissa_max_bit_len() + (-ACOS_EXP_THRES) as usize + 1, RoundingMode::None)?;

        let mut ret = x.asin(RoundingMode::None, cc)?;

        let mut pi = cc.pi(x.get_mantissa_max_bit_len(), RoundingMode::None)?;

        pi.set_exponent(pi.get_exponent() - 1);

        ret = pi.sub(&ret, RoundingMode::None)?;

        if ret.get_exponent() < ACOS_EXP_THRES {

            x.set_precision(self.get_mantissa_max_bit_len() + ret.get_exponent().unsigned_abs() as usize 
                            + (-ACOS_EXP_THRES) as usize + 1, RoundingMode::None)?;

            ret = x.asin(RoundingMode::None, cc)?;

            let mut pi = cc.pi(x.get_mantissa_max_bit_len(), RoundingMode::None)?;

            pi.set_exponent(pi.get_exponent() - 1);

            ret = pi.sub(&ret, RoundingMode::None)?;    
        }

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_arccosine() {

        let mut cc = Consts::new().unwrap();

        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(4294967295,64).unwrap();
        n1.set_exponent(0);
        //println!("{}", n1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
        let _n2 = n1.acos(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // near 1
        let n1 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC487_e-1", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let n2 = n1.acos(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("5.2049C1114CF98E7B6DB49CCF999F4A5E697D73E5DA6BEC6578098357460BAFFB0C25779F1C63E8D8_e-21", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // near zero
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e-10", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let n2 = n1.acos(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.921FB54442D18467F76D0FD2BEE6B538C877D6FA13175F455EB9961B4834A04EF790AE0274E87FF6_e+0", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature="std")]
    fn arccosine_perf() {

        let mut cc = Consts::new().unwrap();

        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(133, -5, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.acos(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

}