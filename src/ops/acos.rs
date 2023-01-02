//! Arccosine.

use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::Exponent;

const ACOS_EXP_THRES: Exponent = -32;

impl BigFloatNumber {
    /// Computes the arccosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: argument is greater than 1 or smaller than -1, or the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn acos(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);
        let mut x = self.clone()?;

        let p_x = p + (-ACOS_EXP_THRES) as usize + 1;
        x.set_precision(p_x, RoundingMode::None)?;

        let mut ret = x.asin(p_x, RoundingMode::None, cc)?;

        let mut pi = cc.pi(p_x, RoundingMode::None)?;

        pi.set_exponent(pi.get_exponent() - 1);

        ret = pi.sub(&ret, p_x, RoundingMode::None)?;

        if ret.get_exponent() < ACOS_EXP_THRES {
            let p_x =
                p + ret.get_exponent().unsigned_abs() as usize + (-ACOS_EXP_THRES) as usize + 1;

            x.set_precision(p_x, RoundingMode::None)?;

            ret = x.asin(p_x, RoundingMode::None, cc)?;

            let mut pi = cc.pi(p_x, RoundingMode::None)?;

            pi.set_exponent(pi.get_exponent() - 1);

            ret = pi.sub(&ret, p_x, RoundingMode::None)?;
        }

        ret.set_precision(p, rm)?;

        Ok(ret)
    }
}

#[cfg(test)]
mod tests {

    use crate::common::{consts::ONE, util::random_subnormal};

    use super::*;

    #[test]
    fn test_arccosine() {
        let mut cc = Consts::new().unwrap();

        let rm = RoundingMode::ToEven;
        let p = 64;
        let mut n1 = BigFloatNumber::from_word(4294967295, p).unwrap();
        n1.set_exponent(0);
        //println!("{}", n1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
        let _n2 = n1.acos(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // near 1
        let p = 320;
        let n1 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let n2 = n1.acos(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("5.2049C1114CF98E7B6DB49CCF999F4A5E697D73E5DA6BEC6578098357460BAFFB0C25779F1C63E8D8_e-21", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // near zero
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e-10", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.acos(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.921FB54442D18467F76D0FD2BEE6B538C877D6FA13175F455EB9961B4834A04EF790AE0274E87FF6_e+0", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();
        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();

        let mut half_pi = cc.pi(p, RoundingMode::ToEven).unwrap();
        half_pi.set_exponent(1);

        assert!(d1.acos(p, rm, &mut cc).is_err());
        assert!(d2.acos(p, rm, &mut cc).is_err());
        assert!(d3.acos(p, rm, &mut cc).unwrap().cmp(&half_pi) == 0);
        assert!(zero.acos(p, rm, &mut cc).unwrap().cmp(&half_pi) == 0);
        assert!(ONE.acos(p, rm, &mut cc).unwrap().is_zero());

        // subnormal arg
        let n1 = random_subnormal(p);
        assert!(n1.acos(p, rm, &mut cc).unwrap().cmp(&half_pi) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn arccosine_perf() {
        let mut cc = Consts::new().unwrap();
        let p = 133;

        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, -5, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.acos(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
