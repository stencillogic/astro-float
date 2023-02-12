//! Arccosine.

use crate::common::consts::ONE;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::Exponent;
use crate::Sign;
use crate::WORD_BIT_SIZE;

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

        let cmpone = self.cmp(&ONE);
        if cmpone == 0 {
            return Self::new2(p, Sign::Pos, self.inexact());
        } else if cmpone > 0 {
            return Err(Error::InvalidArgument);
        }

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        let mut add_p = (1 - ACOS_EXP_THRES) as usize;
        loop {
            let mut x = self.clone()?;

            let p_x = p_wrk + add_p;
            x.set_precision(p_x, RoundingMode::None)?;

            let mut ret = x.asin(p_x, RoundingMode::None, cc)?;

            let mut pi = cc.pi_num(p_x, RoundingMode::None)?;
            pi.set_exponent(pi.exponent() - 1);

            ret = pi.sub(&ret, p_x, RoundingMode::None)?;

            let t = ret.exponent().unsigned_abs() as usize + 1; // ret near pi / 2 gives cancellation
            if add_p < t {
                add_p = t;
            } else {
                if ret.try_set_precision(p, rm, p_wrk)? {
                    return Ok(ret);
                }

                p_wrk += p_inc;
                p_inc = round_p(p_wrk / 5);
            }
        }
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

        let mut half_pi = cc.pi_num(p, RoundingMode::ToEven).unwrap();
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
