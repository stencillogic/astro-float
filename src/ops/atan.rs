//! Arctangent.

use crate::common::consts::ONE;
use crate::common::consts::TWO;
use crate::common::util::get_add_cost;
use crate::common::util::get_mul_cost;
use crate::common::util::get_sqrt_cost;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::ops::series::series_cost_optimize;
use crate::ops::series::series_run;
use crate::ops::series::ArgReductionEstimator;
use crate::ops::series::PolycoeffGen;
use crate::ops::util::compute_small_exp;
use crate::Exponent;
use crate::WORD_BIT_SIZE;

// Polynomial coefficient generator.
struct AtanPolycoeffGen {
    f: BigFloatNumber,
    iter_cost: usize,
}

impl AtanPolycoeffGen {
    fn new(_p: usize) -> Result<Self, Error> {
        let f = BigFloatNumber::from_word(1, 1)?;

        let iter_cost = get_add_cost(f.get_mantissa_max_bit_len());

        Ok(AtanPolycoeffGen { f, iter_cost })
    }
}

impl PolycoeffGen for AtanPolycoeffGen {
    fn next(&mut self, rm: RoundingMode) -> Result<&BigFloatNumber, Error> {
        let p = self.f.get_mantissa_max_bit_len();
        if self.f.is_positive() {
            self.f = self.f.add(&TWO, p, rm)?;
        } else {
            self.f = self.f.sub(&TWO, p, rm)?;
        }

        self.f.inv_sign();

        Ok(&self.f)
    }

    #[inline]
    fn get_iter_cost(&self) -> usize {
        self.iter_cost
    }

    #[inline]
    fn is_div(&self) -> bool {
        true
    }
}

struct AtanArgReductionEstimator {}

impl ArgReductionEstimator for AtanArgReductionEstimator {
    /// Estimates cost of reduction n times for number with precision p.
    fn get_reduction_cost(n: usize, p: usize) -> usize {
        let cost_mul = get_mul_cost(p);
        let cost_add = get_add_cost(p);
        let sqrt_cost = get_sqrt_cost(p, cost_mul, cost_add);
        n * (2 * (cost_mul + cost_add) + sqrt_cost)
    }

    /// Given m, the negative power of 2 of a number, returns the negative power of 2 if reduction is applied n times.
    #[inline]
    fn reduction_effect(n: usize, m: isize) -> usize {
        // for x much smaller than 1, reduction is almost x/2
        (n as isize + m) as usize
    }
}

impl BigFloatNumber {
    /// Computes the arctangent of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn atan(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            let mut ret = Self::new(p)?;
            ret.set_sign(self.get_sign());
            return Ok(ret);
        }

        compute_small_exp!(self, self.get_exponent() as isize / 2 - 1, true, p, rm);

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        loop {
            let mut x = self.clone()?;

            let p_x = p_wrk + 2;
            x.set_precision(p_x, RoundingMode::None)?;

            // if x > 1 then arctan(x) = pi/2 - arctan(1/x)
            let mut ret = if x.get_exponent() > 0 {
                x = x.reciprocal(p_x, RoundingMode::None)?;
                let ret = x.atan_series(RoundingMode::None)?;
                let mut pi = cc.pi_num(p_x, RoundingMode::None)?;
                pi.set_exponent(1);
                pi.set_sign(self.get_sign());

                pi.sub(&ret, p_x, RoundingMode::None)
            } else {
                x.atan_series(RoundingMode::None)
            }?;

            if ret.try_set_precision(p, rm, p_wrk)? {
                break Ok(ret);
            }

            p_wrk += p_inc;
            p_inc *= 2;
        }
    }

    /// arctan using series
    pub(super) fn atan_series(mut self, rm: RoundingMode) -> Result<Self, Error> {
        // atan:  x - x^3/3 + x^5/5 - x^7/7 + ...

        let p = self.get_mantissa_max_bit_len();
        let mut polycoeff_gen = AtanPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<AtanArgReductionEstimator>(
            p,
            &polycoeff_gen,
            -(self.e as isize),
            2,
            false,
        );

        let p_arg = self.get_mantissa_max_bit_len() + 1 + reduction_times * 3;
        self.set_precision(p_arg, rm)?;

        let arg = if reduction_times > 0 {
            self.atan_arg_reduce(reduction_times, rm)?
        } else {
            self
        };

        let acc = arg.clone()?; // x
        let x_step = arg.mul(&arg, p_arg, rm)?; // x^2
        let x_first = arg.mul(&x_step, p_arg, rm)?; // x^3

        let mut ret = series_run(acc, x_first, x_step, niter, &mut polycoeff_gen)?;

        if reduction_times > 0 {
            ret.set_exponent(ret.get_exponent() + reduction_times as Exponent);
        }

        Ok(ret)
    }

    // reduce argument n times.
    fn atan_arg_reduce(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // y = x / (1 + sqrt(1 + x*x))
        let mut ret = self.clone()?;
        let p = ret.get_mantissa_max_bit_len();

        for _ in 0..n {
            let xx = ret.mul(&ret, p, rm)?;
            let n0 = xx.add(&ONE, p, rm)?;
            let n1 = n0.sqrt(p, rm)?;
            let n2 = n1.add(&ONE, p, rm)?;
            ret = ret.div(&n2, p, rm)?;
        }

        Ok(ret)
    }
}

#[cfg(test)]
mod tests {

    use crate::common::util::random_subnormal;

    use super::*;

    #[test]
    fn test_arctan() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, p).unwrap();
        n1.set_exponent(1);
        let _n2 = n1.atan(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // small exp
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e-20", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.atan(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419D71406B5262DC1F0C_e-20", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // large exp
        let n1 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A200000000000000004D3C337F7C8D419EBBFC39B4BEC14AF6_e+20", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.atan(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.921FB54442D18469898CC51701B839A1AF0B18A2C68B83BE07F0257A80F25883A5F3E060CDB82FEE_e+0", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // near 1
        let n1 = BigFloatNumber::parse(
            "1.00000000000000000000000000000000000000000000000000000000000000002DC85F7E77EC487C",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let n2 = n1.atan(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse(
            "C.90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22682E3838CA2A291C_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();

        // println!("{:?}", n1.format(crate::Radix::Bin, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // max, min, subnormal
        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();
        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();

        let mut half_pi = cc.pi_num(p, RoundingMode::ToEven).unwrap();
        half_pi.set_exponent(1);

        assert!(d1.atan(p, rm, &mut cc).unwrap().cmp(&half_pi) == 0);
        assert!(
            d2.atan(p, rm, &mut cc)
                .unwrap()
                .cmp(&half_pi.neg().unwrap())
                == 0
        );
        assert!(d3.atan(p, rm, &mut cc).unwrap().cmp(&d3) == 0);
        assert!(zero.atan(p, rm, &mut cc).unwrap().is_zero());

        // subnormal arg
        let n1 = random_subnormal(p);
        assert!(n1.atan(p, rm, &mut cc).unwrap().cmp(&n1) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn arctan_perf() {
        let p = 16000;
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10 {
            n.push(BigFloatNumber::random_normal(p, -5, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.atan(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
