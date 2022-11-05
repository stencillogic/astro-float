//! Hyperbolic cocosine.

use crate::common::consts::FOUR;
use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::common::util::get_add_cost;
use crate::common::util::get_mul_cost;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;
use crate::ops::series::PolycoeffGen;
use crate::ops::series::ArgReductionEstimator;
use crate::ops::series::series_run;
use crate::ops::series::series_cost_optimize;


// Polynomial coefficient generator.
struct CoshPolycoeffGen {
    one_full_p: BigFloatNumber,
    inc: BigFloatNumber,
    fct: BigFloatNumber,
    iter_cost: usize,
}

impl CoshPolycoeffGen {

    fn new(p: usize) -> Result<Self, Error> {
        let inc = BigFloatNumber::from_word(0, 1)?;
        let fct = BigFloatNumber::from_word(1, p)?;
        let one_full_p = BigFloatNumber::from_word(1, p)?;

        let iter_cost = (get_mul_cost(p) + get_add_cost(p)) << 1; // 2 * (cost(mul) + cost(add))

        Ok(CoshPolycoeffGen {
            one_full_p,
            inc,
            fct,
            iter_cost,
        })
    }
}

impl PolycoeffGen for CoshPolycoeffGen {

    fn next(&mut self, rm: RoundingMode) -> Result<&BigFloatNumber, Error> {

        self.inc = self.inc.add(&ONE, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, rm)?;
        self.fct = self.fct.mul(&inv_inc, rm)?;

        self.inc = self.inc.add(&ONE, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, rm)?;
        self.fct = self.fct.mul(&inv_inc, rm)?;

        Ok(&self.fct)
    }

    #[inline]
    fn get_iter_cost(&self) -> usize {
        self.iter_cost
    }
}

struct CoshArgReductionEstimator {}

impl ArgReductionEstimator for CoshArgReductionEstimator {

    /// Estimates the cost of reduction n times for number with precision p.
    fn get_reduction_cost(n: usize, p: usize) -> usize {
        // n * (4 * cost(mul) + 2 * cost(add))
        let cost_mul = get_mul_cost(p);
        let cost_add = get_add_cost(p);
        (n * ((cost_mul << 1) + cost_add )) << 1
    }

    /// Given m, the negative power of 2 of a number, returns the negative power of 2 if reduction is applied n times.
    #[inline]
    fn reduction_effect(n: usize, m: isize) -> usize {
        // n*log2(3) + m
        (n as isize*1000/631 + m) as usize
    }
}

impl BigFloatNumber {

    /// Computes the hyperbolic cosine of a number. The result is rounded using the rounding mode `rm`.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn cosh(&self, rm: RoundingMode) -> Result<Self, Error> {

        let arg = self.clone()?;

        let mut ret = arg.cosh_series(RoundingMode::None)?;

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }

    /// cosh using series, for |x| < 1
    pub(super) fn cosh_series(mut self, rm: RoundingMode) -> Result<Self, Error> {
        // cosh:  1 + x^2/2! + x^4/4! + x^6/6! + ...

        let p = self.get_mantissa_max_bit_len();
        let mut polycoeff_gen = CoshPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<CoshPolycoeffGen, CoshArgReductionEstimator>(
            p, &polycoeff_gen, (-self.e) as isize, 2, false);

        let full_p = p + niter * 2 + reduction_times * 3;
        self.set_precision(full_p, rm)?;

        let arg = if reduction_times > 0 {
            self.cosh_arg_reduce(reduction_times, rm)?
        } else {
            self
        };

        let acc = Self::from_word(1, full_p)?;    // x
        let x_step = arg.mul(&arg, rm)?;   // x^2
        let x_first = x_step.clone()?;

        let ret = series_run(acc, x_first, x_step, niter, &mut polycoeff_gen, rm)?;

        if reduction_times > 0 {
            ret.cosh_arg_restore(reduction_times, rm)
        } else {
            Ok(ret)
        }
    }

    // reduce argument n times.
    // cost: n * O(add)
    fn cosh_arg_reduce(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // cosh(3*x) = 4*cosh(x)^3 - 3*cosh(x)
        let mut ret = self.clone()?;
        for _ in 0..n {
            ret = ret.div(&THREE, rm)?;
        }
        Ok(ret)
    }

    // restore value for the argument reduced n times.
    fn cosh_arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // cosh(3*x) = 4*cosh(x)^3 - 3*cosh(x)
        let mut cosh = self.clone()?;

        for _ in 0..n {
            let mut cosh_cub = cosh.mul(&cosh, rm)?;
            cosh_cub = cosh_cub.mul(&cosh, rm)?;
            let p1 = cosh.mul(&THREE, rm)?;
            let p2 = cosh_cub.mul(&FOUR, rm)?;
            cosh = p2.sub(&p1, rm)?;
        }

        Ok(cosh)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_cosh() {
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1,320).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.cosh(rm).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());
    }

    #[ignore]
    #[test]
    #[cfg(feature="std")]
    fn cosh_perf() {
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(320, -20, 20).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.cosh(RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

}
