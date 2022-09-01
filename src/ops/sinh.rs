//! Hyperbolic sine.

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
struct SinhPolycoeffGen {
    one: BigFloatNumber,
    one_full_p: BigFloatNumber,
    inc: BigFloatNumber,
    fct: BigFloatNumber,
    iter_cost: usize,
}

impl SinhPolycoeffGen {

    fn new(p: usize) -> Result<Self, Error> {
        let one = BigFloatNumber::from_word(1, 1)?;
        let inc = BigFloatNumber::from_word(1, 1)?;
        let fct = BigFloatNumber::from_word(1, p)?;
        let one_full_p = BigFloatNumber::from_word(1, p)?;

        let iter_cost = (get_mul_cost(p) + get_add_cost(p)) << 1; // 2 * (cost(mul) + cost(add))

        Ok(SinhPolycoeffGen {
            one,
            one_full_p,
            inc,
            fct,
            iter_cost,
        })
    }
}

impl PolycoeffGen for SinhPolycoeffGen {
    fn next(&mut self, rm: RoundingMode) -> Result<&BigFloatNumber, Error> {
        self.inc = self.inc.add(&self.one, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, rm)?;
        self.fct = self.fct.mul(&inv_inc, rm)?;
        self.inc = self.inc.add(&self.one, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, rm)?;
        self.fct = self.fct.mul(&inv_inc, rm)?;
        Ok(&self.fct)
    }

    #[inline]
    fn get_iter_cost(&self) -> usize {
        self.iter_cost
    }
}

struct SinhArgReductionEstimator {}

impl ArgReductionEstimator for SinhArgReductionEstimator {

    /// Estimates cost of reduction n times for number with precision p.
    fn get_reduction_cost(n: usize, p: usize) -> usize {
        // n * (4 * cost(mul) + 2 * cost(add))
        let cost_mul = get_mul_cost(p);
        let cost_add = get_add_cost(p);
        (n * ((cost_mul << 1) + cost_add )) << 1
    }

    /// Given m, the negative power of 2 of a number, returns the negative power of 2 if reduction is applied n times.
    #[inline]
    fn reduction_effect(n: usize, m: usize) -> usize {
        // n*log2(3) + m
        n*1000/631 + m
    }
}

impl BigFloatNumber {

    /// Computes hyperbolic sine.
    pub fn sinh(&self, rm: RoundingMode) -> Result<Self, Error> {
        // sinh(3*x) = 3*sinh(x) + 4*sinh(x)^3
        Err(Error::InvalidArgument)
    }

    /// sinh using series, for |x| < 1
    pub(super) fn sinh_series(&self, rm: RoundingMode) -> Result<Self, Error> {
        // sinh:  x + x^3/3! + x^5/5! + x^7/7! + ...

        let p = self.get_mantissa_max_bit_len();
        let mut polycoeff_gen = SinhPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<SinhPolycoeffGen, SinhArgReductionEstimator>(
            p, &polycoeff_gen, (-self.e) as usize, 2);

        let arg_holder;
        let arg = if reduction_times > 0 {
            arg_holder = self.sinh_arg_reduce(reduction_times, rm)?;
            &arg_holder
        } else {
            self
        };

        let acc = arg.clone()?;    // x
        let x_step = arg.mul(arg, rm)?;   // x^2
        let x_first = arg.mul(&x_step, rm)?;   // x^3

        let ret = series_run(acc, x_first, x_step, niter, &mut polycoeff_gen, rm)?;

        if reduction_times > 0 {
            ret.sinh_arg_restore(reduction_times, rm)
        } else {
            Ok(ret)
        }
    }

    // reduce argument n times.
    // cost: n * O(add)
    fn sinh_arg_reduce(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sinh(3*x) = 3*sinh(x) + 4*sinh(x)^3
        let mut ret = self.clone()?;
        let three = Self::from_word(3, 1)?;
        for _ in 0..n {
            ret = ret.div(&three, rm)?;
        }
        Ok(ret)
    }

    // restore value for the argument reduced n times.
    // cost: n * (4*O(mul) + O(add))
    fn sinh_arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sinh(3*x) = 3*sinh(x) + 4*sinh(x)^3
        let mut sinh = self.clone()?;
        let three = Self::from_word(3, 1)?;
        let four = Self::from_word(4, 1)?;
        for _ in 0..n {
            let mut sinh_cub = sinh.mul(&sinh, rm)?;
            sinh_cub = sinh_cub.mul(&sinh, rm)?;
            let p1 = sinh.mul(&three, rm)?;
            let p2 = sinh_cub.mul(&four, rm)?;
            sinh = p1.add(&p2, rm)?;
        }
        Ok(sinh)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_sinh() {
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1,32000).unwrap();
        n1.set_exponent(0);
        let n2 = n1.sinh_series(rm).unwrap();
        //println!("{:?}", n2.fp3(crate::Radix::Dec, rm).unwrap());
    }

    #[ignore]
    #[test]
    fn sinh_perf() {
        let mut n = vec![];
        for _ in 0..100 {
            n.push(BigFloatNumber::random_normal(32000, -0, -0).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let f = ni.sinh_series(RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

}