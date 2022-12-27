//! Hyperbolic sine.

use crate::common::consts::FOUR;
use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::common::util::get_add_cost;
use crate::common::util::get_mul_cost;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::series::series_cost_optimize;
use crate::ops::series::series_run;
use crate::ops::series::ArgReductionEstimator;
use crate::ops::series::PolycoeffGen;

// Polynomial coefficient generator.
struct SinhPolycoeffGen {
    one_full_p: BigFloatNumber,
    inc: BigFloatNumber,
    fct: BigFloatNumber,
    iter_cost: usize,
}

impl SinhPolycoeffGen {
    fn new(p: usize) -> Result<Self, Error> {
        let inc = BigFloatNumber::from_word(1, 1)?;
        let fct = BigFloatNumber::from_word(1, p)?;
        let one_full_p = BigFloatNumber::from_word(1, p)?;

        let iter_cost = (get_mul_cost(p) + get_add_cost(p) + get_add_cost(inc.get_mantissa_max_bit_len())) * 2;

        Ok(SinhPolycoeffGen {
            one_full_p,
            inc,
            fct,
            iter_cost,
        })
    }
}

impl PolycoeffGen for SinhPolycoeffGen {
    fn next(&mut self, rm: RoundingMode) -> Result<&BigFloatNumber, Error> {
        let p_inc = self.inc.get_mantissa_max_bit_len();
        let p_one = self.one_full_p.get_mantissa_max_bit_len();

        self.inc = self.inc.add(&ONE, p_inc, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, p_one, rm)?;
        self.fct = self.fct.mul(&inv_inc, p_one, rm)?;

        self.inc = self.inc.add(&ONE, p_inc, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, p_one, rm)?;
        self.fct = self.fct.mul(&inv_inc, p_one, rm)?;

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
        let cost_mul = get_mul_cost(p);
        let cost_add = get_add_cost(p);
        let cost_mul2 = get_mul_cost(THREE.get_mantissa_max_bit_len());

        n * (2 * cost_mul + 3 * cost_add + cost_mul2)
    }

    /// Given m, the negative power of 2 of a number, returns the negative power of 2 if reduction is applied n times.
    #[inline]
    fn reduction_effect(n: usize, m: isize) -> usize {
        // n*log2(3) + m
        (n as isize * 1000 / 631 + m) as usize
    }
}

impl BigFloatNumber {
    /// Computes the hyperbolic sine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn sinh(&self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        let arg = self.clone()?;

        let p = round_p(p);

        let mut ret = arg.sinh_series(p, RoundingMode::None)?;

        ret.set_precision(p, rm)?;

        Ok(ret)
    }

    /// sinh using series, for |x| < 1
    pub(super) fn sinh_series(mut self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sinh:  x + x^3/3! + x^5/5! + x^7/7! + ...

        let mut polycoeff_gen = SinhPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<
            SinhPolycoeffGen,
            SinhArgReductionEstimator,
        >(p, &polycoeff_gen, (-self.e) as isize, 2, false);

        let p_arg = p + 1 + reduction_times * 3;
        self.set_precision(p_arg, rm)?;

        let arg = if reduction_times > 0 {
            self.sinh_arg_reduce(reduction_times, rm)?
        } else {
            self
        };

        let acc = arg.clone()?; // x
        let x_step = arg.mul(&arg, p_arg, rm)?; // x^2
        let x_first = arg.mul(&x_step, p_arg, rm)?; // x^3

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
        let mut d = THREE.clone()?;
        for _ in 1..n {
            d = d.mul_full_prec(&THREE)?;
        }
        self.div(&d, self.get_mantissa_max_bit_len(), rm)
    }

    // restore value for the argument reduced n times.
    // cost: n * (4*O(mul) + O(add))
    fn sinh_arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sinh(3*x) = 3*sinh(x) + 4*sinh(x)^3
        let mut sinh = self.clone()?;
        let p = sinh.get_mantissa_max_bit_len();

        for _ in 0..n {
            let mut sinh_cub = sinh.mul(&sinh, p, rm)?;
            sinh_cub = sinh_cub.mul(&sinh, p, rm)?;
            let p1 = sinh.mul(&THREE, p, rm)?;
            let p2 = sinh_cub.mul(&FOUR, p, rm)?;
            sinh = p1.add(&p2, p, rm)?;
        }

        Ok(sinh)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_sinh() {
        let p = 32000;
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, 1).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.sinh(p, rm).unwrap();
        //println!("{:?}", n2.fp3(crate::Radix::Dec, rm).unwrap());
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn sinh_perf() {
        let p = 32000;
        let mut n = vec![];
        for _ in 0..100 {
            n.push(BigFloatNumber::random_normal(p, -0, -0).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.drain(..) {
                let _f = ni.sinh_series(p, RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
