//! Sine.

use crate::Sign;
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
use crate::ops::consts::Consts;



// Polynomial coefficient generator.
struct SinPolycoeffGen {
    one_full_p: BigFloatNumber,
    inc: BigFloatNumber,
    fct: BigFloatNumber,
    sign: i8,
    iter_cost: usize,
}

impl SinPolycoeffGen {

    fn new(p: usize) -> Result<Self, Error> {

        let inc = BigFloatNumber::from_word(1, 1)?;
        let fct = BigFloatNumber::from_word(1, p)?;
        let one_full_p = BigFloatNumber::from_word(1, p)?;

        let iter_cost = (get_mul_cost(p) + get_add_cost(p)) << 1; // 2 * (cost(mul) + cost(add))

        let sign = 1;

        Ok(SinPolycoeffGen {
            one_full_p,
            inc,
            fct,
            sign,
            iter_cost,
        })
    }
}

impl PolycoeffGen for SinPolycoeffGen {

    fn next(&mut self, rm: RoundingMode) -> Result<&BigFloatNumber, Error> {

        self.inc = self.inc.add(&ONE, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, rm)?;
        self.fct = self.fct.mul(&inv_inc, rm)?;

        self.inc = self.inc.add(&ONE, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, rm)?;
        self.fct = self.fct.mul(&inv_inc, rm)?;

        self.sign *= -1;
        if self.sign > 0 {
            self.fct.set_sign(Sign::Pos);
        } else {
            self.fct.set_sign(Sign::Neg);
        }

        Ok(&self.fct)
    }

    #[inline]
    fn get_iter_cost(&self) -> usize {
        self.iter_cost
    }
}

struct SinArgReductionEstimator {}

impl ArgReductionEstimator for SinArgReductionEstimator {

    /// Estimates cost of reduction n times for number with precision p.
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
        ((n as isize)*1000/631 + m) as usize
    }
}

impl BigFloatNumber {

    /// Computes the sine of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn sin(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        let mut pi = cc.pi(self.get_mantissa_max_bit_len() + 2, RoundingMode::None)?;

        pi.set_exponent(pi.get_exponent() + 1);

        // determine quadrant
        let mut x = self.clone()?;
        x.set_precision(self.get_mantissa_max_bit_len() + 2, RoundingMode::None)?;
        x = x.div(&pi, RoundingMode::None)?;
        let fractional = x.fract()?;
        x = pi.mul(&fractional, RoundingMode::None)?;

        let mut ret = x.sin_series(RoundingMode::None)?;

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }

    /// sine using series
    pub(super) fn sin_series(mut self, rm: RoundingMode) -> Result<Self, Error> {
        // sin:  x - x^3/3! + x^5/5! - x^7/7! + ...

        let p = self.get_mantissa_max_bit_len();
        let mut polycoeff_gen = SinPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<SinPolycoeffGen, SinArgReductionEstimator>(
            p, &polycoeff_gen, -self.e as isize, 2, false);

        self.set_precision(self.get_mantissa_max_bit_len() + niter * 3 + reduction_times * 3, rm)?;

        let arg = if reduction_times > 0 {
            self.sin_arg_reduce(reduction_times, rm)?
        } else {
            self
        };

        let acc = arg.clone()?;    // x
        let x_step = arg.mul(&arg, rm)?;   // x^2
        let x_first = arg.mul(&x_step, rm)?;   // x^3

        let ret = series_run(acc, x_first, x_step, niter, &mut polycoeff_gen, rm)?;

        if reduction_times > 0 {
            ret.sin_arg_restore(reduction_times, rm)
        } else {
            Ok(ret)
        }
    }

    // reduce argument n times.
    // cost: n * O(add)
    fn sin_arg_reduce(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sin(3*x) = 3*sin(x) - 4*sin(x)^3
        let mut ret = self.clone()?;
        for _ in 0..n {
            ret = ret.div(&THREE, rm)?;
        }
        Ok(ret)
    }

    // restore value for the argument reduced n times.
    // cost: n * (4*O(mul) + O(add))
    fn sin_arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sin(3*x) = 3*sin(x) - 4*sin(x)^3
        let mut sin = self.clone()?;

        for _ in 0..n {
            let mut sin_cub = sin.mul(&sin, rm)?;
            sin_cub = sin_cub.mul(&sin, rm)?;
            let p1 = sin.mul(&THREE, rm)?;
            let p2 = sin_cub.mul(&FOUR, rm)?;
            sin = p1.sub(&p2, rm)?;
        }

        Ok(sin)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_sine() {
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(5,320).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.sin(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());
    }

    #[ignore]
    #[test]
    #[cfg(feature="std")]
    fn sine_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(133, -5, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.sin(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

}