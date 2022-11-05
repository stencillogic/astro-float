//! Hyperbolic arctangent.

use crate::Exponent;
use crate::common::consts::ONE;
use crate::common::consts::TWO;
use crate::common::util::get_add_cost;
use crate::common::util::get_mul_cost;
use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;
use crate::ops::consts::Consts;
use crate::ops::series::PolycoeffGen;
use crate::ops::series::ArgReductionEstimator;
use crate::ops::series::series_cost_optimize;
use crate::ops::series::series_run;


// Polynomial coefficient generator.
struct AtanhPolycoeffGen {
    acc: BigFloatNumber,
    one_full_p: BigFloatNumber,
    val: BigFloatNumber,
    iter_cost: usize,
}

impl AtanhPolycoeffGen {

    fn new(p: usize) -> Result<Self, Error> {

        let acc = BigFloatNumber::from_word(1, 1)?;
        let one_full_p = BigFloatNumber::from_word(1, p)?;
        let val = BigFloatNumber::from_word(1, p)?;

        let iter_cost = get_add_cost(p) + get_add_cost(1); // div is linear, since add is O(1)

        Ok(AtanhPolycoeffGen {
            acc,
            one_full_p,
            val,
            iter_cost,
        })
    }
}

impl PolycoeffGen for AtanhPolycoeffGen {
    fn next(&mut self, rm: RoundingMode) -> Result<&BigFloatNumber, Error> {

        self.acc = self.acc.add(&TWO, rm)?;
        self.val = self.one_full_p.div(&self.acc, rm)?;

        Ok(&self.val)
    }

    #[inline]
    fn get_iter_cost(&self) -> usize {
        self.iter_cost
    }
}

struct AtanhArgReductionEstimator {}

impl ArgReductionEstimator for AtanhArgReductionEstimator {

    /// Estimates cost of reduction n times for number with precision p.
    fn get_reduction_cost(n: usize, p: usize) -> usize {
        let cost_mul = get_mul_cost(p);
        let cost_add = get_add_cost(p);
        n * (3 * cost_mul + 5 * cost_add)
    }

    /// Given m, the negative power of 2 of a number, returns the negative power of 2 if reduction is applied n times.
    #[inline]
    fn reduction_effect(n: usize, m: isize) -> usize {
        // n*log2(3) + m
        ((n as isize)*1000/631 + m) as usize
    }
}


impl BigFloatNumber {

    /// Computes the hyperbolic arctangent of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// 
    /// ## Errors
    /// 
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: when |`self`| > 1.
    pub fn atanh(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {

        let additional_prec = self.get_mantissa_max_bit_len() / 10;

        if self.get_exponent() as isize >= -(additional_prec as isize) {

            // 0.5 * ln((1 + x) / (1 - x))

            let mut x = self.clone()?;

            x.set_precision(x.get_mantissa_max_bit_len() + additional_prec + 3, RoundingMode::None)?;

            let d1 = ONE.add(&x, RoundingMode::None)?;
            let d2 = ONE.sub(&x, RoundingMode::None)?;
            let d3 = d1.div(&d2, RoundingMode::None)?;
            let mut ret = d3.ln(RoundingMode::None, cc)?;

            ret.set_exponent(ret.get_exponent() - 1);
            ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

            Ok(ret)

        } else {

            // series

            let x = self.clone()?;

            let mut ret = x.atanh_series(RoundingMode::None)?;

            ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

            Ok(ret)
        }
    }

    fn atanh_series(mut self, rm: RoundingMode) -> Result<Self, Error> {

        // x + x^3/3 + x^5/5 + ...

        let p = self.get_mantissa_max_bit_len();

        let mut polycoeff_gen = AtanhPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<AtanhPolycoeffGen, AtanhArgReductionEstimator>(
            p, &polycoeff_gen, (-self.e) as isize, 2, false);

        self.set_precision(self.get_mantissa_max_bit_len() + (niter + 1) / 2 + reduction_times * 3, rm)?;

        let arg = if reduction_times > 0 {
            self.atanh_arg_reduce(reduction_times, rm)?
        } else {
            self
        };

        let acc = arg.clone()?;    // x
        let x_step = arg.mul(&arg, rm)?;   // x^2
        let x_first = arg.mul(&x_step, rm)?;   // x^3

        let mut ret = series_run(acc, x_first, x_step, niter, &mut polycoeff_gen, rm)?;
        
        if reduction_times > 0 {
            ret.set_exponent(ret.get_exponent() + reduction_times as Exponent);
        }

        Ok(ret)
    }

    // reduce argument n times.
    fn atanh_arg_reduce(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // y = x / (1 + sqrt(1 - x*x))
        let mut ret = self.clone()?;
        for _ in 0..n {
            let xx = ret.mul(&ret, rm)?;
            let n0 = ONE.sub(&xx, rm)?;
            let n1 = n0.sqrt(rm)?;
            let n2 = n1.add(&ONE, rm)?;
            ret = ret.div(&n2, rm)?;
        }

        Ok(ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_atanh() {
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1,320).unwrap();
        n1.set_exponent(-34);
        let _n2 = n1.atanh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        let mut n1 = BigFloatNumber::from_word(1,320).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.atanh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());
    }

    #[ignore]
    #[test]
    #[cfg(feature="std")]
    fn atanh_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(160, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.atanh(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }

}