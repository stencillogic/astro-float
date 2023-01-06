//! Hyperbolic cocosine.

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
use crate::Consts;
use crate::Sign;

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

        let iter_cost =
            (get_mul_cost(p) + get_add_cost(p) + get_add_cost(inc.get_mantissa_max_bit_len())) * 2;

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

struct CoshArgReductionEstimator {}

impl ArgReductionEstimator for CoshArgReductionEstimator {
    /// Estimates the cost of reduction n times for number with precision p.
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
    /// Computes the hyperbolic cosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache cc for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn cosh(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let mut arg = self.clone()?;

        if self.get_exponent() > 0 {
            arg.set_sign(Sign::Pos);

            let mut ret = if (self.get_exponent() as isize - 1) / 2
                > self.get_mantissa_max_bit_len() as isize + 2
            {
                // e^x / 2

                arg.exp(p, rm, cc)
            } else {
                // (e^x + e^(-x)) / 2

                let p_arg = p + 3;

                arg.set_precision(p_arg, RoundingMode::None)?;

                let ex = arg.exp(p_arg, rm, cc)?;

                let xe = ex.reciprocal(p_arg, RoundingMode::None)?;

                ex.add(&xe, p_arg, RoundingMode::None)
            }?;

            ret.set_exponent(ret.get_exponent() - 1);
            ret.set_precision(p, rm)?;

            Ok(ret)
        } else {
            let mut ret = arg.cosh_series(p, RoundingMode::None)?;

            ret.set_precision(p, rm)?;

            Ok(ret)
        }
    }

    /// cosh using series, for |x| < 1
    pub(super) fn cosh_series(mut self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        let p = round_p(p);

        // cosh:  1 + x^2/2! + x^4/4! + x^6/6! + ...

        let mut polycoeff_gen = CoshPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<
            CoshPolycoeffGen,
            CoshArgReductionEstimator,
        >(p, &polycoeff_gen, -(self.e as isize), 2, false);

        let p_arg = p + 1 + reduction_times * 6;
        self.set_precision(p_arg, rm)?;

        let arg = if reduction_times > 0 {
            self.cosh_arg_reduce(reduction_times, rm)?
        } else {
            self
        };

        let acc = Self::from_word(1, p_arg)?; // 1
        let x_step = arg.mul(&arg, p_arg, rm)?; // x^2
        let x_first = x_step.clone()?; // x^2

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
        let mut d = THREE.clone()?;
        for _ in 1..n {
            d = d.mul_full_prec(&THREE)?;
        }
        self.div(&d, self.get_mantissa_max_bit_len(), rm)
    }

    // restore value for the argument reduced n times.
    fn cosh_arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // cosh(3*x) = 4*cosh(x)^3 - 3*cosh(x)
        let mut cosh = self.clone()?;
        let p = cosh.get_mantissa_max_bit_len();

        for _ in 0..n {
            let mut cosh_cub = cosh.mul(&cosh, p, rm)?;
            cosh_cub = cosh_cub.mul(&cosh, p, rm)?;
            let p1 = cosh.mul(&THREE, p, rm)?;
            let p2 = cosh_cub.mul(&FOUR, p, rm)?;
            cosh = p2.sub(&p1, p, rm)?;
        }

        Ok(cosh)
    }
}

#[cfg(test)]
mod tests {

    use crate::{common::util::random_subnormal, Sign};

    use super::*;

    #[test]
    fn test_cosh() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, p).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.cosh(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        // asymptotic & extrema testing
        let p = 640;
        let n1 = BigFloatNumber::parse(
            "1.0111001e-1000000",
            crate::Radix::Bin,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let n2 = n1.cosh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("1.000000000000000000000000000000010B6200000000000000000000000000002E8B9840AAAAAAAAAAAAAAAAAAAAAAAAADE85C5950B78E38E38E38E38E38E38E3902814A92D7C21CDB6DB6DB6DB6DB6E_e+0", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        assert!(n2.cmp(&n3) == 0);

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();

        assert!(d1.cosh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Pos));
        assert!(d2.cosh(p, rm, &mut cc).unwrap_err() == Error::ExponentOverflow(Sign::Pos));

        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();
        let d4 = random_subnormal(p);

        assert!(d3.cosh(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(zero.cosh(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(d4.cosh(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn cosh_perf() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, -20, 20).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.cosh(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
