//! Tangent.

use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::common::util::get_add_cost;
use crate::common::util::get_mul_cost;
use crate::common::util::log2_floor;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::ops::series::series_cost_optimize;
use crate::ops::series::ArgReductionEstimator;
use crate::ops::series::PolycoeffGen;

// Polynomial coefficient generator (for tan it only used for cost estmation).
struct TanPolycoeffGen {
    iter_cost: usize,
}

impl TanPolycoeffGen {
    fn new(p: usize) -> Result<Self, Error> {
        let l = log2_floor(p);
        let ll = log2_floor(l) * 3 / 2;
        let iter_cost = (7 * get_mul_cost(p) + 4 * get_add_cost(p)) * ll / l;

        Ok(TanPolycoeffGen { iter_cost })
    }
}

impl PolycoeffGen for TanPolycoeffGen {
    fn next(&mut self, _rm: RoundingMode) -> Result<&BigFloatNumber, Error> {
        Ok(&ONE)
    }

    #[inline]
    fn get_iter_cost(&self) -> usize {
        self.iter_cost
    }
}

struct TanArgReductionEstimator {}

impl ArgReductionEstimator for TanArgReductionEstimator {
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
        ((n as isize) * 1000 / 631 + m) as usize
    }
}

impl BigFloatNumber {
    /// Computes the tangent of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn tan(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let arg = self.reduce_trig_arg(cc, RoundingMode::None)?;

        let mut ret = arg.tan_series(RoundingMode::None)?;

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        Ok(ret)
    }

    fn tan_series(mut self, rm: RoundingMode) -> Result<Self, Error> {
        let p = self.get_mantissa_max_bit_len();
        let polycoeff_gen = TanPolycoeffGen::new(p)?;
        let (reduction_times, _niter) = series_cost_optimize::<
            TanPolycoeffGen,
            TanArgReductionEstimator,
        >(p, &polycoeff_gen, -self.e as isize, 1, true);

        self.set_precision(
            self.get_mantissa_max_bit_len() + reduction_times * 4 + 4,
            rm,
        )?;

        let arg_holder;
        let arg = if reduction_times > 0 {
            arg_holder = self.tan_arg_reduce(reduction_times, rm)?;
            &arg_holder
        } else {
            &self
        };

        let ret = Self::tan_series_run(arg, rm)?;

        if reduction_times > 0 {
            ret.tan_arg_restore(reduction_times, rm)
        } else {
            Ok(ret)
        }
    }

    /// Tangent series
    fn tan_series_run(&self, rm: RoundingMode) -> Result<Self, Error> {
        //  sin + cos series combined

        let mut xx = self.mul(self, rm)?;
        xx.inv_sign();
        let mut xxacc = BigFloatNumber::from_word(1, 1)?;
        let mut fct = BigFloatNumber::from_word(2, 1)?;
        let mut inc = BigFloatNumber::from_word(2, 1)?;
        let mut q1 = BigFloatNumber::from_word(1, 1)?;
        let mut p1 = BigFloatNumber::from_word(1, 1)?;
        let mut q2 = BigFloatNumber::from_word(1, 1)?;
        let mut p2 = BigFloatNumber::from_word(1, 1)?;

        while fct.get_exponent() as isize - (xxacc.get_exponent() as isize)
            <= self.get_mantissa_max_bit_len() as isize
        {
            xxacc = xxacc.mul(&xx, rm)?;

            p1 = p1.mul(&fct, rm)?;
            let n1 = xxacc.mul(&q1, rm)?;
            p1 = p1.add(&n1, rm)?;

            q1 = q1.mul_full_prec(&fct)?;

            inc = inc.add(&ONE, rm)?;
            fct = fct.mul_full_prec(&inc)?;

            p2 = p2.mul(&fct, rm)?;
            let n1 = xxacc.mul(&q2, rm)?;
            p2 = p2.add(&n1, rm)?;

            q2 = q2.mul_full_prec(&fct)?;

            inc = inc.add(&ONE, rm)?;
            fct = fct.mul_full_prec(&inc)?;
        }

        let n0 = p2.mul(self, rm)?;
        let n1 = n0.mul(&q1, rm)?;
        let n2 = p1.mul(&q2, rm)?;
        n1.div(&n2, rm)
    }

    // reduce argument n times.
    fn tan_arg_reduce(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // tan(3*x) = 3*tan(x) - tan(x)^3 / (1 - 3*tan(x)^2)
        let mut ret = self.clone()?;
        for _ in 0..n {
            ret = ret.div(&THREE, rm)?;
        }
        Ok(ret)
    }

    // restore value for the argument reduced n times.
    fn tan_arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // tan(3*x) = 3*tan(x) - tan(x)^3 / (1 - 3*tan(x)^2)

        let mut val = self.clone()?;

        for _ in 0..n {
            let val_sq = val.mul(&val, rm)?;
            let val_cub = val_sq.mul(&val, rm)?;

            let p1 = val.mul(&THREE, rm)?;
            let p2 = p1.sub(&val_cub, rm)?;
            let p3 = val_sq.mul(&THREE, rm)?;
            let p4 = ONE.sub(&p3, rm)?;

            val = p2.div(&p4, rm)?;
        }

        Ok(val)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_tan() {
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(2, 320).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.tan(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // asymptotic & extrema testing
        let mut half_pi = cc.pi(128, RoundingMode::None).unwrap();
        half_pi.set_exponent(0);
        half_pi.set_precision(320, RoundingMode::None).unwrap();

        let n2 = half_pi.tan(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFADFB63EEEB306717FBE882B389D8C9BB6A8F6914FC1931BD_e-1",
            crate::Radix::Hex,
            640,
            RoundingMode::None,
        )
        .unwrap();

        assert!(n2.cmp(&n3) == 0);

        // large exponent
        half_pi.set_exponent(256);
        let n2 = half_pi.tan(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("4.ECDEC5EF3A1EA5339A46BC0C490F52A86A033C56BCDD413E36C657EB7757F073500B013B9A7B43D8_e+0", crate::Radix::Hex, 640, RoundingMode::None).unwrap();

        assert!(n2.cmp(&n3) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn tan_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(160, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.tan(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
