//! Sine.

use crate::common::consts::FOUR;
use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::common::util::calc_add_cost;
use crate::common::util::calc_mul_cost;
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
use crate::Sign;
use crate::WORD_BIT_SIZE;

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

        let iter_cost =
            (calc_mul_cost(p) + calc_add_cost(p) + calc_add_cost(inc.mantissa_max_bit_len())) * 2;

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
        let p_inc = self.inc.mantissa_max_bit_len();
        let p_one = self.one_full_p.mantissa_max_bit_len();

        self.inc = self.inc.add(&ONE, p_inc, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, p_one, rm)?;
        self.fct = self.fct.mul(&inv_inc, p_one, rm)?;

        self.inc = self.inc.add(&ONE, p_inc, rm)?;
        let inv_inc = self.one_full_p.div(&self.inc, p_one, rm)?;
        self.fct = self.fct.mul(&inv_inc, p_one, rm)?;

        self.sign *= -1;
        if self.sign > 0 {
            self.fct.set_sign(Sign::Pos);
        } else {
            self.fct.set_sign(Sign::Neg);
        }

        Ok(&self.fct)
    }

    #[inline]
    fn iter_cost(&self) -> usize {
        self.iter_cost
    }
}

struct SinArgReductionEstimator {}

impl ArgReductionEstimator for SinArgReductionEstimator {
    /// Estimates cost of reduction n times for number with precision p.
    fn reduction_cost(n: usize, p: usize) -> u64 {
        let cost_mul = calc_mul_cost(p);
        let cost_add = calc_add_cost(p);
        let cost_mul2 = calc_mul_cost(THREE.mantissa_max_bit_len());

        n as u64 * (2 * cost_mul + 3 * cost_add + cost_mul2) as u64
    }

    /// Given m, the negative power of 2 of a number, returns the negative power of 2 if reduction is applied n times.
    #[inline]
    fn reduction_effect(n: usize, m: isize) -> usize {
        // n*log2(3) + m
        ((n as isize) * 1000 / 631 + m) as usize
    }
}

impl BigFloatNumber {
    /// Computes the sine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn sin(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            return Self::new2(p, self.sign(), self.inexact());
        }

        compute_small_exp!(self, self.exponent() as isize * 2 - 2, true, p, rm);

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p.max(self.mantissa_max_bit_len()) + p_inc;

        loop {
            let mut x = self.clone()?;

            let p_x = p_wrk + 3;
            x.set_precision(p_x, RoundingMode::None)?;

            x = x.reduce_trig_arg(cc, RoundingMode::None)?;

            let mut ret = x.sin_series(RoundingMode::None)?;

            if ret.try_set_precision(p, rm, p_wrk)? {
                break Ok(ret);
            }

            p_wrk += p_inc;
            p_inc = round_p(p_wrk / 5);
        }
    }

    /// sine using series
    pub fn sin_series(mut self, rm: RoundingMode) -> Result<Self, Error> {
        // sin:  x - x^3/3! + x^5/5! - x^7/7! + ...

        let p = self.mantissa_max_bit_len();

        let mut polycoeff_gen = SinPolycoeffGen::new(p)?;
        let (reduction_times, niter, e_eff) = series_cost_optimize::<SinArgReductionEstimator>(
            p,
            &polycoeff_gen,
            -(self.exponent() as isize),
            2,
            false,
        );

        // Reduction gives 2^(-p+3) once.
        // Restore gives 2^(-p+6) per iteration.
        // First terms of the series for any e_eff >= 0 give 2^(-p+6) at most.
        // The error of the remaining terms of the series is compensated (see doc/README.md).
        let add_prec = reduction_times as isize * 6 + 9 - e_eff as isize;
        let p_arg = p + if add_prec > 0 { add_prec as usize } else { 0 };
        self.set_precision(p_arg, rm)?;

        let arg = if reduction_times > 0 {
            self.sin_arg_reduce(reduction_times, rm)?
        } else {
            self
        };

        let acc = arg.clone()?; // x
        let x_step = arg.mul(&arg, p_arg, rm)?; // x^2
        let x_first = arg.mul(&x_step, p_arg, rm)?; // x^3

        let ret = series_run(acc, x_first, x_step, niter, &mut polycoeff_gen)?;

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
        let mut d = THREE.clone()?;
        for _ in 1..n {
            d = d.mul_full_prec(&THREE)?;
        }
        self.div(&d, self.mantissa_max_bit_len(), rm)
    }

    // restore value for the argument reduced n times.
    // cost: n * (4*O(mul) + O(add))
    fn sin_arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sin(3*x) = 3*sin(x) - 4*sin(x)^3
        let mut sin = self.clone()?;
        let p = sin.mantissa_max_bit_len();

        for _ in 0..n {
            let mut sin_cub = sin.mul(&sin, p, rm)?;
            sin_cub = sin_cub.mul(&sin, p, rm)?;
            let p1 = sin.mul(&THREE, p, rm)?;
            let p2 = sin_cub.mul(&FOUR, p, rm)?;
            sin = p1.sub(&p2, p, rm)?;
        }

        Ok(sin)
    }
}

#[cfg(test)]
mod tests {

    use crate::common::util::random_subnormal;

    use super::*;

    #[test]
    fn test_sine() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(5, p).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.sin(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // asymptotic & extrema testing
        let mut half_pi = cc.pi_num(128, RoundingMode::None).unwrap();
        half_pi.set_exponent(1);
        half_pi.set_precision(p, RoundingMode::None).unwrap();

        let n2 = half_pi.sin(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            640,
            RoundingMode::None,
            &mut cc,
        )
        .unwrap();

        assert!(n2.cmp(&n3) == 0);

        // large exponent
        half_pi.set_exponent(256);
        let n2 = half_pi.sin(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse(
            "F.AE195882CABDC16FAF2A733AB99159AF50C47E8B9ED8BA42C5872FF88A52726061B4231170F1BE8_e-1",
            crate::Radix::Hex,
            640,
            RoundingMode::None,
            &mut cc,
        )
        .unwrap();

        //println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // small exponent
        let p = 384;
        let d1 = BigFloatNumber::parse("-4.6C7B4339E519CAFC9C58869B348D66FD510B4E74F0A6476126B55FD73F5533C7B84C5733C34BB312677AE7C015A666D0_e-17", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();
        let d2 = d1.sin(p, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse("-4.6C7B4339E519CAFC9C58869B348D66FD510B4E74F0A638F3725423CE43E0D375A6FEE810D77915E6EA2D8EE32EBCF618_e-17", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();
        let n1 = random_subnormal(p);

        assert!(d3.sin(p, rm, &mut cc).unwrap().cmp(&d3) == 0);
        assert!(zero.sin(p, rm, &mut cc).unwrap().is_zero());
        assert!(n1.sin(p, rm, &mut cc).unwrap().cmp(&n1) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn sine_perf() {
        let p = 133;
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, -5, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.sin(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
