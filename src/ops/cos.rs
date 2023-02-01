//! Cosine.

use crate::common::consts::C24;
use crate::common::consts::ONE;
use crate::common::consts::TWO;
use crate::common::util::get_add_cost;
use crate::common::util::get_mul_cost;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::defs::EXPONENT_MIN;
use crate::defs::WORD_BIT_SIZE;
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::ops::series::series_cost_optimize;
use crate::ops::series::series_run;
use crate::ops::series::ArgReductionEstimator;
use crate::ops::series::PolycoeffGen;
use crate::Exponent;
use crate::Sign;

const COS_EXP_THRES: Exponent = -(WORD_BIT_SIZE as Exponent);

// Polynomial coefficient generator.
struct CosPolycoeffGen {
    one_full_p: BigFloatNumber,
    inc: BigFloatNumber,
    fct: BigFloatNumber,
    sign: i8,
    iter_cost: usize,
}

impl CosPolycoeffGen {
    fn new(p: usize) -> Result<Self, Error> {
        let inc = BigFloatNumber::new(1)?;
        let fct = BigFloatNumber::from_word(1, p)?;
        let one_full_p = BigFloatNumber::from_word(1, p)?;

        let iter_cost =
            (get_mul_cost(p) + get_add_cost(p) + get_add_cost(inc.get_mantissa_max_bit_len())) * 2;

        let sign = 1;

        Ok(CosPolycoeffGen {
            one_full_p,
            inc,
            fct,
            sign,
            iter_cost,
        })
    }
}

impl PolycoeffGen for CosPolycoeffGen {
    fn next(&mut self, rm: RoundingMode) -> Result<&BigFloatNumber, Error> {
        let p_inc = self.inc.get_mantissa_max_bit_len();
        let p_one = self.one_full_p.get_mantissa_max_bit_len();

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
    fn get_iter_cost(&self) -> usize {
        self.iter_cost
    }
}

struct CosArgReductionEstimator {}

impl ArgReductionEstimator for CosArgReductionEstimator {
    /// Estimates cost of reduction n times for number with precision p.
    fn get_reduction_cost(n: usize, p: usize) -> usize {
        // n * (cost(add) + cost(mul))
        let cost_mul = get_mul_cost(p);
        let cost_add = get_add_cost(p);
        n * (cost_mul + cost_add)
    }

    /// Given m, the negative power of 2 of a number, returns the negative power of 2 if reduction is applied n times.
    #[inline]
    fn reduction_effect(n: usize, m: isize) -> usize {
        // n + m
        ((n as isize) + m) as usize
    }
}

impl BigFloatNumber {
    /// Computes the cosine of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn cos(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            return Self::from_word(1, p);
        }

        if (self.get_exponent() as isize) < -(p as isize) / 6 {
            // short series: 1 - x^2/2! + x^4/4!

            let mut x = self.clone()?;

            let p_x = p.max(x.get_mantissa_max_bit_len()) + 8;
            x.set_precision(p_x, RoundingMode::None)?;

            let xx = x.mul(&x, p_x, RoundingMode::None)?;

            let mut p1 = xx.clone()?;
            p1.div_by_2(RoundingMode::None);

            let mut ret = if p1.is_zero() {
                // p1 is too small, but still enought for rounding
                let one = Self::from_word(1, p_x)?;
                one.add_correction(true)
            } else {
                x = ONE.sub(&p1, p_x, RoundingMode::ToZero)?;

                let x4 = xx.mul(&xx, p_x, RoundingMode::None)?;
                let p2 = x4.div(&C24, p_x, RoundingMode::None)?;

                if p2.is_zero() {
                    x.add_correction(false)
                } else {
                    x.add(
                        &p2,
                        x.get_mantissa_max_bit_len() + 1,
                        RoundingMode::FromZero,
                    )
                }
            }?;

            ret.set_precision(p, rm)?;

            Ok(ret)

        } else {
            let p_inc = WORD_BIT_SIZE;
            let mut p_wrk = p.max(self.get_mantissa_max_bit_len()) + p_inc;

            let mut add_p = (1 - COS_EXP_THRES) as usize;
            loop {
                let mut x = self.clone()?;

                let p_x = p_wrk + add_p;
                x.set_precision(p_x, RoundingMode::None)?;

                x = x.reduce_trig_arg(cc, RoundingMode::None)?;

                let mut ret = x.cos_series(RoundingMode::None, false)?;

                let t = ret.get_exponent().unsigned_abs() as usize + 1;
                if add_p < t {
                    add_p = t;
                } else {
                    if ret.try_set_precision(p, rm, p_wrk)? {
                        break Ok(ret);
                    }

                    p_wrk += p_inc;
                }
            }
        }  
    }

    /// cosine series
    pub(super) fn cos_series(
        mut self,
        rm: RoundingMode,
        with_correction: bool,
    ) -> Result<Self, Error> {
        // cos:  1 - x^2/2! + x^4/4! - x^6/6! + ...

        let p = self.get_mantissa_max_bit_len();
        let mut polycoeff_gen = CosPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<CosArgReductionEstimator>(
            p,
            &polycoeff_gen,
            -(self.e as isize),
            2,
            false,
        );

        let p_arg = p + niter * 4 + reduction_times * 3;
        self.set_precision(p_arg, rm)?;

        let arg = if reduction_times > 0 {
            self.cos_arg_reduce(reduction_times, rm)?
        } else {
            self
        };

        let acc = BigFloatNumber::from_word(1, p_arg)?; // 1
        let x_step = arg.mul(&arg, p_arg, rm)?; // x^2
        let x_first = x_step.clone()?; // x^2

        let ret = series_run(
            acc,
            x_first,
            x_step,
            niter,
            &mut polycoeff_gen,
            with_correction,
        )?;

        if reduction_times > 0 {
            ret.cos_arg_restore(reduction_times, rm)
        } else {
            Ok(ret)
        }
    }

    // reduce argument n times.
    // cost: n * O(add)
    fn cos_arg_reduce(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // cos(2*x) = 2*cos(x)^2 - 1
        let mut ret = self.clone()?;
        let p = ret.get_mantissa_max_bit_len();
        if ret.get_exponent() < EXPONENT_MIN + n as Exponent {
            ret.set_exponent(EXPONENT_MIN);
            for _ in 0..n - (ret.get_exponent() - EXPONENT_MIN) as usize {
                ret = ret.div(&TWO, p, rm)?;
            }
        } else {
            ret.set_exponent(ret.get_exponent() - n as Exponent);
        }
        Ok(ret)
    }

    // restore value for the argument reduced n times.
    // cost: n * (4*O(mul) + O(add))
    fn cos_arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // cos(2*x) = 2*cos(x)^2 - 1
        let mut cos = self.clone()?;
        let p = cos.get_mantissa_max_bit_len();

        for _ in 0..n {
            let mut cos2 = cos.mul(&cos, p, rm)?;
            cos2.set_exponent(cos2.get_exponent() + 1);
            cos = cos2.sub(&ONE, p, rm)?;
        }

        Ok(cos)
    }
}

#[cfg(test)]
mod tests {

    use crate::common::util::random_subnormal;

    use super::*;

    #[test]
    fn test_cosine() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, 320).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.cos(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // asymptotic & extrema testing
        let mut half_pi = cc.pi_num(128, RoundingMode::None).unwrap();
        half_pi.set_exponent(1);
        half_pi.set_precision(p, RoundingMode::None).unwrap();

        let n2 = half_pi.cos(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("5.2049C1114CF98E804177D4C76273644A29410F31C6809BBDF2A33679A7486365EEEE1A43A7D13E58_e-21", crate::Radix::Hex, 640, RoundingMode::None).unwrap();

        //println!("{:?}", n2.format(crate::Radix::Bin, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // large exponent
        half_pi.set_exponent(256);
        let n2 = half_pi.cos(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("3.2F00069261A9FFC022D09F662F2E2DDBEFD1AF138813F2A71D7601C58E793299EA052E4EBC59107C_e-1", crate::Radix::Hex, 640, RoundingMode::None).unwrap();

        //println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        // small exponent
        let p = 384;
        let n1 = BigFloatNumber::parse("1.992EF09686C3DC782C05BFD7863A715ECBDAED45DBAEE3ADFEF1AB8F74DB393D8CD6EAF9CA8443A6C28CF59D35B7FF56_e-20", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.cos(p, RoundingMode::ToEven, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEB8FC7D51D69792F9AB263F754D161F6A_e-1", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();
        let d4 = random_subnormal(p);

        assert!(d3.cos(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(zero.cos(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(d4.cos(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn cosine_perf() {
        let p = 640;
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, -5, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.cos(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
