//! Logarithm.

use crate::common::consts::ONE;
use crate::common::consts::TEN;
use crate::common::consts::TWO;
use crate::common::util::count_leading_ones;
use crate::common::util::count_leading_zeroes_skip_first;
use crate::common::util::get_add_cost;
use crate::common::util::get_mul_cost;
use crate::common::util::get_sqrt_cost;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::defs::Sign;
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::ops::series::series_cost_optimize;
use crate::ops::series::series_run;
use crate::ops::series::ArgReductionEstimator;
use crate::ops::series::PolycoeffGen;
use crate::Exponent;
use crate::WORD_BIT_SIZE;

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

        let iter_cost = get_add_cost(p) + get_add_cost(acc.get_mantissa_max_bit_len());

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
        self.acc = self
            .acc
            .add(&TWO, self.acc.get_mantissa_max_bit_len(), rm)?;
        self.val =
            self.one_full_p
                .div(&self.acc, self.one_full_p.get_mantissa_max_bit_len(), rm)?;

        Ok(&self.val)
    }

    #[inline]
    fn get_iter_cost(&self) -> usize {
        self.iter_cost
    }
}

struct LnArgReductionEstimator {}

impl ArgReductionEstimator for LnArgReductionEstimator {
    /// Estimates cost of reduction n times for number with precision p.
    fn get_reduction_cost(n: usize, p: usize) -> usize {
        // cost(shift) + n*cost(sqrt)
        let cost_mul = get_mul_cost(p);
        let cost_add = get_add_cost(p);
        let sqrt_cost = get_sqrt_cost(p, cost_mul, cost_add);

        n * sqrt_cost
    }

    /// Given m, the negative power of 2 of a number, returns the negative power of 2 if reduction is applied n times.
    #[inline]
    fn reduction_effect(n: usize, m: isize) -> usize {
        (m + n as isize) as usize
    }
}

impl BigFloatNumber {
    /// Computes the natural logarithm of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the argument is zero or negative, or the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn ln(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        // factoring: ln(self) = ln(x * 2^n) = ln(x) + n*ln(2), 0.5 <= x < 1
        // reduction: ln(x) = 2*ln(sqrt(x))
        // replacement: ln(x) = 2*atanh((x-1)/(x+1))
        // atanh(x) = x + x^3/3 + x^5/5 + ...

        if self.is_zero() || self.is_negative() {
            return Err(Error::InvalidArgument);
        }

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        loop {
            let mut x = self.clone()?;
            let e = x.normalize2() as isize;
            let e = self.get_exponent() as isize - e;

            x.set_exponent(0);

            let additional_prec = if e == 0 {
                count_leading_ones(x.get_mantissa_digits())
            } else if e == 1 {
                count_leading_zeroes_skip_first(x.get_mantissa_digits())
            } else {
                0
            } + 2;

            // test for one.
            if e == 1 && additional_prec == x.get_mantissa_max_bit_len() + 2 {
                return Self::new(p);
            }

            let p_ext = p_wrk + additional_prec;
            x.set_precision(p_ext, RoundingMode::None)?;

            let p1 = Self::ln_series(x, RoundingMode::None)?;

            let mut ret = if e == 0 {
                p1
            } else {
                let p2 = cc.ln_2_num(p_ext, RoundingMode::None)?;

                let mut n = Self::from_usize(e.unsigned_abs())?;
                if e < 0 {
                    n.set_sign(Sign::Neg);
                }

                let p2n = p2.mul(&n, p_ext, RoundingMode::None)?;
                p1.add(&p2n, p_ext, RoundingMode::None)?
            };

            if ret.try_set_precision(p, rm, p_wrk)? {
                return Ok(ret);
            }

            p_wrk += p_inc;
            p_inc *= 2;
        }
    }

    fn ln_series(mut x: Self, rm: RoundingMode) -> Result<Self, Error> {
        let p = x.get_mantissa_max_bit_len();
        let mut polycoeff_gen = AtanhPolycoeffGen::new(p)?;
        let (reduction_times, niter) =
            series_cost_optimize::<LnArgReductionEstimator>(p, &polycoeff_gen, 0, 2, false);

        let err = reduction_times + 4;
        let p = x.get_mantissa_max_bit_len() + err;
        x.set_precision(p, rm)?;

        let arg = if reduction_times > 0 {
            Self::ln_arg_reduce(x, reduction_times, rm)?
        } else {
            x
        };

        // x-1 / x+1
        let x1 = arg.sub(&ONE, p, rm)?;
        let x2 = arg.add(&ONE, p, rm)?;
        let z = x1.div(&x2, p, rm)?;

        let x_step = z.mul(&z, p, rm)?; // x^2
        let x_first = z.mul(&x_step, p, rm)?; // x^3

        let ret = series_run(z, x_first, x_step, niter, &mut polycoeff_gen)?;

        Self::ln_arg_restore(ret, reduction_times + 1)
    }

    // reduce argument n times.
    fn ln_arg_reduce(mut x: Self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        for _ in 0..n {
            x = x.sqrt(x.get_mantissa_max_bit_len(), rm)?;
        }

        Ok(x)
    }

    // restore value for the argument reduced n times.
    fn ln_arg_restore(mut x: Self, n: usize) -> Result<Self, Error> {
        x.set_exponent(x.get_exponent() + n as Exponent);

        Ok(x)
    }

    /// Computes the logarithm base 2 of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the argument is zero or negative, or the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn log2(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        // factoring: log2(self) = ln(x * 2^n) / ln(2) = ln(x) / ln(2) + n, 0.5 <= x < 1
        // reduction: ln(x) = 2 * ln(sqrt(x))
        // replacement: ln(x) = 2*atanh((x-1)/(x+1))
        // atanh(x) = x + x^3/3 + x^5/5 + ...

        if self.is_zero() || self.is_negative() {
            return Err(Error::InvalidArgument);
        }

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        loop {
            let mut x = self.clone()?;
            let e = x.normalize2() as isize;
            let e = self.get_exponent() as isize - e;

            x.set_exponent(0);

            let zeroes_cnt = count_leading_zeroes_skip_first(x.get_mantissa_digits());
            if zeroes_cnt == x.get_mantissa_max_bit_len() {
                // special case x = 0.5
                let mut ret = Self::from_usize((e - 1).unsigned_abs())?;
                if e < 1 {
                    ret.set_sign(Sign::Neg);
                }
                ret.set_precision(p, rm)?;
                return Ok(ret);
            }

            let additional_prec = if e == 0 {
                count_leading_ones(x.get_mantissa_digits())
            } else if e == 1 {
                zeroes_cnt
            } else {
                0
            } + 2;

            let p_ext = p_wrk + additional_prec;
            x.set_precision(p_ext, RoundingMode::None)?;

            let p1 = Self::ln_series(x, RoundingMode::None)?;

            let p2 = cc.ln_2_num(p_ext, RoundingMode::None)?;

            let p3 = p1.div(&p2, p_ext, RoundingMode::None)?;

            let mut n = Self::from_usize(e.unsigned_abs())?;
            if e < 0 {
                n.set_sign(Sign::Neg);
            }

            let mut ret = p3.add(&n, p_ext, RoundingMode::None)?;

            if ret.try_set_precision(p, rm, p_wrk)? {
                return Ok(ret);
            }

            p_wrk += p_inc;
            p_inc *= 2;
        }
    }

    /// Computes the logarithm base 10 of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the argument is zero or negative, or the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn log10(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        // ln(self) / ln(10)

        let mut x = self.clone()?;

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        loop {
            let p_ext = p_wrk + 2;
            x.set_precision(p_ext, RoundingMode::None)?;

            let p1 = x.ln(p_ext, RoundingMode::None, cc)?;

            let p2 = cc.ln_10_num(p_ext, RoundingMode::None)?;

            let mut ret = p1.div(&p2, p_ext, RoundingMode::None)?;

            // check if x is exactly power of 10
            if ret.is_int() {
                let n = ret.get_int_as_usize()?;
                let tp = TEN.powi(n, p_ext, RoundingMode::None)?;
                if tp.cmp(&x) == 0 {
                    ret.set_precision(p, rm)?;
                    return Ok(ret);
                }
            }

            if ret.try_set_precision(p, rm, p_wrk)? {
                return Ok(ret);
            }

            p_wrk += p_inc;
            p_inc *= 2;
        }
    }

    /// Computes the logarithm base `n` of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: the argument is zero or negative, or the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - DivisionByZero: `n` = 1
    pub fn log(
        &self,
        n: &Self,
        p: usize,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<Self, Error> {
        let p = round_p(p);

        // ln(self) / ln(n)

        let mut x = self.clone()?;

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        loop {
            let p_ext = p_wrk + 2;

            x.set_precision(p_ext, RoundingMode::None)?;

            let mut n = n.clone()?;
            n.set_precision(p_ext, RoundingMode::None)?;

            let p1 = x.ln(p_ext, RoundingMode::None, cc)?;

            let p2 = n.ln(p_ext, RoundingMode::None, cc)?;

            let mut ret = p1.div(&p2, p_ext, RoundingMode::None)?;

            let pwr = n.pow(&ret, p_ext, RoundingMode::None, cc)?;
            if pwr.cmp(&x) == 0 {
                ret.set_precision(p, rm)?;
                return Ok(ret);
            }

            if ret.try_set_precision(p, rm, p_wrk)? {
                return Ok(ret);
            }

            p_wrk += p_inc;
            p_inc *= 2;
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        common::{
            consts::TEN,
            util::{log2_ceil, random_subnormal},
        },
        WORD_BIT_SIZE,
    };

    use super::*;

    #[cfg(not(feature = "std"))]
    use alloc::vec::Vec;

    #[test]
    fn test_logarithm() {
        let mut cc = Consts::new().unwrap();

        let rm = RoundingMode::ToEven;
        let p = 3200;
        let n1 = BigFloatNumber::from_word(123, p).unwrap();

        let mut n2 = n1.ln(p, rm, &mut cc).unwrap();
        n2.set_sign(Sign::Pos);

        //println!("{:?}", n2.fp3(crate::Radix::Dec, rm).unwrap());

        // near 1
        let p = 320;
        let d1 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC4872DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.ln(p, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse("-D.237A0818813B78D237A0818813B7900000000000000000000564FA7B56FC57E9FBF3EE86C58F3F4_e-33", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        let d1 = BigFloatNumber::parse(
            "1.00000000000000000000000000000000000000000000000000000000000000002DC85F7E77EC487C",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.ln(p, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse("2.DC85F7E77EC487BFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFBE7F8CC184E38EBC_e-41", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        // MAX
        let prec = 3200;
        let mut eps = ONE.clone().unwrap();

        let d1 = BigFloatNumber::max_value(prec).unwrap();
        let d2 = d1.ln(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = d2.exp(prec, RoundingMode::ToEven, &mut cc).unwrap();
        eps.set_exponent(
            d1.get_exponent() - prec as Exponent
                + log2_ceil(d1.get_exponent().unsigned_abs() as usize) as Exponent,
        );

        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );

        let d2 = d1.log2(prec, RoundingMode::ToEven, &mut cc).unwrap();
        match TWO.pow(&d2, prec, RoundingMode::ToEven, &mut cc) {
            Ok(d3) => {
                eps.set_exponent(
                    d1.get_exponent() - prec as Exponent
                        + log2_ceil(d1.get_exponent().unsigned_abs() as usize) as Exponent,
                );

                assert!(
                    d1.sub(&d3, prec, RoundingMode::ToEven)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps)
                        < 0
                );
            }
            Err(e) => {
                if e != Error::ExponentOverflow(Sign::Pos) {
                    panic!("unexpected error");
                }
            }
        }

        let d2 = d1.log10(prec, RoundingMode::ToEven, &mut cc).unwrap();
        match TEN.pow(&d2, prec, RoundingMode::ToEven, &mut cc) {
            Ok(d3) => {
                eps.set_exponent(
                    d1.get_exponent() - prec as Exponent
                        + log2_ceil(d1.get_exponent().unsigned_abs() as usize) as Exponent,
                );

                assert!(
                    d1.sub(&d3, prec, RoundingMode::ToEven)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps)
                        < 0
                );
            }
            Err(e) => {
                if e != Error::ExponentOverflow(Sign::Pos) {
                    panic!("unexpected error");
                }
            }
        }

        // MIN
        let d1 = BigFloatNumber::min_positive(prec).unwrap();
        let d2 = d1.ln(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = d2.exp(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let eps = BigFloatNumber::min_positive_normal(prec).unwrap();

        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                <= 0
        );

        // random subnormal arg
        let mut eps = ONE.clone().unwrap();
        for _ in 0..1000 {
            let prec = (rand::random::<usize>() % 3 + 3) * WORD_BIT_SIZE;

            let mut d1 = random_subnormal(prec);
            d1.set_sign(Sign::Pos);
            let mut d2 = d1.ln(prec, RoundingMode::ToEven, &mut cc).unwrap();
            let d2e = d2.get_exponent();
            d2.set_exponent(d2e / 2 + (d2e & 1));
            let d3 = d2.exp(prec + 1, RoundingMode::None, &mut cc).unwrap();
            let d4 = d3.powi(1 << (d2e / 2), prec, RoundingMode::ToEven).unwrap();

            eps.set_exponent(d2e - prec as Exponent);
            let err = eps.exp(prec, RoundingMode::Up, &mut cc).unwrap();

            // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
            // println!("{:?}", d4.mul(&err, prec, RoundingMode::Up).unwrap().format(crate::Radix::Bin, RoundingMode::None).unwrap());
            // println!("{:?}", d4.div(&err, prec, RoundingMode::Down).unwrap().format(crate::Radix::Bin, RoundingMode::None).unwrap());

            // d2 - ulp(d2)/2 <= ln(d1) <= d2 + ulp(d2)/2  ->  d3 / e^(ulp(d2)/2) <= d1 <= d3 * e^(ulp(d2)/2)
            assert!(d1.cmp(&d4.mul(&err, prec, RoundingMode::Up).unwrap()) <= 0);
            assert!(d1.cmp(&d4.div(&err, prec, RoundingMode::Down).unwrap()) >= 0);
        }

        let d1 = BigFloatNumber::min_positive(prec).unwrap();
        let d2 = d1.log2(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = TWO.pow(&d2, prec, RoundingMode::ToEven, &mut cc).unwrap();
        let eps = BigFloatNumber::min_positive_normal(prec).unwrap();

        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                <= 0
        );

        let d1 = BigFloatNumber::min_positive(prec).unwrap();
        let d2 = d1.log10(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = TEN.pow(&d2, prec, RoundingMode::ToEven, &mut cc).unwrap();
        let eps = BigFloatNumber::min_positive_normal(prec).unwrap();

        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                <= 0
        );

        // arbitrary base
        assert!(TWO.log(&ONE, p, rm, &mut cc).unwrap_err() == Error::DivisionByZero);

        let d1 = BigFloatNumber::min_positive(prec).unwrap();
        let d2 = BigFloatNumber::max_value(prec).unwrap();

        assert!(d1.log(&d1, prec, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(d2.log(&d2, prec, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(d1.log(&d2, prec, rm, &mut cc).is_ok());
        assert!(d2.log(&d1, prec, rm, &mut cc).is_ok());

        // base close to 0, 1, or a large value
        let mut nums = Vec::new();
        for s in [
            "1.23456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF12_e-100000",
            "0.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF123456789ABCDEF0123456789ABCDEF12_e+0",
            "1.0000000000000000000000000000000123456789ABCDEF0123456789ABCDEF12_e+0",
            "1.23456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF12_e+100000",
            "1.23456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF12_e+1000",
            "1.23456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF12_e-1000",
        ] {
            nums.push(
                BigFloatNumber::parse(s, crate::Radix::Hex, 256, RoundingMode::None).unwrap(),
            );
        }

        let mediumsmall = nums.pop().unwrap();
        let mediumlarge = nums.pop().unwrap();
        let large = nums.pop().unwrap();
        let above1 = nums.pop().unwrap();
        let below1 = nums.pop().unwrap();
        let small = nums.pop().unwrap();

        // base close to 0
        let s = "1.010101110001000100000101000110000000101010001001001111001011001001110000010000010010001101010111001111111000100110100110101001101111010011000110111101011100010000100111001110000111100110011011111100001111100011001110011110001001111111110000100101001110001e-10010010";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = below1
            .log(&small, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.10100100001101110010010011011100100001110110010010111001011000010000000000010101000100100011101000011010111010110000011111001101111011110100010100101111100110110111101100111100010011000100101011101111100001110011100001111101101110011000001001100010101101e-10010110";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = above1
            .log(&small, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.000000000000000000000001011111010110000001001010100010010000111110010100111100100000000111110011101100111000000010001001011010001110100011001001111010101111000111010010000011000110011011011101101001001010011011010111011011010001110100000010100100001001001e+0";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = large
            .log(&small, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "1.111111111111111010000100000111010001010111000001011110010111101010100010111100000000111001000000001100101111011100100000100000000001111011011110111110010001111111000101101001011000100100111000111111011100111101101010010100000001101001110001111111110100101e-1001";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = mediumsmall
            .log(&small, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.00000000000000001011111101101110110101010110100111001100010100100100001101111001111110101101001110011010000001001111100100101000110110010101101001101110011000011110111100111001101000100100000100100101101111110010001001000101000011111100100110010000111011e-1000";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = mediumlarge
            .log(&small, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        // base close to 1
        let s = "1.01111110000011110101111111010000100100110001110110101100011100010101010010001100000100011011011100010111000011100111111010100000010001001111111000010111001000011000011110001110011001001011010101111111100110001000000011011111101111001110100010010101001101e+10010001";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = small
            .log(&below1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.001110011001000111000010110000011000011111110110001100100011010101110000000001101101100001100011010000011001111101001101000010001001100010000001111001011000000000111110110101101111010100100000001001100110111110111010000000001000000011100100110110001001011e-100";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = above1
            .log(&below1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.01111110000011110110001000001001101111111011010001000110110010011010110010100010101010100110101010110000000101100010011000110001000111001100010011010011010111101011101010110100001110101100100000111001110011010011001101001001000001100100110010000001111101e+10010001";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = large
            .log(&below1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "1.011111100000111001000100010101101101111000011011110011010111000101110101010010110000010001000100010111111011111010001001111111001100110110000011010101101010011010001110001101100100011001100001110000100101100110100101011011111010111110100100001011000001e+10001001";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = mediumsmall
            .log(&below1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.0111111000010000011111011000001101110100101101100010010111001001100010111110001110110111110111010110011101100110000110101101010010010100001111111001001111011001101101000000110001011001000110111111011100001100000011101011100100010011100100001110101100011e+10001001";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = mediumlarge
            .log(&below1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        // base close to 1
        let s = "-1.00110111111010101000110100111001010010000001101100111011000000110101010011010001010111010110001010110010000101110100010001010101011011100101100101010101001111110010011110001010100010110111110010010011001111000000001100110011010101100000010101101010001e+10010101";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = small
            .log(&above1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.10100010000000000000000000000000000000000000000000000001101001011110000000000000000000000000000000000000000000011000110100011010111000101101110000000000000000000000000101110101101111010011101001011100100000000000000000000001010111111011111010110100000101e+11";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = below1
            .log(&above1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "1.0011011111101010100011110000100111110101100000100010111100000101011101001011110110100101000010010111111101011110010100010100110111000101010110100111101001011111010000011001111000001010110011011001011101101111111100010111101010100011001010100000001001001e+10010101";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = large
            .log(&above1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.001101111110100110100101110010101110101101010100101100111111010001101110101000111010110111001111011101010011010001001110101001100001100101000111010101111100001000101010110101001010001010100010111110110101111011010110101100000110101001001011101000100100111e+10001101";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = mediumsmall
            .log(&above1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "1.00110111111010110111011001111000010100100100100010110110000101000101101011101011010101001001110010111100010000010100011011111101000110100110110001110111110111000011111001010011111100111010011100101111010011010001110111111101100011101110001111001010000111e+10001101";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = mediumlarge
            .log(&above1, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        // large base
        let s = "-1.111111111111111111111101000001010011111101101111010111100011000001010011101001110001010000100011001101110111010000110100011100111000001001101110000001111000000100110110110001001101001110101000000101010111111000100101110100000111101010010101000110001001001e-1";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = small
            .log(&large, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.010101110001000100000011000110001111010100101101010111001100110001001110010101000111010100110100100101010000101011110011001001010101000101110000001101010100011001100111100000000111111110100000001111010111001101000101100101111010110011111001011000101110001e-10010010";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = below1
            .log(&large, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "1.1010010000110111001000100110101010000011010001110111101100001000101001011000101100010001110101111001111110100010100101100110011110011111001101110001000111011101100101101011001001000100111111011101100010100010111110100000101100010010000100000000111100001e-10010110";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = above1
            .log(&large, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "-1.111111111111111010000001001000100101011101100110110001110100000111111101010111011001101110101101010101011101010001010011111110101111100000111010110001000101101111111101110011000011110111011110110010011101000111111011001001011000011111010110110101010101011e-1001";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = mediumsmall
            .log(&large, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);

        let s = "1.000000000000000010111101111100010111010000000100010010110111011100101011001001001011110000111010111100001100111111110000001111000100010100011001101000011001001010011100011111000100101011100100101001011101011000010101010101010111100101011111001000011001111e-1000";
        let refn = BigFloatNumber::parse(s, crate::Radix::Bin, 256, RoundingMode::None).unwrap();
        let d1 = mediumlarge
            .log(&large, 256, RoundingMode::ToEven, &mut cc)
            .unwrap();
        assert!(d1.cmp(&refn) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn ln_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        let p = 133;
        for _ in 0..10000 {
            let mut nn = BigFloatNumber::random_normal(p, -100, 100).unwrap();
            nn.set_sign(Sign::Pos);
            n.push(nn);
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.ln(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
