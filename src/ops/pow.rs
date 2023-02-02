//! Exponentiation.

use crate::common::consts::{FOUR, THREE};
use crate::common::util::{get_add_cost, get_mul_cost, round_p};
use crate::ops::consts::Consts;
use crate::ops::util::compute_small_exp;
use crate::{
    common::consts::ONE,
    defs::{Error, WORD_BIT_SIZE, WORD_SIGNIFICANT_BIT},
    num::BigFloatNumber,
    RoundingMode, Sign,
};

use super::series::{series_cost_optimize, series_run, ArgReductionEstimator, PolycoeffGen};

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

        let iter_cost =
            (get_mul_cost(p) + get_add_cost(p) + get_add_cost(inc.get_mantissa_max_bit_len())) * 2;

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
    /// Computes `e` to the power of `self` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn exp(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            return Self::from_word(1, p);
        }

        compute_small_exp!(ONE, self.get_exponent() as isize, self.is_negative(), p, rm);

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        loop {
            let mut ret = if self.is_negative() {
                let p_x = p_wrk + 1;
                let x = match self.exp_positive_arg(p_x, cc) {
                    Ok(v) => Ok(v),
                    Err(e) => match e {
                        Error::ExponentOverflow(_) => {
                            return Self::new(p);
                        }
                        Error::DivisionByZero => Err(Error::DivisionByZero),
                        Error::InvalidArgument => Err(Error::InvalidArgument),
                        Error::MemoryAllocation(a) => Err(Error::MemoryAllocation(a)),
                    },
                }?;

                ONE.div(&x, p_wrk, RoundingMode::FromZero)
            } else {
                self.exp_positive_arg(p_wrk, cc)
            }?;

            if ret.try_set_precision(p, rm, p_wrk)? {
                return Ok(ret);
            }

            p_wrk += p_inc;
            p_inc *= 2;
        }
    }

    // exp for positive argument
    fn exp_positive_arg(&self, p: usize, cc: &mut Consts) -> Result<Self, Error> {
        debug_assert!(!self.is_zero());

        if self.e as isize > WORD_BIT_SIZE as isize {
            return Err(Error::ExponentOverflow(self.get_sign()));
        }

        let p_work = p + 4;

        // compute separately for int and fract parts, then combine the results.
        let int = self.get_int_as_usize().map_err(|e| {
            if matches!(e, Error::InvalidArgument) {
                Error::ExponentOverflow(Sign::Pos)
            } else {
                e
            }
        })?;
        let e_int = if int > 0 {
            let e_const = cc.e_num(p_work, RoundingMode::None)?;

            e_const.powi(int, p_work, RoundingMode::None)
        } else {
            ONE.clone()
        }?;

        let mut fract = self.fract()?;
        let e_fract = if !fract.is_zero() {
            fract.set_precision(p_work, RoundingMode::None)?;
            fract.set_sign(Sign::Pos);
            fract.expf(RoundingMode::None)
        } else {
            ONE.clone()
        }?;

        e_int.mul(&e_fract, p, RoundingMode::FromZero)
    }

    /// Compute the power of `self` to the integer `n` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn powi(&self, n: usize, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        let mut inexact = false;
        self.powi_internal(n, p, rm, &mut inexact)
    }

    /// Compute the power of `self` to the signed integer `n` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    ///  - DivisionByZero: `self` is zero and `n` is negative.
    pub fn powsi(&self, n: isize, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        if n >= 0 {
            return self.powi(n as usize, p, rm);
        } else {
            let p = round_p(p);

            if self.is_zero() {
                return Err(Error::DivisionByZero);
            }

            if n == -1 {
                return ONE.div(&self, p, rm);
            }

            let mut p_inc = WORD_BIT_SIZE;
            let mut p_wrk = p + p_inc;

            loop {
                let p_x = p_wrk + 1;

                let mut inexact = false;
                let x =
                    self.powi_internal(n.unsigned_abs(), p_x, RoundingMode::None, &mut inexact)?;

                if inexact {
                    let mut ret = ONE.div(&x, p_x, RoundingMode::None)?;
                    if ret.try_set_precision(p, rm, p_wrk)? {
                        return Ok(ret);
                    }
                } else {
                    return ONE.div(&x, p, rm);
                }

                p_wrk += p_inc;
                p_inc *= 2;
            }
        }
    }

    /// Compute self^n, set inexact to true if the result is inexact.
    fn powi_internal(
        &self,
        n: usize,
        p: usize,
        rm: RoundingMode,
        inexact: &mut bool,
    ) -> Result<Self, Error> {
        let p = round_p(p);

        let mut i = n;

        if i == 0 {
            return Self::from_word(1, p);
        }

        if self.is_zero() || i == 1 {
            let mut ret = self.clone()?;
            ret.set_precision(p, rm)?;
            return Ok(ret);
        }

        let mut bit_pos = WORD_BIT_SIZE;
        while bit_pos > 0 {
            bit_pos -= 1;
            i <<= 1;
            if i & WORD_SIGNIFICANT_BIT as usize != 0 {
                bit_pos -= 1;
                i <<= 1;
                break;
            }
        }
        let bit_pos = bit_pos; // make immutable

        let p = round_p(p);

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        loop {
            let p_x = p_wrk + bit_pos * 2;

            let mut ret = || -> Result<Self, Error> {
                let mut x = self.clone()?;

                x.set_precision_inexact(p_x, RoundingMode::FromZero, inexact)?;

                // TODO: consider windowing and precomputed values.
                let mut bp = bit_pos;
                let mut j = i;
                while bp > 0 {
                    bp -= 1;

                    x = x.mul_inexact(&x, p_x, RoundingMode::FromZero, inexact)?;

                    if j & WORD_SIGNIFICANT_BIT as usize != 0 {
                        x = x.mul_inexact(self, p_x, RoundingMode::FromZero, inexact)?;
                    }

                    j <<= 1;
                }

                Ok(x)
            }()
            .map_err(|e| -> Error {
                if let Error::ExponentOverflow(_) = e {
                    Error::ExponentOverflow(if self.is_negative() && (n & 1 == 1) {
                        Sign::Neg
                    } else {
                        Sign::Pos
                    })
                } else {
                    e
                }
            })?;

            if *inexact {
                if ret.try_set_precision(p, rm, p_wrk)? {
                    return Ok(ret);
                }
            } else {
                ret.set_precision(p, rm)?;
                return Ok(ret);
            }

            p_wrk += p_inc;
            p_inc *= 2;
        }
    }

    // e^self for |self| < 1.
    fn expf(self, rm: RoundingMode) -> Result<Self, Error> {
        debug_assert!(!self.is_zero());

        let p = self.get_mantissa_max_bit_len();

        let sh = self.sinh_series(p, rm)?; // faster convergence than direct series

        // e = sh + sqrt(sh^2 + 1)
        let sq = sh.mul(&sh, p, rm)?;
        let sq2 = sq.add(&ONE, p, rm)?;
        let sq3 = sq2.sqrt(p, rm)?;
        sq3.add(&sh, p, RoundingMode::FromZero)
    }

    /// sinh using series, for |x| < 1
    pub fn sinh_series(mut self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sinh:  x + x^3/3! + x^5/5! + x^7/7! + ...

        let mut polycoeff_gen = SinhPolycoeffGen::new(p)?;
        let (reduction_times, niter) = series_cost_optimize::<SinhArgReductionEstimator>(
            p,
            &polycoeff_gen,
            -(self.e as isize),
            2,
            false,
        );

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

        let ret = series_run(acc, x_first, x_step, niter, &mut polycoeff_gen)?;

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

    /// Compute the power of `self` to the `n` with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: `self` is negative, and `n` is not an integer number; the precision is incorrect.
    pub fn pow(
        &self,
        n: &Self,
        p: usize,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<Self, Error> {
        if n.is_zero() {
            return Self::from_word(1, p);
        } else if self.is_zero() {
            return if n.is_negative() {
                if n.is_odd_int() {
                    Err(Error::ExponentOverflow(self.get_sign()))
                } else {
                    Err(Error::ExponentOverflow(Sign::Pos))
                }
            } else {
                let mut ret = Self::new(p)?;
                if n.is_odd_int() {
                    ret.set_sign(self.get_sign());
                }
                Ok(ret)
            };
        } else if self.get_exponent() == 1 && self.abs_cmp(&ONE) == 0 {
            return if n.is_odd_int() {
                Self::from_i8(self.get_sign().as_int(), p)
            } else {
                if self.is_positive() || n.is_int() {
                    Self::from_word(1, p)
                } else {
                    return Err(Error::InvalidArgument);
                }
            };
        } else if self.is_negative() {
            if n.is_int() {
                let int = n.get_int_as_usize().map_err(|e| {
                    if matches!(e, Error::InvalidArgument) {
                        let sign = if n.is_odd_int() { Sign::Neg } else { Sign::Pos };
                        Error::ExponentOverflow(sign)
                    } else {
                        e
                    }
                })?;

                let int = int as isize * n.get_sign().as_int() as isize;

                return self.powsi(int, p, rm);
            } else {
                return Err(Error::InvalidArgument);
            }
        } else if n.get_exponent() == 1 && n.abs_cmp(&ONE) == 0 {
            if n.is_positive() {
                let mut ret = self.clone()?;
                ret.set_precision(p, rm)?;
                return Ok(ret);
            } else {
                return ONE.div(&self, p, rm);
            }
        }

        // actual pow : self^n = e^(n * ln(self))

        let p = round_p(p);

        let mut x = self.clone()?;

        let p_ext = p + 2;
        x.set_precision(p_ext, RoundingMode::None)?;

        let ln = x.ln(p_ext, RoundingMode::None, cc)?;

        let m = match n.mul(&ln, p_ext, RoundingMode::None) {
            Ok(v) => Ok(v),
            Err(e) => match e {
                Error::ExponentOverflow(Sign::Neg) => {
                    return Self::new(p);
                }
                Error::ExponentOverflow(Sign::Pos) => Err(Error::ExponentOverflow(Sign::Pos)),
                Error::DivisionByZero => Err(Error::DivisionByZero),
                Error::InvalidArgument => Err(Error::InvalidArgument),
                Error::MemoryAllocation(a) => Err(Error::MemoryAllocation(a)),
            },
        }?;

        m.exp(p, rm, cc)
    }
}

#[cfg(test)]
mod test {

    use crate::common::{consts::TWO, util::random_subnormal};

    use super::*;

    #[test]
    fn test_power() {
        let mut cc = Consts::new().unwrap();

        // near 1
        let p = 320;
        let d1 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC4872DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.exp(p, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse(
            "2.B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A5496AF9D95160A40F47A2ECF1C6AEA0",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        let d1 = BigFloatNumber::parse(
            "1.00000000000000000000000000000000000000000000000000000000000000002DC85F7E77EC487C",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.exp(p, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = BigFloatNumber::parse(
            "2.B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEFAEC1BE22DDEADB48",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        // random subnormal
        let d1 = random_subnormal(p);
        assert!(d1.exp(p, RoundingMode::ToEven, &mut cc).unwrap().cmp(&ONE) == 0);

        // pow(small, small)
        let p = 256;
        let mut d1 = BigFloatNumber::parse("1.10010100010011110010001011101010010101111000010101010100010010111001000100011101010111011010110011011111110000010010101000110001001000000101000010101111001100110111100011101000110001001000000101000010101111001100110111100011101010011101101", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d1.set_exponent(-123456);
        let mut d2 = BigFloatNumber::parse("1.00110001001000010100001010111100110011011110001110101001110110100000101000010010101111000010110010100010011110010001011101010101010001001011100110111111100100010001110101011101101011000001001010100101111001100110111100011101000110001001000", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d2.set_exponent(-123);
        let d3 = d1.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap();
        let d4 = BigFloatNumber::parse("1.111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111100111000110010011110111100111111100111010011001110010010110010100100110010110111110110100011010000110110011010111101110000011100011010100110100000001e-1", crate::Radix::Bin, p, RoundingMode::None).unwrap();

        assert!(d4.cmp(&d3) == 0);

        // pow(large, small)
        let mut d1 = BigFloatNumber::parse("1.10010100010011110010001011101010010101111000010101010100010010111001000100011101010111011010110011011111110000010010101000110001001000000101000010101111001100110111100011101000110001001000000101000010101111001100110111100011101010011101101", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d1.set_exponent(123456);
        let mut d2 = BigFloatNumber::parse("1.00110001001000010100001010111100110011011110001110101001110110100000101000010010101111000010110010100010011110010001011101010101010001001011100110111111100100010001110101011101101011000001001010100101111001100110111100011101000110001001000", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d2.set_exponent(-123);
        let d3 = d1.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap();
        let d4 = BigFloatNumber::parse("1.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110001110011010111001000101100100101011011111001101101011011010100101111001001000010000010100110110011000001011011111000000000010111010000010110111", crate::Radix::Bin, p, RoundingMode::None).unwrap();

        assert!(d4.cmp(&d3) == 0);

        // pow(>~1, large)
        let d1 = BigFloatNumber::parse("1.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110001110011010111001000101100100101011011111001101101011011010100101111001001000010000010100110110011000001011011111000000000010111010000010110111", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        let mut d2 = BigFloatNumber::parse("1.00110001001000010100001010111100110011011110001110101001110110100000101000010010101111000010110010100010011110010001011101010101010001001011100110111111100100010001110101011101101011000001001010100101111001100110111100011101000110001001000", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d2.set_exponent(123);
        let d3 = d1.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap();
        let d4 = BigFloatNumber::parse("1.000011101011111010010100111000101101011001100110110100101011001110100110011011100100100101011100010100011101011111010011100011010000110001100111001011000001111110001110000110000000101101011001010001000011011001000010001110000100110000110011111100000001e+1010101101000111", crate::Radix::Bin, p, RoundingMode::None).unwrap();

        assert!(d4.cmp(&d3) == 0);

        // pow(<~1, large)
        let d1 = BigFloatNumber::parse("0.1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110001110011010111001000101100100101011011111001101101011011010100101111001001000010000010100110110011000001011011111000000000010111010000010110111", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        let mut d2 = BigFloatNumber::parse("1.00110001001000010100001010111100110011011110001110101001110110100000101000010010101111000010110010100010011110010001011101010101010001001011100110111111100100010001110101011101101011000001001010100101111001100110111100011101000110001001000", crate::Radix::Bin, p, RoundingMode::None).unwrap();
        d2.set_exponent(123);
        let d3 = d1.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap();
        let d4 = BigFloatNumber::parse("1.010011011001100100100000101011101001110011001100011001011011010010101111101100111101011010101101101111100111001001001101000111110001010010111101110010011100001011011111001111001001001100100111010100100010010111011011110010110101110000100111001100100000011e-110000110100111100", crate::Radix::Bin, p, RoundingMode::None).unwrap();

        // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{:?}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        assert!(d4.cmp(&d3) == 0);

        // max, min, subnormal
        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();
        let d3 = BigFloatNumber::min_positive(p).unwrap();

        assert!(
            d1.exp(p, RoundingMode::ToEven, &mut cc).unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        assert!(
            d1.pow(&d1, p, RoundingMode::ToEven, &mut cc).unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        assert!(d1
            .pow(&d2, p, RoundingMode::ToEven, &mut cc)
            .unwrap()
            .is_zero());
        assert!(
            d1.pow(&d3, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );

        assert!(d2.exp(p, RoundingMode::ToEven, &mut cc).unwrap().is_zero());

        assert!(d3.exp(p, RoundingMode::ToEven, &mut cc).unwrap().cmp(&ONE) == 0);

        assert!(d3
            .pow(&d1, p, RoundingMode::ToEven, &mut cc)
            .unwrap()
            .is_zero());
        assert!(
            d3.pow(&d2, p, RoundingMode::ToEven, &mut cc).unwrap_err()
                == Error::ExponentOverflow(Sign::Pos)
        );
        assert!(
            d3.pow(&d3, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );

        assert!(
            d1.pow(&ONE, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&d1)
                == 0
        );
        assert!(
            d3.pow(&ONE, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&d3)
                == 0
        );
        assert!(
            ONE.pow(&d1, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );
        assert!(
            ONE.pow(&d2, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );
        assert!(
            ONE.pow(&d3, p, RoundingMode::ToEven, &mut cc)
                .unwrap()
                .cmp(&ONE)
                == 0
        );

        let rm = RoundingMode::ToOdd;
        let d1 = TWO.pow(&ONE.neg().unwrap(), p, rm, &mut cc).unwrap();
        let d2 = ONE.div(&TWO, p, rm).unwrap();

        assert!(d1.cmp(&d2) == 0);
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
