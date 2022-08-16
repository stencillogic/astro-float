//! High-level operations on the numbers.

use crate::num::BigFloatNumber;
use crate::defs::RoundingMode;
use crate::defs::Error;
use crate::ops::series::PolycoeffGen;
use crate::ops::series::series_horner;
use crate::ops::series::series_rect;
use crate::ops::series::series_niter;


// Polynomial coefficient generator.
struct SinhPolycoeffGen {
    one: BigFloatNumber,
    one_full_p: BigFloatNumber,
    inc: BigFloatNumber,
    fct: BigFloatNumber,
}

impl SinhPolycoeffGen {

    fn new(p: usize) -> Result<Self, Error> {
        let one = BigFloatNumber::from_digit(1, 1)?;
        let inc = BigFloatNumber::from_digit(1, 1)?;
        let fct = BigFloatNumber::from_digit(1, p)?;
        let one_full_p = BigFloatNumber::from_digit(1, p)?;
        Ok(SinhPolycoeffGen {
            one,
            one_full_p,
            inc,
            fct,
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
}

impl BigFloatNumber {

    /// Computes hyperbolic sine.
    pub fn sinh(&self, rm: RoundingMode) -> Result<Self, Error> {
        // sinh(3*x) = 3*sinh(x) + 4*sinh(x)^3
        Err(Error::InvalidArgument)
    }

    /// sinh using series, for |x| < 1
    pub(super) fn sinh_series(&self, rm: RoundingMode) -> Result<Self, Error> {

        let reduction_times = 10;

        let arg_holder;
        let arg = if reduction_times > 0 {
            arg_holder = self.arg_reduce(reduction_times, rm)?;
            &arg_holder
        } else {
            self
        };

        // x + x^3/3! + x^5/5! + x^7/7! + ...
        let polycoeff_gen = SinhPolycoeffGen::new(arg.get_mantissa_max_bit_len())?;
        let acc = arg.clone()?;    // x
        let x_step = arg.mul(arg, rm)?;   // x^2
        let x_first = arg.mul(&x_step, rm)?;   // x^3
        let niter = series_niter(arg.get_mantissa_max_bit_len(), (-arg.e) as usize) / 2;
        let ret = if niter >= 16 {
            series_rect(niter, acc, x_first, x_step, polycoeff_gen, rm)
        } else {
            series_horner(acc, x_first, x_step, polycoeff_gen, rm)
        }?;

        if reduction_times > 0 {
            ret.arg_restore(reduction_times, rm)
        } else {
            Ok(ret)
        }
    }

    // reduce argument n times.
    // cost: n * O(add)
    fn arg_reduce(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sinh(3*x) = 3*sinh(x) + 4*sinh(x)^3
        let mut ret = self.clone()?;
        let three = Self::from_digit(3, 1)?;
        for _ in 0..n {
            ret = ret.div(&three, rm)?;
        }
        Ok(ret)
    }

    // restore value for the argument reduced n times.
    // cost: n * (4*O(mul) + O(add))
    fn arg_restore(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        // sinh(3*x) = 3*sinh(x) + 4*sinh(x)^3
        let mut sinh = self.clone()?;
        let three = Self::from_digit(3, 1)?;
        let four = Self::from_digit(4, 1)?;
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
    fn test_trigh() {
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_digit(1,320).unwrap();
        n1.set_exponent(0);
        let n2 = n1.sinh_series(rm).unwrap();
        println!("{:?}", n2.fp3(crate::Radix::Dec, rm).unwrap());
    }

    //#[ignore]
    #[test]
    fn trigh_perf() {
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(320*2, -0, -0).unwrap());
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