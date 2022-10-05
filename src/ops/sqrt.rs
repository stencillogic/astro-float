//! Sqrt computation.

use crate::{
    num::BigFloatNumber, 
    RoundingMode, 
    defs::{Error, EXPONENT_MIN, EXPONENT_MAX},
};
use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::common::consts::TEN;
use crate::common::consts::FIFTEEN;


impl BigFloatNumber {

    /// Compute square root of a number.
    pub fn sqrt(&self, rm: RoundingMode) -> Result<Self, Error> {

        if self.is_negative() {
            return Err(Error::InvalidArgument);
        }

        if self.is_zero() {
            return self.clone();
        }

        let mut p = self.get_mantissa_max_bit_len();
        let mut err = 30;
        while p >= 32 {
            p /= 3;
            err += 6;
        }

        let e = self.get_exponent();
        let mut e_shift = 0;
        if e & 1 == 1 {
            err += 1;
            if e < 0 {
                e_shift = 1;
            }
        }

        let mut x = self.clone()?;
        x.set_precision(x.get_mantissa_max_bit_len() + err, RoundingMode::None)?;

        x.set_exponent(e & 1);
        let mut ret= x.sqrt_iter()?;
        ret = x.mul(&ret, RoundingMode::None)?;
        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        // new exponent
        let mut e_corr = ret.get_exponent() as isize + e as isize / 2 - e_shift as isize;
        if e_corr < EXPONENT_MIN as isize {
            let is_positive = ret.is_positive();
            if !Self::process_subnormal(&mut ret.m, &mut e_corr, rm, is_positive) {
                return Self::new(self.get_mantissa_max_bit_len());
            }
        }

        if e_corr > EXPONENT_MAX as isize {
            return Err(Error::ExponentOverflow(ret.get_sign()));
        }

        ret.set_exponent(ret.get_exponent() + e / 2 - e_shift);

        Ok(ret)
    }

    // Computation iteration.
    fn sqrt_iter(&self) -> Result<Self, Error> {

        let mut prec = self.get_mantissa_max_bit_len();

        if prec <= 64 {

            prec *= 3;
            let mut x = ONE.div(self, RoundingMode::None)?;

            while prec > 0 {
                x = self.sqrt_step(x)?;
                prec /= 3;
            }

            Ok(x)

        } else {

            let mut x = self.clone()?;

            x.set_precision((prec + 2) / 3, RoundingMode::None)?;

            let xn= x.sqrt_iter()?;

            self.sqrt_step(xn)
        }
    }

    fn sqrt_step(&self, mut xn: Self) -> Result<Self, Error> {
        // y(n) = self*x(n)
        // x(n+1) = x(n)*2^(-3)*(15 - y(n)*(10 - 3*y(n)))
        
        let yn = self.mul(&xn, RoundingMode::None)?;
        let yn = yn.mul(&xn, RoundingMode::None)?;
        let n1 = THREE.mul(&yn, RoundingMode::None)?;
        let n2 = TEN.sub(&n1, RoundingMode::None)?;
        let n3 = yn.mul(&n2, RoundingMode::None)?;
        let n4 = FIFTEEN.sub(&n3, RoundingMode::None)?;

        xn.set_exponent(xn.get_exponent() - 3);
        xn.mul(&n4, RoundingMode::None)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{Exponent, Sign};

    #[test]
    fn test_sqrt() {
/* 
         let n1 = BigFloatNumber::from_raw_parts(
            &[1616073276, 160212377, 2290662135],
            96, Sign::Pos, -70).unwrap();
        let n2 = n1.sqrt(RoundingMode::ToEven).unwrap();
        println!("{:?}", n2.mul(&n2, RoundingMode::ToEven).unwrap());
        return;  */

        let mut eps = ONE.clone().unwrap();
        let prec = 3200;

        for _ in 0..1000 {

            let mut d1 = BigFloatNumber::random_normal(prec, -80, 80).unwrap();
            if d1.is_negative() {
                d1.inv_sign();
            }

            let d2 = d1.sqrt(RoundingMode::ToEven).unwrap();
            let d3 = d2.mul(&d2, RoundingMode::ToEven).unwrap();

            eps.set_exponent(d1.get_exponent() - prec as Exponent + 2);
            //println!("d1 {:?}\nd3 {:?}", d1, d3);
            assert!(d1.sub(&d3, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);
        }
    }


    #[ignore]
    #[test]
    fn sqrt_perf() {

        let mut n = vec![];
        for _ in 0..100000 {
            let mut n0 = BigFloatNumber::random_normal(132, -0, 0).unwrap();
            n0.set_sign(Sign::Pos);
            n.push(n0);
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let f = ni.sqrt(RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}