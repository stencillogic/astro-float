//! Sqrt computation.

use crate::{
    num::BigFloatNumber, 
    RoundingMode, 
    defs::{Error, EXPONENT_MIN, EXPONENT_MAX},
};


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
        while p >= 128 {
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

        let three = Self::three(1)?;
        let ten = Self::ten(1)?;
        let fifteen = Self::fifteen(1)?;

        let mut x = self.clone()?;
        x.set_precision(x.get_mantissa_max_bit_len() + err, RoundingMode::None)?;

        x.set_exponent(e & 1);
        let mut ret= x.sqrt_iter(&three, &ten, &fifteen)?;
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
    fn sqrt_iter(&self, three: &Self, ten: &Self, fifteen: &Self) -> Result<Self, Error> {
        let mut prec = self.get_mantissa_max_bit_len();
        let mut x = self.clone()?;
        if prec <= 128 {
            prec *= 3;
            x = Self::one(1)?.div(&x, RoundingMode::None)?;
            while prec > 0 {
                x = self.sqrt_step(x, three, ten, fifteen)?;
                prec /= 3;
            }
            Ok(x)
        } else {
            x.set_precision((prec + 2) / 3, RoundingMode::None)?;
            let mut xn= x.sqrt_iter(three, ten, fifteen)?;
            xn.set_precision(prec, RoundingMode::None)?;
            self.sqrt_step(xn, three, ten, fifteen)
        }
    }

    fn sqrt_step(&self, mut xn: Self, three: &Self, ten: &Self, fifteen: &Self) -> Result<Self, Error> {
        // y(n) = self*x(n)
        // x(n+1) = x(n)*2^(-3)*(15 - y(n)*(10 - 3*y(n)))
        let xx = xn.mul(&xn, RoundingMode::None)?;
        let yn = self.mul(&xx, RoundingMode::None)?;
        let n1 = three.mul(&yn, RoundingMode::None)?;
        let n2 = ten.sub(&n1, RoundingMode::None)?;
        let n3 = yn.mul(&n2, RoundingMode::None)?;
        let n4 = fifteen.sub(&n3, RoundingMode::None)?;
        xn.set_exponent(xn.get_exponent() - 3);
        xn.mul(&n4, RoundingMode::None)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::Exponent;

    #[test]
    fn test_sqrt() {
/* 
         let n1 = BigFloatNumber::from_raw_parts(
            &[1616073276, 160212377, 2290662135],
            96, Sign::Pos, -70).unwrap();
        let n2 = n1.sqrt(RoundingMode::ToEven).unwrap();
        println!("{:?}", n2.mul(&n2, RoundingMode::ToEven).unwrap());
        return;  */

        let one = BigFloatNumber::one(1).unwrap();
        let mut eps = one.clone().unwrap();
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
}