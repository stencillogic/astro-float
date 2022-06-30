use crate::defs::DECIMAL_SIGN_NEG;
/// Power.

use crate::inc::inc::BigFloatInc;
use crate::inc::ops::tables::exp_const::EXP_VALUES;
use crate::defs::Error;
use crate::inc::inc::DECIMAL_PARTS;
use crate::defs::DECIMAL_BASE_LOG10;
use crate::defs::DECIMAL_BASE;
use crate::inc::inc::E;


impl BigFloatInc {


    /// Return BigFloatInc to the power of `d1`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    ///
    /// ArgumentIsNegative - when `d1` has fractional part and `self` is negative.
    pub fn pow(&self, d1: &Self) -> Result<Self, Error> {
        if self.n == 0 {
            return Ok(*self);
        }
        if Self::extract_fract_part(d1).n == 0 {
            let int = Self::extract_int_part(d1);
            self.powi(&int)
        } else {
            // self^d1 = e^(d1*ln(self))
            // e^(d1*ln(self)) = e^int * e^fract
            // e^int = e.powi(int)
            // e^fract = fract.exp()
            let b = if self.sign == DECIMAL_SIGN_NEG {
                self.inv_sign()
            } else {
                *self
            };
            let mut x = d1.mul(&b.ln()?)?;
            if d1.sign == DECIMAL_SIGN_NEG {
                x = x.inv_sign();
            }
            let one = BigFloatInc::one();
            let int = Self::extract_int_part(&x);
            let frac = Self::extract_fract_part(&x);
            let p1 = if int.n != 0 {
                E.powi(&int)?
            } else {
                one
            };
            let p2 = if frac.n != 0 {
                BigFloatInc::expf(&frac)?
            } else {
                one
            };
            let mut ret = if d1.sign == DECIMAL_SIGN_NEG {
                one.div(&p1.mul(&p2)?)
            } else {
                p1.mul(&p2)
            }?;
            ret.sign = self.sign;
            Ok(ret)
        }
    }

    // self^d1, for integer d1
    fn powi(&self, d1: &Self) -> Result<Self, Error> {
        let mut int = *d1;
        let mut ret = Self::one();
        let mut ml = *self;
        while int.n > 0 {
            if int.m[0] & 1 != 0 {
                ret = ret.mul(&ml)?;
            }
            ml = ml.mul(&ml)?;
            Self::divide_by_two_int(&mut int);
        }
        Ok(ret)
    }

    // e^d1, where d1 is fractional < 1
    fn expf(d1: &Self) -> Result<Self, Error> {
        // if d1 >= 0.001, factoring: d1 = p1 + p2, p2 < 0.001
        // e^p1 - precomputed
        // e^p2 = 1 + p2 + p2^2/2! + p2^3/3! + ...
        let one = Self::one();
        if d1.n == 0 {
            return Ok(one);
        }
        let mut p2 = *d1;
        p2.maximize_mantissa();
        let mut idx = p2.m[DECIMAL_PARTS - 1];
        let mut e = -(p2.e as i32);
        let e_p1;
        if e < 48 {
            let mut t = 1;
            while e >= 44 {
                t *= 10;
                e -= 1;
            }
            idx /= t;
            p2.m[DECIMAL_PARTS - 1] %= t;
            p2.n = Self::num_digits(&p2.m);
            e_p1 = EXP_VALUES[idx as usize];
        } else {
            e_p1 = one;
        }
        let mut ret = one.add(&p2)?;
        let mut ml = p2;
        let mut n = one;
        let mut d = n;
        loop {
            ml = ml.mul(&p2)?;
            n = n.add(&one)?;
            d = d.mul(&n)?;
            let val = ret.add(&ml.div(&d)?)?;
            if val.cmp(&ret) == 0 {
                break;
            }
            ret = val;
        }
        ret.mul(&e_p1)
    }

    // divide BigFloat by two as integer
    fn divide_by_two_int(d1: &mut Self) {
        if d1.m[0] & 1 == 1 && d1.e > 0 {
            d1.maximize_mantissa();
        }
        d1.m[0] >>= 1;
        for i in 1..(d1.n as usize + DECIMAL_BASE_LOG10 - 1) / DECIMAL_BASE_LOG10 {
            if d1.m[i] & 1 != 0 {
                d1.m[i - 1] += DECIMAL_BASE as i16 / 2;
            }
            d1.m[i] >>= 1;
        }
        d1.n = Self::num_digits(&d1.m);
    }
}
