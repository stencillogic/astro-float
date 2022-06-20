/// Logarithms.

use crate::defs::BigFloat;
use crate::defs::Error;
use crate::defs::DECIMAL_POSITIONS;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::DECIMAL_MIN_EXPONENT;
use crate::defs::DECIMAL_MAX_EXPONENT;
use crate::increased::BigFloatInc;
use crate::ops::tables::atan_const::ATAN_VALUES1;
use crate::ops::tables::ln_const::LN_VALUES;

const LN_OF_10: BigFloatInc = BigFloatInc {
    m: [1015, 7601, 6420, 6843, 1454, 1799, 6840, 4045, 9299, 5850, 2302] , 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

impl BigFloat {

    /// Returns natural logarithm of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    ///
    /// InvalidArgument - when `self` is negative or zero.
    pub fn ln(&self) -> Result<BigFloat, Error> {
        if self.sign == DECIMAL_SIGN_NEG || self.n == 0 {
            return Err(Error::InvalidArgument);
        }

        // factoring: ln(d) = ln(d.m ^ (1 - d.n)) + (d.e - 1 + d.n) * ln(10)
        let mut add = BigFloatInc::new();
        let mut s = self.e as i16 - 1 + self.n;
        if s != 0 {
            // check if s fits in single "digit"
            assert!(DECIMAL_MAX_EXPONENT as i16 + 1 + (DECIMAL_POSITIONS as i16) < DECIMAL_BASE as i16 && 
               DECIMAL_POSITIONS as i16 + 1 - (DECIMAL_MIN_EXPONENT as i16) < DECIMAL_BASE as i16);
            if s > 0 {
                add.m[0] = s;
            } else {
                add.m[0] = -s;
                add.sign = DECIMAL_SIGN_NEG;
            }
            while s != 0 {
                add.n += 1;
                s /= 10;
            }
            add = add.mul(&LN_OF_10)?;
        }

        let one = BigFloatInc::one();
        let two = BigFloatInc::two();
        let mut ml = Self::to_big_float_inc(self);
        ml.e = 1 - ml.n as i8;

        // arctanh series
        ml = ml.sub(&one)?.div(&ml.add(&one)?)?;    // (x-1)/(x+1)
        
        // further reduction: arctanh(x) = arctanh(s) + arctanh((x - s) / (1 - x*s))
        let (idx, mut dx) = Self::get_trig_params(&mut ml, 0);
        let atanh_s = LN_VALUES[idx];
        let s = ml.sub(&dx)?;
        dx = dx.div(&one.sub(&ml.mul(&s)?)?)?;

        let mut ret = dx;
        let dxx = dx.mul(&dx)?;
        for i in 0..ATAN_VALUES1.len() {
            dx = dx.mul(&dxx)?;
            let mut poly_coeff = ATAN_VALUES1[i];
            poly_coeff.sign = DECIMAL_SIGN_POS;     // same as for atan, but always positive
            let p = poly_coeff.mul(&dx)?;
            let val = ret.add(&p)?;
            if val.cmp(&ret) == 0 {
                break;
            }
            ret = val;
            assert!(i != ATAN_VALUES1.len()-2);
        }
        ret = ret.add(&atanh_s)?.mul(&two)?.add(&add)?;

        Self::from_big_float_inc(&mut ret)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::E;

    #[test]
    fn test_log() {

        let mut d1;
        let mut d2;
        let one = BigFloat::one();
        let mut epsilon = BigFloat::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);

        // arg = 0
        d1 = BigFloat::new();
        assert!(d1.ln().unwrap_err() == Error::InvalidArgument);

        // arg < 0
        d1 = BigFloat::one();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.ln().unwrap_err() == Error::InvalidArgument);

        // ln of E = 1
        epsilon.e = -77;    // 1*10^(-39)
        assert!(E.ln().unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);

        d2 = BigFloat::new();
        d2.m[0] = 4567;
        d2.m[1] = 123;
        d2.m[2] = 6789;
        d2.m[3] = 2345;
        d2.m[4] = 651;
        d2.m[5] = 41;
        d2.m[6] = 671;
        d2.m[7] = 100;
        d2.m[8] = 10;
        d2.m[9] = 9999;
        d2.n = DECIMAL_POSITIONS as i16;
        d2.e = -10;
        for i in 0..100 {
            d2.m[2] = i;
            d2.m[5] = i;
            d2.e = -50 + (i%100) as i8;
            epsilon.e = d2.e - 36;  // 1*10^(1 + d2.e)
            let ret = d2.ln().unwrap();
            d1 = E.pow(&ret).unwrap();
            assert!(d2.sub(&d1).unwrap().abs().cmp(&epsilon) <= 0);
        }
    }
}
