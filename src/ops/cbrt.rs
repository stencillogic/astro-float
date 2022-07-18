//! Cube root.

use crate::defs::BigFloatNum;
use crate::defs::Error;


impl BigFloatNum {

    /// Return cube root of a number.
    pub fn cbrt(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.cbrt()?;
        Self::from_big_float_inc(ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::{DECIMAL_POSITIONS, DECIMAL_SIGN_NEG, DECIMAL_SIGN_POS, DECIMAL_MIN_EXPONENT};

    #[test]
    fn test_cbrt() {

        let mut d1 ;
        
        let one = BigFloatNum::one();
        let mut epsilon = BigFloatNum::one();
        epsilon.e = - epsilon.n as i8 + 2 - (DECIMAL_POSITIONS as i8);

/*
        for i in 0..11 {
            for j in 1..100 {
                let mut d = crate::inc::inc::BigFloatInc::new();
                d.m[i] = j*100;
                d.n = crate::inc::inc::BigFloatInc::num_digits(&d.m);
                let ret = d.cbrt().unwrap();
            }
        }
*/
        // 0
        d1 = BigFloatNum::new();
        assert!(d1.cbrt().unwrap().n == 0);

        // |d1| = 1
        d1 = BigFloatNum::one();
        let d2 = d1;
        let ret = d1.cbrt().unwrap();
        assert!(ret.sub(&d2).unwrap().abs().cmp(&epsilon) <= 0);

        d1.sign = DECIMAL_SIGN_NEG;
        let d2 = d1;
        let ret = d1.cbrt().unwrap();
        assert!(ret.sub(&d2).unwrap().abs().cmp(&epsilon) <= 0);

        // |d1| < 1
        d1 = BigFloatNum::one();
        d1.m[0] = 456;
        d1.m[8] = 123;
        d1.e -= 1;
        let d2 = d1;
        let ret = d1.cbrt().unwrap();
        let ret = ret.mul(&ret).unwrap().mul(&ret).unwrap();
        assert!(ret.div(&d2).unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);

        d1.sign = DECIMAL_SIGN_NEG;
        let d2 = d1;
        let ret = d1.cbrt().unwrap();
        let ret = ret.mul(&ret).unwrap().mul(&ret).unwrap();
        assert!(ret.div(&d2).unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);

        // |d1| > 1
        d1.e += 2;
        d1.sign = DECIMAL_SIGN_POS;
        let d2 = d1;
        let ret = d1.cbrt().unwrap();
        let ret = ret.mul(&ret).unwrap().mul(&ret).unwrap();
        assert!(ret.div(&d2).unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);
        
        d1.sign = DECIMAL_SIGN_NEG;
        let d2 = d1;
        let ret = d1.cbrt().unwrap();
        let ret = ret.mul(&ret).unwrap().mul(&ret).unwrap();
        assert!(ret.div(&d2).unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);

        // subnormal
        d1 = BigFloatNum::new();
        d1.m[0] = 456;
        d1.m[1] = 123;
        d1.n = 7;
        d1.e = DECIMAL_MIN_EXPONENT;
        let d2 = d1;
        let ret = d1.cbrt().unwrap();
        let ret = ret.mul(&ret).unwrap().mul(&ret).unwrap();
        assert!(ret.sub(&d2).unwrap().abs().get_mantissa_len() < 2);

        // range of numbers
        let mut ret;
        let mut d1 = BigFloatNum::new();
        d1.m[0] = 4560;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 651;
        d1.m[5] = 41;
        d1.m[6] = 671;
        d1.m[7] = 100;
        d1.m[8] = 0;
        d1.m[9] = 0;
        d1.n = 32;
        d1.e = -38;
        epsilon.e = - epsilon.n as i8 + 3 - (DECIMAL_POSITIONS as i8);
        for i in 1..8000 {
            d1.m[8] = 10+i;
            d1.m[9] = i;
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 36;
            ret = d1.cbrt().unwrap();
            ret = ret.mul(&ret).unwrap().mul(&ret).unwrap();
            assert!(ret.div(&d1).unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);
        }
    }
}
