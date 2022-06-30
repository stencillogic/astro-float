/// Power.

use crate::defs::BigFloatNum;
use crate::defs::Error;


impl BigFloatNum {

    /// Return BigFloat to the power of `d1`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    ///
    /// ArgumentIsNegative - when `d1` has fractional part and `self` is negative.
    pub fn pow(&self, d1: &Self) -> Result<Self, Error> {
        let a = Self::to_big_float_inc(self);
        let n = Self::to_big_float_inc(d1);
        let mut ret = a.pow(&n)?;
        Self::from_big_float_inc(&mut ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::DECIMAL_SIGN_POS;
    use crate::defs::DECIMAL_POSITIONS;
    use crate::defs::DECIMAL_SIGN_NEG;

    #[test]
    fn test_pow() {

        let mut d1;
        let mut d2;
        let mut ref_num;
        let one = BigFloatNum::one();
        let mut epsilon = BigFloatNum::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);


        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        d2.m[0] = 2;
        d2.n = 1;
        d1.m[0] = 2345;
        d1.m[1] = 8901;
        d1.m[2] = 4567;
        d1.m[3] = 123;
        d1.n = 15;
        d1.e = -12;
        d2.pow(&d1).unwrap();


        // zero number
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();
        d1.m[0] = 123;
        d1.n = 3;
        d1.e = -1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // zero argument
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();
        ref_num.m[0] = 1;
        ref_num.n = 1;
        d2.m[0] = 400;
        d2.n = 3;
        d2.e = -1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // argument is too large
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        d2.m[0] = 2;
        d2.n = 1;
        d1.m[0] = 400;
        d1.n = 3;
        d1.e = 1;
        assert!(d2.pow(&d1).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));

        // argument is too small
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();
        ref_num.m[0] = 1;
        ref_num.n = 1;
        d1.m[0] = 123;
        d1.m[1] = 123;
        d1.n = 7;
        d1.e = -47;
        d2.m[0] = 2;
        d2.n = 1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // 2^123.4567890
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();
        ref_num.m[0] = 5308;
        ref_num.m[1] = 7857;
        ref_num.m[2] = 6147;
        ref_num.m[3] = 8828;
        ref_num.m[4] = 46;
        ref_num.m[5] = 873;
        ref_num.m[6] = 5984; 
        ref_num.m[7] = 9057; 
        ref_num.m[8] = 4749; 
        ref_num.m[9] = 1459;
        ref_num.n = 40;
        ref_num.e = -2;
        d1.m[0] = 7890;
        d1.m[1] = 3456;
        d1.m[2] = 12;
        d1.n = 10;
        d1.e = -7;
        d2.m[0] = 2;
        d2.n = 1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // negative argument
        ref_num = one.div(&ref_num).unwrap();
        d1.sign = DECIMAL_SIGN_NEG;
        let ret = d2.pow(&d1).unwrap();
        assert!(ret.sub(&ref_num).unwrap().abs().cmp(&epsilon) <= 0);

        // negative base
        d2.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_NEG;
        let ret = d2.pow(&d1).unwrap();
        assert!(ret.sub(&ref_num).unwrap().abs().cmp(&epsilon) <= 0);

        // negative base, even int arg
        d1 = BigFloatNum::new();
        d1.m[0] = 2;
        d1.n = 1;
        d2.sign = DECIMAL_SIGN_NEG;
        let ret = d2.pow(&d1).unwrap();
        ref_num = d2.mul(&d2).unwrap();
        assert!(ret.sub(&ref_num).unwrap().abs().cmp(&epsilon) <= 0);

        // negative base, odd int arg
        d1 = d1.add(&BigFloatNum::one()).unwrap();
        d2.sign = DECIMAL_SIGN_NEG;
        let ret = d2.pow(&d1).unwrap();
        ref_num = d2.mul(&d2).unwrap().mul(&d2).unwrap();
        assert!(ret.sub(&ref_num).unwrap().abs().cmp(&epsilon) <= 0);

        let mut ret;
        let mut inv;
        d2 = BigFloatNum::new();
        d2.m[0] = 4560;
        d2.m[1] = 123;
        d2.m[2] = 6789;
        d2.m[3] = 2345;
        d2.m[4] = 651;
        d2.m[5] = 41;
        d2.m[6] = 671;
        d2.m[7] = 100;
        d2.m[8] = 10;
        d2.m[9] = 0;
        d2.n = 34;
        d2.e = -33;
        d1 = BigFloatNum::new();
        d1.m[0] = 2;
        d1.m[1] = 0;
        d1.m[2] = 0;
        d1.n = 10;
        epsilon.e = -79; // 1 digit discrepancy
        d1.e = -8;
        for i in 1..100 {
            for j in 0..10 {
                d2.m[2] = i;
                d2.m[5] = i;
                d1.m[1] = j*1000;
                d1.m[2] = 10+j;
                inv = one.div(&d1).unwrap();
                ret = d2.pow(&d1).unwrap();
                ret = ret.pow(&inv).unwrap();
                assert!(d2.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);
            }
        }
    }
}
