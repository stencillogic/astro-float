/// Square root.

use crate::defs::BigFloat;
use crate::defs::Error;
use crate::defs::DECIMAL_PARTS;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::ZEROED_MANTISSA;
use crate::increased::BigFloatInc;
use crate::ops::tables::sqrt_const::SQRT_VALUES;

const SQRT_OF_10: BigFloatInc = BigFloatInc {
    m: [5551, 3719, 1853, 4327, 3544, 9889, 3319, 8379, 6016, 2776, 3162], 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

impl BigFloat {

    /// Return square root of a number.
    ///
    /// # Errors
    ///
    /// Returns ArgumentIsNegative if `self` is less than 0.
    pub fn sqrt(&self) -> Result<BigFloat, Error> {
        if self.sign == DECIMAL_SIGN_NEG {
            return Err(Error::ArgumentIsNegative);
        }

        if self.n == 0 || self.m == ZEROED_MANTISSA {
            return Ok(*self);
        }

        let mut int_num = Self::to_big_float_inc(self);
        int_num.e = 0;
        let mut sq = Self::sqrt_int(&int_num)?;

        if self.e & 1 != 0 {
            if self.e < 0 {
                sq = sq.div(&SQRT_OF_10)?;
            } else {
                sq = sq.mul(&SQRT_OF_10)?;
            }
        }
        let mut ret = Self::from_big_float_inc(&mut sq)?;
        ret.e += self.e/2;
        return Ok(ret);
    }

    // sqrt of integer
    fn sqrt_int(d1: &BigFloatInc) -> Result<BigFloatInc, Error> {

        // choose initial value
        let mut i = DECIMAL_PARTS - 1;
        while d1.m[i] == 0 && i > 0 {
            i -= 1;
        }
        let j = d1.m[i] / 100;
        let mut n = Self::to_big_float_inc(&SQRT_VALUES[i*99 + j as usize]);

        // Newton's method
        let mut two = BigFloatInc::new();
        two.m[0] = 2;
        two.n = 1;
        let mut err = *d1;
        loop {
            let nsq = n.mul(&n)?;
            let nd = n.mul(&two)?;
            let n2 = d1.add(&nsq)?.div(&nd)?;
            let err2 = n.sub(&n2)?;
            if err2.cmp(&err) >= 0 {
                break;
            }
            err = err2;
            n = n2;
        }
        return Ok(n);
    }

}


#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::DECIMAL_POSITIONS;

    #[test]
    fn test_sqrt() {

        let mut d1 ;

        let mut epsilon = BigFloat::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);

        d1 = BigFloat::new();
        d1.m[0] = 10;
        d1.n = 2;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) < 0);


        // sqrt(1234567890.1234567 = 1.2345...+10^9)
        d1 = BigFloat::new();
        d1.m[0] = 4567;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 1;
        d1.n = 17;
        d1.e = -7;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        epsilon.e = -69;    // 1*10^(-30)
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);

        // positive exponent
        d1 = BigFloat::new();
        d1.m[0] = 4567;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 1;
        d1.n = 17;
        d1.e = 7;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        epsilon.e = -55;    // 1*10^(-16)
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);

        // value less than 1
        d1 = BigFloat::new();
        d1.m[0] = 4567;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 1;
        d1.n = 17;
        d1.e = -20;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        epsilon.e = -82;    // 1*10^(-43)
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);

        // value is negative
        d1 = BigFloat::new();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.sqrt().unwrap_err() == Error::ArgumentIsNegative);
    }
}
