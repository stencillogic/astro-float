/// Square root.

use crate::defs::BigFloatNum;
use crate::defs::Error;


impl BigFloatNum {

    /// Return square root of a number.
    ///
    /// # Errors
    ///
    /// Returns ArgumentIsNegative if `self` is less than 0.
    pub fn sqrt(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.sqrt()?;
        Self::from_big_float_inc(ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::DECIMAL_POSITIONS;
    use crate::defs::DECIMAL_SIGN_NEG;

    #[test]
    fn test_sqrt() {

        let mut d1 ;
        
        let mut epsilon = BigFloatNum::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);

        d1 = BigFloatNum::new();
        d1.m[0] = 10;
        d1.n = 2;
        let ret = d1.sqrt().unwrap();
        let ret = ret.mul(&ret).unwrap();
        assert!(d1.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);


        // sqrt(1234567890.1234567 = 1.2345...+10^9)
        d1 = BigFloatNum::new();
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
        d1 = BigFloatNum::new();
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
        d1 = BigFloatNum::new();
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
        d1 = BigFloatNum::new();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.sqrt().unwrap_err() == Error::ArgumentIsNegative);

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
        d1.e = -36;
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);
        for i in 1..8000 {
            d1.m[8] = 10+i;
            d1.m[9] = i;
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 36;
            ret = d1.sqrt().unwrap();
            ret = ret.mul(&ret).unwrap();
            assert!(ret.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);
        }
    }
}
