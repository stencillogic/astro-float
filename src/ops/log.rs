/// Logarithms.

use crate::defs::BigFloatNum;
use crate::defs::Error;

impl BigFloatNum {

    /// Returns natural logarithm of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    ///
    /// InvalidArgument - when `self` is negative or zero.
    pub fn ln(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.ln()?;
        Self::from_big_float_inc(ret)
    }

    /// E to the power of `self`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn exp(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.exp()?;
        Self::from_big_float_inc(ret)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::E;
    use crate::defs::DECIMAL_POSITIONS;
    use crate::defs::DECIMAL_SIGN_NEG;

    #[test]
    fn test_log() {

        let mut d1;
        let mut d2;
        let one = BigFloatNum::one();
        let mut epsilon = BigFloatNum::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);

        // arg = 0
        d1 = BigFloatNum::new();
        assert!(d1.ln().unwrap_err() == Error::InvalidArgument);

        // arg < 0
        d1 = BigFloatNum::one();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.ln().unwrap_err() == Error::InvalidArgument);

        // ln of E = 1
        epsilon.e = -77;    // 1*10^(-39)
        assert!(E.ln().unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);

        d2 = BigFloatNum::new();
        d2.m[0] = 4567;
        d2.m[1] = 123;
        d2.m[2] = 6789;
        d2.m[3] = 2345;
        d2.m[4] = 651;
        d2.m[5] = 41;
        d2.m[6] = 671;
        d2.m[7] = 9999;
        d2.m[8] = 0;
        d2.m[9] = 0;
        d2.e = -10;
        for i in 264..1000 {
            d2.m[2] = i;
            d2.m[7] = i;
            d2.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 28;
            d2.e = -50 + (i%100) as i8;
            let ret = d2.ln().unwrap();
            d1 = ret.exp().unwrap();
            assert!(d2.sub(&d1).unwrap().n <= 3);
        }
    }
}
