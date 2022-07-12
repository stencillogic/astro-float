/// Logarithms.

use crate::defs::BigFloatNum;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_PARTS;
use crate::defs::DECIMAL_POSITIONS;
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

    /// Returns logarithm of base `b` of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    ///
    /// InvalidArgument - when `self` or `b` is negative or zero.
    ///
    /// DivisionByZero - when `b` is equal to 1.
    pub fn log(&self, b: &Self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let base = Self::to_big_float_inc(b);
        let ret = arg.log(&base)?;
        Self::from_big_float_inc(ret)
    }


    /// Returns logarithm of base 2 of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    ///
    /// InvalidArgument - when `self` or `b` is negative or zero.
    pub fn log2(&self) -> Result<Self, Error> {
        let mut two = Self::new();
        two.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16/5;
        two.n = DECIMAL_POSITIONS as i16;
        two.e = 1 - DECIMAL_POSITIONS as i8;
        self.log(&two)
    }

    /// Returns logarithm of base 10 of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    ///
    /// InvalidArgument - when `self` or `b` is negative or zero.
    pub fn log10(&self) -> Result<Self, Error> {
        let mut ten = Self::new();
        ten.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16/10;
        ten.n = DECIMAL_POSITIONS as i16;
        ten.e = 2 - DECIMAL_POSITIONS as i8;
        self.log(&ten)
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
        let two = one.add(&one).unwrap();
        let mut epsilon = BigFloatNum::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);

        // arg = 0
        d1 = BigFloatNum::new();
        assert!(d1.ln().unwrap_err() == Error::InvalidArgument);
        assert!(d1.log(&two).unwrap_err() == Error::InvalidArgument);

        // base = 0
        assert!(two.log(&d1).unwrap_err() == Error::InvalidArgument);

        // arg < 0
        d1 = BigFloatNum::one();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.ln().unwrap_err() == Error::InvalidArgument);
        assert!(d1.log(&two).unwrap_err() == Error::InvalidArgument);

        // base < 0
        assert!(two.log(&d1).unwrap_err() == Error::InvalidArgument);

        // ln of E = 1
        epsilon.e = -77;    // 1*10^(-39)
        assert!(E.ln().unwrap().sub(&one).unwrap().abs().cmp(&epsilon) <= 0);

        // log2 of 4 = 2
        let four = two.add(&two).unwrap();
        assert!(four.log(&two).unwrap().sub(&two).unwrap().abs().cmp(&epsilon) <= 0);

        // log0.5 of 4 = -2
        let half = one.div(&two).unwrap();
        assert!(four.log(&half).unwrap().add(&two).unwrap().abs().cmp(&epsilon) <= 0);

        // base = 1
        assert!(four.log(&one).unwrap_err() == Error::DivisionByZero);


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

            // base > 1
            let ret = d2.log(&two).unwrap();
            d1 = two.pow(&ret).unwrap();
            assert!(d2.sub(&d1).unwrap().n <= 3);

            // base < 1
            let ret = d2.log(&half).unwrap();
            d1 = half.pow(&ret).unwrap();
            assert!(d2.sub(&d1).unwrap().n <= 3);
        }

        // log2
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);
        assert!(four.log2().unwrap().sub(&two).unwrap().abs().cmp(&epsilon) <= 0);

        // log10
        d1 = BigFloatNum::new();
        d1.m[0] = 100;
        d1.n = 3;
        assert!(d1.log10().unwrap().sub(&two).unwrap().abs().cmp(&epsilon) <= 0);
    }
}
