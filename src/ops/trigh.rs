//! Hyperbolic trigonometric functions and inverse hyperbolic trigonometric functions.

use crate::defs::BigFloatNum;
use crate::defs::Error;


impl BigFloatNum {

    /// Returns hyperbolic sine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn sinh(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.sinh()?;
        Self::from_big_float_inc(ret)
    }

    /// Returns hyperbolic cosine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn cosh(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.cosh()?;
        Self::from_big_float_inc(ret)
    }

    /// Returns hyperbolic tangent of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn tanh(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.tanh()?;
        Self::from_big_float_inc(ret)
    }

    /// Returns inverse hyperbolic sine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn asinh(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.asinh()?;
        Self::from_big_float_inc(ret)
    }

    /// Returns inverse hyperbolic cosine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    /// InvalidArgument - when `self` is less than 1.
    pub fn acosh(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.acosh()?;
        Self::from_big_float_inc(ret)
    }

    /// Returns inverse hyperbolic tangent of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    /// InvalidArgument - when |`self`| >= 1.
    pub fn atanh(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let ret = arg.atanh()?;
        Self::from_big_float_inc(ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::DECIMAL_POSITIONS;
    use crate::defs::DECIMAL_SIGN_NEG;
    use crate::defs::DECIMAL_SIGN_POS;

    #[test]
    fn test_trigh() {

        let mut d1;
        let mut epsilon = BigFloatNum::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);


        //
        // sinh, asinh
        //


        d1 = BigFloatNum::new();
        d1.m[7] = 123;
        d1.e = -37;
        epsilon.e = -76; // 1*10^(-37)
        for i in 1..100 {
            d1.m[8] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 32;
            let s = d1.sinh().unwrap();
            let c = s.asinh().unwrap();
            assert!(d1.sub(&c).unwrap().abs().cmp(&epsilon) <= 0);
        }


        //
        // cosh, acosh
        //


        d1 = BigFloatNum::new();
        d1.m[7] = 123;
        d1.e = -37;
        epsilon.e = -74; // 1*10^(-35)
        for i in 0..100 {
            d1.m[8] = 10 + i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = BigFloatNum::num_digits(&d1.m);
            let s = d1.cosh().unwrap();
            let mut c = s.acosh().unwrap();
            assert!(c.sign == DECIMAL_SIGN_POS);
            c.sign = d1.sign;
            assert!(d1.sub(&c).unwrap().abs().cmp(&epsilon) <= 0);
        }
        // arg < 1
        d1 = BigFloatNum::new();
        d1.m[9] = 1;
        d1.n = 37;
        d1.e = -37;
        assert!(d1.acosh().unwrap_err() == Error::InvalidArgument);


        // 
        // tanh and atanh
        //


        d1 = BigFloatNum::new();
        d1.m[7] = 123;
        d1.e = -37;
        epsilon.e = -75; // 1*10^(-36)
        for i in 0..1000 {
            d1.m[8] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 32;
            let s = d1.tanh().unwrap();
            let c = s.atanh().unwrap();
            assert!(d1.sub(&c).unwrap().abs().cmp(&epsilon) <= 0);
        }
    }
}
