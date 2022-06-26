/// Hyperbolic trigonometric functions and inverse hyperbolic trigonometric functions.

use crate::defs::BigFloat;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::Error;
use crate::defs::DECIMAL_SIGN_POS;
use crate::E;

pub const ONE_HALF: BigFloat = BigFloat {
    m: [0, 0, 0, 0, 0, 0, 0, 0, 0, 5000],
    n: 40, 
    sign: DECIMAL_SIGN_POS, 
    e: -40,
};

impl BigFloat {

    /// Returns hyperbolic sine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn sinh(&self) -> Result<BigFloat, Error> {
        // 0.5*(e^x - e^-x)
        let e_x1 = E.pow(self)?;
        let e_x2 = Self::one().div(&e_x1)?;
        e_x1.sub(&e_x2)?.mul(&ONE_HALF)
    }

    /// Returns hyperbolic cosine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn cosh(&self) -> Result<BigFloat, Error> {
        // 0.5*(e^x + e^-x)
        let e_x1 = E.pow(self)?;
        let e_x2 = Self::one().div(&e_x1)?;
        e_x1.add(&e_x2)?.mul(&ONE_HALF)
    }

    /// Returns hyperbolic tangent of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn tanh(&self) -> Result<BigFloat, Error> {
        // (e^x - e^-x) / (e^x + x^-x)
        let e_x1 = E.pow(self)?;
        let e_x2 = Self::one().div(&e_x1)?;
        e_x1.sub(&e_x2)?.div(&e_x1.add(&e_x2)?)
    }

    /// Returns inverse hyperbolic sine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn asinh(&self) -> Result<BigFloat, Error> {
        // ln(x + sqrt(x^2 + 1))
        let x = *self;
        let xx = x.mul(&x)?;
        let arg = x.add(&xx.add(&Self::one())?.sqrt()?)?;
        if arg.n == 0 {
            Err(Error::ExponentOverflow(DECIMAL_SIGN_NEG)) 
        } else {
            arg.ln()
        }
    }

    /// Returns inverse hyperbolic cosine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    /// InvalidArgument - when `self` is less than 1.
    pub fn acosh(&self) -> Result<BigFloat, Error> {
        // ln(x + sqrt(x^2 - 1))
        let x = *self;
        let one = Self::one();
        if x.cmp(&one) < 0 {
            return Err(Error::InvalidArgument);
        }
        let xx = x.mul(&x)?;
        let arg = x.add(&xx.sub(&one)?.sqrt()?)?;
        arg.ln()
    }

    /// Returns inverse hyperbolic tangent of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    /// InvalidArgument - when |`self`| >= 1.
    pub fn atanh(&self) -> Result<BigFloat, Error> {
        // 0.5 * ln( (1+x) / (1-x) )
        let x = *self;
        let one = Self::one();
        if x.abs().cmp(&one) >= 0 {
            return Err(Error::InvalidArgument);
        }
        let arg = one.add(&x)?.div(&one.sub(&x)?)?;
        ONE_HALF.mul(&arg.ln()?)
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::DECIMAL_POSITIONS;
    use crate::defs::DECIMAL_SIGN_NEG;

    #[test]
    fn test_trigh() {

        let mut d1;
        let mut epsilon = BigFloat::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);


        //
        // sinh, asinh
        //


        d1 = BigFloat::new();
        d1.m[7] = 123;
        d1.e = -37;
        epsilon.e = -71; // 1*10^(-32)
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


        d1 = BigFloat::new();
        d1.m[7] = 123;
        d1.e = -37;
        epsilon.e = -71; // 1*10^(-32)
        for i in 0..100 {
            d1.m[8] = 10 + i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i<100 {2} else if i<1000 {3} else {4} + 32;
            let s = d1.cosh().unwrap();
            let mut c = s.acosh().unwrap();
            assert!(c.sign == DECIMAL_SIGN_POS);
            c.sign = d1.sign;
            assert!(d1.sub(&c).unwrap().abs().cmp(&epsilon) <= 0);
        }
        // arg < 1
        d1 = BigFloat::new();
        d1.m[9] = 1;
        d1.n = 37;
        d1.e = -37;
        assert!(d1.acosh().unwrap_err() == Error::InvalidArgument);


        // 
        // tanh and atanh
        //


        d1 = BigFloat::new();
        d1.m[7] = 123;
        d1.e = -37;
        epsilon.e = -70; // 1*10^(-32)
        for i in 0..100 {
            d1.m[8] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 32;
            let s = d1.tanh().unwrap();
            let c = s.atanh().unwrap();
            assert!(d1.sub(&c).unwrap().abs().cmp(&epsilon) <= 0);
        }
    }
}
