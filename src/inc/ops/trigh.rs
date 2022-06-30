/// Hyperbolic trigonometric functions and inverse hyperbolic trigonometric functions.

use crate::inc::inc::BigFloatInc;
use crate::inc::inc::DECIMAL_POSITIONS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::Error;
use crate::defs::DECIMAL_SIGN_POS;

const ONE_HALF: BigFloatInc = BigFloatInc {
    m: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5000],
    n: DECIMAL_POSITIONS as i16, 
    sign: DECIMAL_SIGN_POS, 
    e: -(DECIMAL_POSITIONS as i8),
};

impl BigFloatInc {

    /// Returns hyperbolic sine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn sinh(&self) -> Result<Self, Error> {
        // 0.5*(e^x - e^-x)
        let e_x1 = if self.sign == DECIMAL_SIGN_NEG {
            self.inv_sign().exp()
        } else {
            self.exp()
        }?;
        let e_x2 = Self::one().div(&e_x1)?;
        let mut ret = e_x1.sub(&e_x2)?.mul(&ONE_HALF)?;
        ret.sign = self.sign;
        Ok(ret)
    }

    /// Returns hyperbolic cosine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn cosh(&self) -> Result<Self, Error> {
        // 0.5*(e^x + e^-x)
        let e_x1 = if self.sign == DECIMAL_SIGN_NEG {
            self.inv_sign().exp()
        } else {
            self.exp()
        }?;
        let e_x2 = Self::one().div(&e_x1)?;
        e_x1.add(&e_x2)?.mul(&ONE_HALF)
    }

    /// Returns hyperbolic tangent of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn tanh(&self) -> Result<Self, Error> {
        // (e^x - e^-x) / (e^x + e^-x)
        let e_x1 = if self.sign == DECIMAL_SIGN_NEG {
            self.inv_sign().exp()
        } else {
            self.exp()
        }?;
        let e_x2 = Self::one().div(&e_x1)?;
        let mut ret = e_x1.sub(&e_x2)?.div(&e_x1.add(&e_x2)?)?;
        ret.sign = self.sign;
        Ok(ret)
    }

    /// Returns inverse hyperbolic sine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn asinh(&self) -> Result<Self, Error> {
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
    /// ExponentOverflow - when result is too big.
    /// InvalidArgument - when `self` is less than 1.
    pub fn acosh(&self) -> Result<Self, Error> {
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
    /// ExponentOverflow - when result is too big.
    /// InvalidArgument - when |`self`| >= 1.
    pub fn atanh(&self) -> Result<Self, Error> {
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
