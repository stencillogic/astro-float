/// Trigonometric functions and inverse trigonometric functions.

use crate::defs::BigFloatNum;
use crate::defs::Error;

impl BigFloatNum {

    /// Returns sine of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn sin(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let mut ret = arg.sin()?;
        Self::from_big_float_inc(&mut ret)
    }

    /// Returns cosine of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn cos(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let mut ret = arg.cos()?;
        Self::from_big_float_inc(&mut ret)
    }

    /// Returns tangent of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn tan(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let mut ret = arg.tan()?;
        Self::from_big_float_inc(&mut ret)
    }

    /// Returns arcsine of a number. Result is an angle in radians ranging from `-pi` to `pi`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    /// InvalidArgument - when |`self`| > 1.
    pub fn asin(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let mut ret = arg.asin()?;
        Self::from_big_float_inc(&mut ret)
    }

    /// Returns arccosine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    /// InvalidArgument - when |`self`| > 1.
    pub fn acos(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let mut ret = arg.acos()?;
        Self::from_big_float_inc(&mut ret)
    }

    /// Returns arctangent of a number. 
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn atan(&self) -> Result<Self, Error> {
        let arg = Self::to_big_float_inc(self);
        let mut ret = arg.atan()?;
        Self::from_big_float_inc(&mut ret)
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::DECIMAL_SIGN_POS;
    use crate::defs::DECIMAL_SIGN_NEG;
    use crate::defs::DECIMAL_POSITIONS;

    #[test]
    fn test_trig_fun() {

        let mut d1;
        let one = BigFloatNum::one();
        let mut epsilon = BigFloatNum::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);


        //
        // sin, cos, asin, acos
        //

        d1 = BigFloatNum::new();
        d1.e = -39;
        d1.m[0] = 123;
        d1.m[3] = 123;
        d1.m[7] = 123;
        for i in 1..1572 {
            d1.m[8] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 36;
            let s = d1.sin().unwrap();
            let c = d1.cos().unwrap();
            let p = s.mul(&s).unwrap().add(&c.mul(&c).unwrap()).unwrap();
            assert!(p.sub(&one).unwrap().abs().n <= 1);
        }

        // asin
        d1 = BigFloatNum::new();
        d1.e = -39;
        d1.m[0] = 123;
        d1.m[3] = 123;
        d1.m[7] = 123;
        for i in 1..1571 {  // -pi/2..pi/2
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 36;
            let s = d1.sin().unwrap();
            let asn = s.asin().unwrap();
            assert!(d1.sub(&asn).unwrap().abs().n <= 2);
        }

        // acos
        d1 = BigFloatNum::new();
        d1.e = -39;
        d1.m[8] = 123;
        epsilon.e = -71; // 1*10^(-32)
        for i in 1..3142 {  // 0..pi
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 36;
            let c = d1.cos().unwrap();
            let acs = c.acos().unwrap();
            assert!(d1.abs().sub(&acs).unwrap().abs().cmp(&epsilon) <= 0);
        }


        //
        // tan, atan
        //


        d1 = BigFloatNum::new();
        d1.e = -39;
        d1.m[0] = 5678;
        d1.m[7] = 1234;
        epsilon.e = -77; // 1*10^(-38) for arguments close to pi/2 the precision is lost
        for i in 1..9999 {
            d1.m[8] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 32;
            let t1 = d1.tan().unwrap();
            let t2 = d1.sin().unwrap().div(&d1.cos().unwrap()).unwrap();
            let p = t1.div(&t2).unwrap();
            assert!(p.sub(&one).unwrap().abs().cmp(&epsilon) <= 0);
        }

        d1 = BigFloatNum::new();
        d1.e = -39;
        d1.m[0] = 5678;
        d1.m[7] = 1234;
        epsilon.e = -78; // 1*10^(-39) for arguments close to pi/2 the precision is lost
        for i in 1..1571 {
            d1.m[8] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else if i<100 {2} else if i<1000 {3} else {4} + 32;
            let t1 = d1.tan().unwrap();
            let atn = t1.atan().unwrap();
            assert!(atn.sub(&d1).unwrap().abs().cmp(&epsilon) <= 0);
        }
    }
}
