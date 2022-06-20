/// Trigonometric functions and inverse trigonometric functions.

use crate::defs::BigFloat;
use crate::defs::Error;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::DECIMAL_POSITIONS;
use crate::increased::BigFloatInc;
use crate::ops::tables::atan_const::ATAN_VALUES1;
use crate::ops::tables::atan_const::ATAN_VALUES2;
use crate::ops::tables::sin_const::SIN_VALUES1;
use crate::ops::tables::sin_const::SIN_VALUES2;
use crate::ops::tables::tan_const::TAN_VALUES;

const HALF_PI: BigFloatInc = BigFloatInc {
    m: [5846, 2098, 5144, 6397, 1691, 3132, 6192, 4896, 2679, 7963, 1570],
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};
const HALF_PI2: BigFloat = BigFloat {
    m: [2099, 5144, 6397, 1691, 3132, 6192, 4896, 2679, 7963, 1570],
    n: DECIMAL_POSITIONS as i16, 
    sign: DECIMAL_SIGN_POS, 
    e: -(DECIMAL_POSITIONS as i8 - 1),
};
const PI2: BigFloatInc = BigFloatInc {
    m: [1694, 4197, 0288, 2795, 3383, 6264, 2384, 9793, 5358, 5926, 3141],
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

impl BigFloat {

    /// Returns sine of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn sin(&self) -> Result<BigFloat, Error> {
        self.sin_cos(0)
    }

    /// Returns cosine of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn cos(&self) -> Result<BigFloat, Error> {
        self.sin_cos(1)
    }

    /// Returns tangent of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn tan(&self) -> Result<BigFloat, Error> {
        // tan(x) = tan(s + dx) = tan(s) + tan(dx) / (1 - tan(s)*tan(dx));
        // tan(s) = sin(s)/cos(s)
        // tan(dx) = x + 1/3*x^3 + 2/15*x^5 + ... (tailor series)
        // do calculation only for angles [0, pi/2)
        let mut x = Self::to_big_float_inc(self);

        // determine quadrant
        let mut quadrant = 0;
        x = x.div(&PI2)?;
        let fractional = x.get_fractional_part();
        x = PI2.mul(&fractional)?;
        while x.cmp(&HALF_PI) > 0 {
            x = PI2.sub(&x)?;
            quadrant = 1;
        }
        let (idx, mut dx) = Self::get_trig_params(&mut x, 1);

        // sin(s) / cos(s) = sin(s) / sin(s + pi/2)
        let tan_s = SIN_VALUES1[idx].div(&SIN_VALUES2[idx])?;

        // tailor series
        let mut tan_dx = dx;
        let dxq = dx.mul(&dx)?;
        let mut i = 0;
        while i < TAN_VALUES.len() {
            dx = dx.mul(&dxq)?;
            let p = dx.mul(&TAN_VALUES[i])?;
            let val = tan_dx.add(&p)?;
            if val.cmp(&tan_dx) == 0 {
                break;
            }
            tan_dx = val;
            i += 1;
            assert!(i != TAN_VALUES.len() - 2);
        }

        // tan(x)
        let d = BigFloatInc::one().sub(&tan_s.mul(&tan_dx)?)?;
        let mut ret = tan_s.add(&tan_dx)?.div(&d)?;
        if (quadrant == 1 && self.sign == DECIMAL_SIGN_POS) || (quadrant == 0 && self.sign == DECIMAL_SIGN_NEG) {
            ret.sign = DECIMAL_SIGN_NEG;
        }
        return Ok(Self::from_big_float_inc(&mut ret)?);
    }

    /// Returns arcsine of a number. Result is an angle in radians ranging from `-pi` to `pi`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    /// InvalidArgument - when |`self`| > 1.
    pub fn asin(&self) -> Result<BigFloat, Error> {
        let one = Self::one();
        if self.abs().cmp(&one) > 0 {
            return Err(Error::InvalidArgument);
        }

        // arcsin(x) = 2*arctan(x / ( 1 + sqrt(1 - x^2)))
        let x = *self;
        let arg = x.div(&one.add(&one.sub(&x.mul(&x)?)?.sqrt()?)?)?;
        Self::two().mul(&arg.atan()?)
    }

    /// Returns arccosine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    /// InvalidArgument - when |`self`| > 1.
    pub fn acos(&self) -> Result<BigFloat, Error> {
        HALF_PI2.sub(&self.asin()?)
    }

    /// Returns arctangent of a number. 
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn atan(&self) -> Result<BigFloat, Error> {
        let one = BigFloatInc::one();
        let mut x = Self::to_big_float_inc(self);
        x.sign = DECIMAL_SIGN_POS;

        // if x > 1 then arctan(x) = pi/2 - arctan(1/x)
        let mut inverse_arg = false;
        if x.abs().cmp(&one) > 0 {
            x = one.div(&x)?;
            inverse_arg = true;
        }

        if x.n == 0 {
            return Ok(Self::new());
        }

        // further reduction: arctan(x) = arctan(s) + arctan((x - s) / (1 + x*s))
        let (idx, mut dx) = Self::get_trig_params(&mut x, 0);
        let atan_s = ATAN_VALUES2[idx];
        let s = x.sub(&dx)?;
        dx = dx.div(&one.add(&x.mul(&s)?)?)?;

        // taylor series
        let mut ret = dx;
        let dxx = dx.mul(&dx)?;
        for i in 0..ATAN_VALUES1.len() {
            dx = dx.mul(&dxx)?;
            let p = ATAN_VALUES1[i].mul(&dx)?;
            let val = ret.add(&p)?;
            if val.cmp(&ret) == 0 {
                break;
            }
            ret = val;
            assert!(i != ATAN_VALUES1.len()-2);
        }

        ret = ret.add(&atan_s)?;

        if inverse_arg {
            ret = HALF_PI.sub(&ret)?;
        }
        ret.sign = self.sign;

        return Ok(Self::from_big_float_inc(&mut ret)?);
    }


    // sin: q=0, cos: q=1; 
    fn sin_cos(&self, q: usize) -> Result<BigFloat, Error> {
        // calculation:
        // x = s + dx, x is in [0, pi/2)
        // use series: sin(x) = sin(s) + sum( der(sin(s), n) * (dx)^n / n! )
        // where: der(sin(s), n) = sin(s + n*pi/2) - n'th derivative of sin
        // use precalculated values: sin(s), sin(s + pi/2), sin(s + pi) = -sin(s), sin(s + 3*pi/2)
        //   = -sin(s + pi/2)
        // do calculation only for angles [0, pi/2)
        let mut x = Self::to_big_float_inc(self);

        // determine quadrant
        let mut quadrant = q;
        x = x.div(&PI2)?;
        let fractional = x.get_fractional_part();
        x = PI2.mul(&fractional)?;
        while x.cmp(&HALF_PI) > 0 {
            x = x.sub(&HALF_PI)?;
            quadrant += 1;
        }
        if quadrant >= 4 {
            quadrant -= 4;
        }
        if x.sign == DECIMAL_SIGN_NEG {
            quadrant = 3 - quadrant;
        }
        let (idx, dx) = Self::get_trig_params(&mut x, 1);

        // determine closest precomputed values of derivatives
        let mut s = [BigFloatInc::new(), BigFloatInc::new(), BigFloatInc::new(), BigFloatInc::new(),];
        s[0] = SIN_VALUES1[idx];
        s[1] = SIN_VALUES2[idx];
        s[2] = s[0];
        s[2].sign = DECIMAL_SIGN_NEG;
        s[3] = s[1];
        s[3].sign = DECIMAL_SIGN_NEG;

        let mut ret = s[quadrant];
        let mut dxn = dx;
        let one = BigFloatInc::one();
        let mut fct = one;
        let mut inc = one;
        let mut der_n = (quadrant + 1) % 4;
        loop {
            let p = dxn.div(&fct)?;
            let der = s[der_n];
            if der.n != 0 {
                let add = der.mul(&p)?;
                let val = ret.add(&add)?;
                if val.cmp(&ret) == 0 {
                    break;
                }
                ret = val;
            }
            dxn = dxn.mul(&dx)?;
            inc = inc.add(&one)?;
            fct = fct.mul(&inc)?;
            der_n += 1;
            if der_n > 3 {
                der_n = 0;
            }
        }
        if q == 0 {
            ret.sign = self.sign;
        }
        if ret.abs().cmp(&one) > 0 {
            ret = one;
        }
        return Ok(Self::from_big_float_inc(&mut ret)?);
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_trig() {

        let mut d1;
        let one = BigFloat::one();
        let mut epsilon = BigFloat::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);

        //
        // sin, cos, asin, acos
        //

        d1 = BigFloat::new();
        d1.e = -39;
        d1.m[8] = 123;
        epsilon.e = -69; // 1*10^(-30)
        for i in 1..9999 {
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else {if i<100 {2} else {if i<1000 {3} else {4}}} + 36;
            let s = d1.sin().unwrap();
            let c = d1.cos().unwrap();
            let p = s.mul(&s).unwrap().add(&c.mul(&c).unwrap()).unwrap();
            assert!(p.sub(&one).unwrap().abs().cmp(&epsilon) <= 0);
        }

        // asin
        d1 = BigFloat::new();
        d1.e = -39;
        d1.m[8] = 123;
        epsilon.e = -75; // 1*10^(-36)
        for i in 1..1571 {  // -pi/2..pi/2
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else {if i<100 {2} else {if i<1000 {3} else {4}}} + 36;
            let s = d1.sin().unwrap();
            let asn = s.asin().unwrap();
            assert!(d1.sub(&asn).unwrap().abs().cmp(&epsilon) <= 0);
        }

        // acos
        d1 = BigFloat::new();
        d1.e = -39;
        d1.m[8] = 123;
        epsilon.e = -75; // 1*10^(-36)
        for i in 1..3142 {  // 0..pi
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else {if i<100 {2} else {if i<1000 {3} else {4}}} + 36;
            let c = d1.cos().unwrap();
            let acs = c.acos().unwrap();
            assert!(d1.abs().sub(&acs).unwrap().abs().cmp(&epsilon) <= 0);
        }


        //
        // tan, atan
        //


        d1 = BigFloat::new();
        d1.e = -39;
        d1.m[0] = 5678;
        d1.m[8] = 1234;
        epsilon.e = -73; // 1*10^(-34) for arguments close to pi/2 the precision is lost
        for i in 1..9999 {
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else {if i<100 {2} else {if i<1000 {3} else {4}}} + 36;
            let t1 = d1.tan().unwrap();
            let t2 = d1.sin().unwrap().div(&d1.cos().unwrap()).unwrap();
            let p = t1.div(&t2).unwrap();
            assert!(p.sub(&one).unwrap().abs().cmp(&epsilon) <= 0);
        }

        d1 = BigFloat::new();
        d1.e = -39;
        d1.m[0] = 5678;
        d1.m[8] = 1234;
        epsilon.e = -78; // 1*10^(-39) for arguments close to pi/2 the precision is lost
        for i in 1..1571 {
            d1.m[9] = i;
            d1.sign = if i & 1 == 0 {DECIMAL_SIGN_POS} else {DECIMAL_SIGN_NEG};
            d1.n = if i < 10 {1} else {if i<100 {2} else {if i<1000 {3} else {4}}} + 36;
            let t1 = d1.tan().unwrap();
            let atn = t1.atan().unwrap();
            assert!(atn.sub(&d1).unwrap().abs().cmp(&epsilon) <= 0);
        }
    }
}
