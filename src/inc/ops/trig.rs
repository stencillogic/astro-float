/// Trigonometric functions and inverse trigonometric functions.

use crate::inc::inc::BigFloatInc;
use crate::defs::Error;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::inc::ops::tables::atan_const::ATAN_VALUES1;
use crate::inc::ops::tables::atan_const::ATAN_VALUES2;
use crate::inc::ops::tables::sin_const::SIN_VALUES1;
use crate::inc::ops::tables::sin_const::SIN_VALUES2;
use crate::inc::ops::tables::tan_const::TAN_VALUES;

const HALF_PI: BigFloatInc = BigFloatInc {
    m: [5846, 2098, 5144, 6397, 1691, 3132, 6192, 4896, 2679, 7963, 1570],
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};
const PI: BigFloatInc = BigFloatInc {
    m: [1694, 4197, 288, 2795, 3383, 6264, 2384, 9793, 5358, 5926, 3141],
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};
const PI2: BigFloatInc = BigFloatInc {
    m: [3388, 8394, 576, 5590, 6766, 2528, 4769, 9586, 717, 1853, 6283],
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

impl BigFloatInc {

    /// Returns sine of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn sin(&self) -> Result<Self, Error> {
        self.sin_cos(0)
    }

    /// Returns cosine of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn cos(&self) -> Result<Self, Error> {
        self.sin_cos(1)
    }

    /// Returns tangent of a number. Argument is an angle in radians.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn tan(&self) -> Result<Self, Error> {
        // tan(x) = tan(s + dx) = tan(s) + tan(dx) / (1 - tan(s)*tan(dx));
        // tan(s) = sin(s)/cos(s)
        // tan(dx) = x + 1/3*x^3 + 2/15*x^5 + ... (tailor series)
        // do calculation only for angles [0, pi/2)
        let mut x = *self;

        // determine quadrant
        let mut quadrant = 0;
        x = x.div(&PI)?;
        let fractional = x.get_fractional_part();
        x = PI.mul(&fractional)?;
        while x.cmp(&HALF_PI) > 0 {
            x = PI.sub(&x)?;
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
        Ok(ret)
    }

    /// Returns arcsine of a number. Result is an angle in radians ranging from `-pi` to `pi`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    /// InvalidArgument - when |`self`| > 1.
    pub fn asin(&self) -> Result<Self, Error> {
        let one = Self::one();
        let cmp_to_one = self.abs().cmp(&one);
        if cmp_to_one > 0 {
            return Err(Error::InvalidArgument);
        } else if cmp_to_one == 0 {
            return Ok(if self.sign == DECIMAL_SIGN_NEG { HALF_PI.inv_sign() } else { HALF_PI });
        }

        // arcsin(x) = arctan(x / sqrt(1 - x^2))
        let x = *self;
        let d = one.sub(&x.mul(&x)?)?.sqrt()?;
        if d.n == 0 {
            return Ok(HALF_PI);
        }
        let arg = x.div(&d)?;
        arg.atan()
    }

    /// Returns arccosine of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    /// InvalidArgument - when |`self`| > 1.
    pub fn acos(&self) -> Result<Self, Error> {
        HALF_PI.sub(&self.asin()?)
    }

    /// Returns arctangent of a number. 
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn atan(&self) -> Result<Self, Error> {
        if self.n == 0 {
            return Ok(Self::new());
        }

        let one = BigFloatInc::one();
        let mut x = *self;
        x.sign = DECIMAL_SIGN_POS;

        // if x > 1 then arctan(x) = pi/2 - arctan(1/x)
        let mut inverse_arg = false;
        let x_one_cmp = x.abs().cmp(&one);
        if x_one_cmp > 0 {
            x = one.div(&x)?;
            if x.n == 0 {
                return Ok(if self.sign == DECIMAL_SIGN_NEG { 
                    HALF_PI.inv_sign() 
                } else { 
                    HALF_PI 
                });
            }
            inverse_arg = true;
        } else if x_one_cmp == 0 {
            return Ok(ATAN_VALUES2[10000]);
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

        Ok(ret)
    }


    // sin: q=0, cos: q=1; 
    fn sin_cos(&self, q: usize) -> Result<Self, Error> {
        // calculation:
        // x = s + dx, x is in [0, pi/2)
        // use series: sin(x) = sin(s) + sum( der(sin(s), n) * (dx)^n / n! )
        // where: der(sin(s), n) = sin(s + n*pi/2) - n'th derivative of sin
        // use precalculated values: sin(s), sin(s + pi/2), sin(s + pi) = -sin(s), sin(s + 3*pi/2)
        //   = -sin(s + pi/2)
        // do calculation only for angles [0, pi/2)
        let mut x = *self;

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
        let (idx, dx) = Self::get_trig_params(&mut x, 1);

        // determine closest precomputed values of derivatives
        let mut s = [Self::new(), Self::new(), Self::new(), Self::new(),];
        s[0] = SIN_VALUES1[idx];
        s[1] = SIN_VALUES2[idx];
        s[2] = s[0];
        s[2].sign = DECIMAL_SIGN_NEG;
        s[3] = s[1];
        s[3].sign = DECIMAL_SIGN_NEG;

        let mut ret = s[quadrant];
        let mut dxn = dx;
        let one = Self::one();
        // TODO: precompute factorials as polynomial coeffs.
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
        ret.sign = if quadrant > 1 {
            DECIMAL_SIGN_NEG
        } else {
            DECIMAL_SIGN_POS
        };
        if q == 0 {
            ret.sign *= self.sign;
        }
        if ret.abs().cmp(&one) > 0 {
            ret = if ret.sign == DECIMAL_SIGN_NEG { one.inv_sign() } else { one };
        }
        Ok(ret)
    }
}
