/// Logarithms.

use crate::inc::inc::BigFloatInc;
use crate::defs::Error;
use crate::inc::inc::DECIMAL_POSITIONS;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::DECIMAL_MIN_EXPONENT;
use crate::defs::DECIMAL_MAX_EXPONENT;
use crate::inc::ops::tables::atan_const::ATAN_VALUES1;
use crate::inc::ops::tables::ln_const::LN_VALUES;
use crate::inc::inc::E;


const LN_OF_10: BigFloatInc = BigFloatInc {
    m: [1015, 7601, 6420, 6843, 1454, 1799, 6840, 4045, 9299, 5850, 2302] , 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

impl BigFloatInc {

    /// Returns natural logarithm of a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    ///
    /// InvalidArgument - when `self` is negative or zero.
    pub fn ln(&self) -> Result<Self, Error> {
        if self.sign == DECIMAL_SIGN_NEG || self.n == 0 {
            return Err(Error::InvalidArgument);
        }

        // factoring: ln(d) = ln(d.m ^ (1 - d.n)) + (d.e - 1 + d.n) * ln(10)
        let mut add = Self::new();
        let mut s = self.e as i16 - 1 + self.n;
        if s != 0 {
            // check if s fits in single "digit"
            assert!(DECIMAL_MAX_EXPONENT as i16 + 1 + (DECIMAL_POSITIONS as i16) < DECIMAL_BASE as i16 && 
               DECIMAL_POSITIONS as i16 + 1 - (DECIMAL_MIN_EXPONENT as i16) < DECIMAL_BASE as i16);
            if s > 0 {
                add.m[0] = s;
            } else {
                add.m[0] = -s;
                add.sign = DECIMAL_SIGN_NEG;
            }
            while s != 0 {
                add.n += 1;
                s /= 10;
            }
            add = add.mul(&LN_OF_10)?;
        }

        let one = BigFloatInc::one();
        let two = BigFloatInc::two();
        let mut ml = *self;
        ml.e = 1 - ml.n as i8;

        // arctanh series
        ml = ml.sub(&one)?.div(&ml.add(&one)?)?;    // (x-1)/(x+1)

        // further reduction: arctanh(x) = arctanh(s) + arctanh((x - s) / (1 - x*s))
        let (idx, mut dx) = Self::get_trig_params(&mut ml, 0);
        let atanh_s = LN_VALUES[idx];
        let s = ml.sub(&dx)?;
        dx = dx.div(&one.sub(&ml.mul(&s)?)?)?;

        let mut ret = dx;
        let dxx = dx.mul(&dx)?;
        for i in 0..ATAN_VALUES1.len() {
            dx = dx.mul(&dxx)?;
            let mut poly_coeff = ATAN_VALUES1[i];
            poly_coeff.sign = DECIMAL_SIGN_POS;     // same as for atan, but always positive
            let p = poly_coeff.mul(&dx)?;
            let val = ret.add(&p)?;
            if val.cmp(&ret) == 0 {
                break;
            }
            ret = val;
            assert!(i != ATAN_VALUES1.len()-2);
        }
        ret = ret.add(&atanh_s)?.mul(&two)?.add(&add)?;

        Ok(ret)
    }

    /// E to the power of `self`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    ///
    /// ArgumentIsNegative - when `d1` has fractional part and `self` is negative.
    pub fn exp(&self) -> Result<Self, Error> {
        E.pow(self)
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
        self.ln()?.div(&b.ln()?)
    }
}
