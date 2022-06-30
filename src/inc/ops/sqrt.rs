/// Square root.

use crate::inc::inc::BigFloatInc;
use crate::defs::Error;
use crate::inc::inc::DECIMAL_PARTS;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::inc::inc::ZEROED_MANTISSA;
use crate::inc::ops::tables::sqrt_const::SQRT_VALUES;

const SQRT_OF_10: BigFloatInc = BigFloatInc {
    m: [5551, 3719, 1853, 4327, 3544, 9889, 3319, 8379, 6016, 2776, 3162], 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

impl BigFloatInc {

    /// Return square root of a number.
    ///
    /// # Errors
    ///
    /// Returns ArgumentIsNegative if `self` is less than 0.
    pub fn sqrt(&self) -> Result<Self, Error> {
        if self.sign == DECIMAL_SIGN_NEG {
            return Err(Error::ArgumentIsNegative);
        }

        if self.n == 0 || self.m == ZEROED_MANTISSA {
            return Ok(*self);
        }

        let mut int_num = *self;
        int_num.e = 0;
        let mut sq = Self::sqrt_int(&int_num)?;

        if self.e & 1 != 0 {
            if self.e < 0 {
                sq = sq.div(&SQRT_OF_10)?;
            } else {
                sq = sq.mul(&SQRT_OF_10)?;
            }
        }
        sq.e += self.e/2;
        Ok(sq)
    }

    // sqrt of integer
    fn sqrt_int(d1: &Self) -> Result<Self, Error> {

        // choose initial value
        let mut i = DECIMAL_PARTS - 1;
        while d1.m[i] == 0 && i > 0 {
            i -= 1;
        }
        let j = d1.m[i] / 100;
        let mut n = if i>0 || j > 0 {SQRT_VALUES[i*99 + j as usize]} else {*d1};

        // Newton's method
        let two = Self::two();
        let mut err = *d1;
        loop {
            let nsq = n.mul(&n)?;
            let nd = n.mul(&two)?;
            let n2 = d1.add(&nsq)?.div(&nd)?;
            let err2 = n.sub(&n2)?;
            if err2.cmp(&err) >= 0 {
                break;
            }
            err = err2;
            n = n2;
        }
        Ok(n)
    }

}
