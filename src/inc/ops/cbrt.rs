//! Cube root.

use crate::inc::inc::BigFloatInc;
use crate::defs::Error;
use crate::inc::inc::DECIMAL_PARTS;
use crate::inc::inc::ZEROED_MANTISSA;
use crate::defs::DECIMAL_SIGN_POS;
use crate::inc::ops::tables::cbrt_const::CBRT_VALUES;


const ONE_THIRD: BigFloatInc = BigFloatInc {
    m: [3333, 3333, 3333, 3333, 3333, 3333, 3333, 3333, 3333, 3333, 3333], 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -44,
};

const TWO_THIRD: BigFloatInc = BigFloatInc {
    m: [6667, 6666, 6666, 6666, 6666, 6666, 6666, 6666, 6666, 6666, 6666], 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -44,
};

const CBRT_OF_10: BigFloatInc = BigFloatInc {
    m: [3449, 5259, 5049, 5193, 3566, 5929, 7217, 1883, 9003, 4346, 2154], 
    n: 44, 
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

const CBRT_OF_100: BigFloatInc = BigFloatInc {
    m: [3491, 6551, 4657, 9194, 6350, 1007, 8924, 2778, 3361, 5888, 4641], 
    n: 44,
    sign: DECIMAL_SIGN_POS, 
    e: -43,
};

impl BigFloatInc {

    /// Return cube root of a number.
    pub fn cbrt(&self) -> Result<Self, Error> {
        // cbrt(self) = cbrt(mantissa)*cbrt(10^exponent)
        // = cbrt(mantissa)*cbrt(10^(exponent%3))*10^(exponent/3)
        if self.n == 0 || self.m == ZEROED_MANTISSA {
            return Ok(*self);
        }

        // cbrt(mantissa)
        let mut int_num = *self;
        int_num.e = 0;
        int_num.sign = DECIMAL_SIGN_POS;
        let part1 = Self::cbrt_int(&int_num)?;

        let e = (self.e as i32).abs() % 3;
        let mut ret = if e > 0 {
            // cbrt(10^(exponent%3))
            let part2 = if e < 2 { CBRT_OF_10 } else { CBRT_OF_100 };

            // result
            if self.e < 0 {
                part1.div(&part2)
            } else {
                part1.mul(&part2)
            }?
        } else {
            part1
        };
        ret.e += self.e/3;
        ret.sign = self.sign;
        Ok(ret)
    }

    // cube root of integer
    fn cbrt_int(d1: &Self) -> Result<Self, Error> {

        // choose initial value
        let mut i = DECIMAL_PARTS - 1;
        while d1.m[i] == 0 && i > 0 {
            i -= 1;
        }
        let j = d1.m[i] / 100;
        let mut n = if i > 0 || j > 0 {CBRT_VALUES[i*99 + j as usize]} else {*d1};

        // Newton's method: n2 = d1/3/n/n + 2/3*n
        let s = d1.mul(&ONE_THIRD)?;
        let mut err = *d1;
        loop {
            if n.n == 0 {
                break;
            }
            let p1 = s.div(&n)?.div(&n)?;
            let p2 = TWO_THIRD.mul(&n)?;
            let n2 = p1.add(&p2)?;
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
