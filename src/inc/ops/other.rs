/// Other operations.

use crate::inc::inc::BigFloatInc;
use crate::defs::DECIMAL_BASE_LOG10;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;

impl BigFloatInc {

    /// Return absolute value. 
    pub fn abs(&self) -> Self {
        let mut ret = *self;
        if ret.sign == DECIMAL_SIGN_NEG {
            ret.sign = DECIMAL_SIGN_POS;
        }
        ret
    }

    /// Return absolute value. 
    pub fn inv_sign(&self) -> Self {
        let mut ret = *self;
        if ret.sign == DECIMAL_SIGN_NEG {
            ret.sign = DECIMAL_SIGN_POS;
        } else {
            ret.sign = DECIMAL_SIGN_NEG;
        }
        ret
    }


    /// Compare to d2.
    /// Returns positive if self > d2, negative if self < d2, 0 otherwise.
    pub fn cmp(&self, d2: &Self) -> i16 {
        if self.sign != d2.sign {
            return self.sign as i16;
        }

        if self.n == 0 || d2.n == 0 {
            if d2.n != 0 {
                return -d2.sign as i16;
            } else if self.n != 0 {
                return self.sign as i16;
            } else {
                return 0;
            }
        }

        let diff: i32 = self.e as i32 + self.n as i32 - d2.e as i32 - d2.n as i32;
        if diff > 0 {
            return self.sign as i16;
        }
        if diff < 0 {
            return -self.sign as i16;
        }

        if self.n != d2.n {
            return Self::abs_cmp_with_shift(&self.m, self.n, &d2.m, d2.n) * self.sign as i16;
        }

        Self::abs_cmp(&self.m, &d2.m) * self.sign as i16
    }

    // compare absolute values of two floats with shifts n1, n2
    // return positive if d1 > d2, negative if d1 < d2, 0 otherwise
    fn abs_cmp_with_shift(d1: &[i16], mut n1: i16, d2: &[i16], mut n2: i16) -> i16 {
        let mut t1: i16 = DECIMAL_BASE as i16 / 10;
        let mut t2: i16 = DECIMAL_BASE as i16 / 10;
        let mut s: i16;
        let mut v1: i16;
        let mut v2: i16;

        s = DECIMAL_BASE_LOG10 as i16 - n1 % DECIMAL_BASE_LOG10 as i16;
        while s > 0 {
            s -= 1;
            t1 /= 10;
            if t1 == 0 {
                t1 = DECIMAL_BASE as i16 / 10;
            };
        }
        s = DECIMAL_BASE_LOG10 as i16 - n2 % DECIMAL_BASE_LOG10 as i16;
        while s > 0 {
            s -= 1;
            t2 /= 10;
            if t2 == 0 {
                t2 = DECIMAL_BASE as i16 / 10;
            };
        }

        n1 -= 1;
        n2 -= 1;
        while n1 >= 0 && n2 >= 0 {
            v1 = (d1[n1 as usize / DECIMAL_BASE_LOG10] / t1) % 10;
            v2 = (d2[n2 as usize / DECIMAL_BASE_LOG10] / t2) % 10;
            if v1 != v2 {
                return v1 - v2;
            }
            t1 /= 10;
            if t1 == 0 {
                t1 = DECIMAL_BASE as i16 / 10;
            }
            t2 /= 10;
            if t2 == 0 {
                t2 = DECIMAL_BASE as i16 / 10;
            }
            n1 -= 1;
            n2 -= 1;
        }
        while n1 >=0 {
            v1 = (d1[n1 as usize / DECIMAL_BASE_LOG10] / t1) % 10;
            if v1 != 0 {
                return 1;
            }
            n1 -= 1;
        }
        while n2 >=0 {
            v2 = (d2[n2 as usize / DECIMAL_BASE_LOG10] / t2) % 10;
            if v2 != 0 {
                return -1;
            }
            n2 -= 1;
        }
        0
    }
}
