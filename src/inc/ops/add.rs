/// Addition and subtraction.

use crate::inc::inc::BigFloatInc;
use crate::defs::Error;
use crate::inc::inc::DECIMAL_PARTS;
use crate::inc::inc::DECIMAL_POSITIONS;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_MAX_EXPONENT;
use crate::inc::inc::ZEROED_MANTISSA;


impl BigFloatInc {

    /// Add d2 and return result of addition.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn add(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, 1)
    }

    /// Subtract d2 and return result of subtraction.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn sub(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, -1)
    }

    // add if op >= 0 subtract if op < 0
    fn add_sub(&self, d2: &Self, op: i8) -> Result<Self, Error> {
        let mut d3 = Self::new();
        let shift: i32;
        let free: i32;
        let mut e: i32;
        let cmp: i16;
        let mut n1: Self;
        let mut n2: Self;

        // one of the numbers is zero
        if 0 == self.n {
            d3 = *d2;
            if op < 0
            // 0 - d2
            {
                d3.sign = -d3.sign;
            }
            return Ok(d3);
        }
        if 0 == d2.n {
            d3 = *self;
            return Ok(d3);
        }

        // assign d1 and d2 to n1 and n2 such that n1 has more significant digits than n2
        // (we want to save more digits while not sacrificing any significant digits)
        if self.e as i32 + (self.n as i32) < d2.e as i32 + d2.n as i32 {
            n1 = if op < 0 {d2.inv_sign()} else {*d2};
            n2 = *self;
        } else {
            n1 = *self;
            n2 = if op < 0 {d2.inv_sign()} else {*d2};
        }
        shift = n1.e as i32 - n2.e as i32;
        e = n1.e as i32;

        // bring n1 and n2 to having common exponent
        if shift > 0 {
            free = DECIMAL_POSITIONS as i32 - n1.n as i32;

            if shift > free {
                if shift - free > n2.n as i32 {
                    // n2 is too small
                    d3 = n1;
                    return Ok(d3);
                } else {
                    if free > 0 {
                        Self::shift_left(&mut n1.m, free as usize);
                    }
                    Self::shift_right(&mut n2.m, (shift - free) as usize);
                    e -= free;
                }
            } else {
                Self::shift_left(&mut n1.m, shift as usize);
                e -= shift;
            }
        } else if shift < 0 {
            Self::shift_left(&mut n2.m, (-shift) as usize);
        }

        if n1.sign != n2.sign {
            // subtract
            cmp = Self::abs_cmp(&n1.m, &n2.m);
            if cmp > 0 {
                d3.sign = n1.sign;
                d3.e = e as i8;
                Self::abs_sub(&n1.m, &n2.m, &mut d3.m);
                d3.n = Self::num_digits(&d3.m);
            } else if cmp < 0 {
                d3.sign = n2.sign;
                d3.e = e as i8;
                Self::abs_sub(&n2.m, &n1.m, &mut d3.m);
                d3.n = Self::num_digits(&d3.m);
            } else {
                d3.sign = DECIMAL_SIGN_POS;
                d3.e = 0;
                d3.n = 0;
                d3.m = ZEROED_MANTISSA;
            }
        } else {
            // add
            d3.sign = n1.sign;
            d3.e = e as i8;
            if Self::abs_add(&n1.m, &n2.m, &mut d3.m) > 0 {
                if d3.e == DECIMAL_MAX_EXPONENT {
                    return Err(Error::ExponentOverflow(d3.sign));
                }
                d3.e += 1;
                if Self::round_mantissa(&mut d3.m, 1) {
                    // e.g. m = 998, round 1 => m = 100, m is suppoed o be shifted right by
                    // one digit, so no additional shift required.
                    if d3.e == DECIMAL_MAX_EXPONENT {
                        return Err(Error::ExponentOverflow(d3.sign));
                    }
                    d3.e += 1;
                } else {
                    // rounding did not caused additional significant digit, but addition itself did.
                    Self::shift_right(&mut d3.m, 1);
                }
                d3.m[DECIMAL_PARTS - 1] += DECIMAL_BASE as i16 / 10;
                d3.n = DECIMAL_POSITIONS as i16;
            } else {
                d3.n = Self::num_digits(&d3.m);
            }
        }
        Ok(d3)
    }

    fn abs_add(d1: &[i16], d2: &[i16], d3: &mut [i16]) -> u32 {
        let mut s: u32;
        let mut c: u32 = 0;

        let mut i: usize = 0;
        while i < DECIMAL_PARTS {
            s = d1[i] as u32 + d2[i] as u32 + c;
            if s >= DECIMAL_BASE as u32 {
                s -= DECIMAL_BASE as u32;
                c = 1;
            } else {
                c = 0;
            }
            d3[i] = s as i16;
            i += 1;
        }
        c
    }

    // subtract absolute value of d2 from d1
    // d1 is supposed to be > d2
    fn abs_sub(d1: &[i16], d2: &[i16], d3: &mut [i16]) {
        let mut c: i16 = 0;
        let mut i: usize = 0;
        while i < DECIMAL_PARTS {
            if d1[i] < d2[i] + c {
                d3[i] = d1[i] + DECIMAL_BASE as i16 - d2[i] - c;
                c = 1;
            } else {
                d3[i] = d1[i] - d2[i] - c;
                c = 0;
            }
            i += 1;
        }
        assert!(0 == c);
    }
}
