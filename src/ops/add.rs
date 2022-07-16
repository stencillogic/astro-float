/// Addition and subtraction.

use crate::defs::BigFloatNum;
use crate::defs::Error;
use crate::defs::DECIMAL_PARTS;
use crate::defs::DECIMAL_POSITIONS;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_MAX_EXPONENT;
use crate::defs::ZEROED_MANTISSA;


impl BigFloatNum {

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
        let mut n1: BigFloatNum;
        let mut n2: BigFloatNum;

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
                if Self::round_mantissa(&mut d3.m, 1, crate::defs::RoundingMode::ToEven, true) {
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


#[cfg(test)]
mod tests {

    use crate::*;
    use defs::*;

    #[test]
    fn test_add() {

        let mut d1 = BigFloatNum::new(); 
        let mut d2 = BigFloatNum::new(); 
        let mut d3: BigFloatNum; 
        let mut ref_num = BigFloatNum::new();

        //
        // addition
        //

        d2.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        for i in 0..DECIMAL_PARTS
        {
            d1.m[i] = 9999;
            d2.m[i] = 0;
        }
        d1.m[0] = 9990;
        d2.m[0] = 10;
        d1.n = DECIMAL_POSITIONS as i16;
        d2.n = 2;
        d2.e = DECIMAL_MAX_EXPONENT;
        d1.e = DECIMAL_MAX_EXPONENT;

        assert!(d1.add(&d2).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));

        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.add(&d2).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_NEG));

        d2.e = 0;
        d1.e = 0;
        ref_num.m.iter_mut().for_each(|x| *x = 0);
        ref_num.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 10;
        ref_num.sign = DECIMAL_SIGN_NEG;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = 1;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d2.sign = DECIMAL_SIGN_POS;
        ref_num.sign = DECIMAL_SIGN_NEG;
        for i in 0..DECIMAL_PARTS {
            ref_num.m[i] = 9999;
        }
        ref_num.m[0] = 9980;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = 0;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        ref_num.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_NEG;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();
        d1.m[1] = 9999;
        d2.m[1] = 9999;
        ref_num.m[1] = 9998;
        ref_num.m[2] = 1;
        d1.n = 8;
        d2.n = 8;
        ref_num.n = 9;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 + d2
        d1.m[1] = 0;
        d1.n = 0;
        d2.e = 3;
        ref_num = d2;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // d1 + 0
        d2.m[1] = 0;
        d2.n = 0;
        d2.e = 0;
        d1.m[1] = 11;
        d1.n = 6;
        d1.e = 123;
        ref_num = d1;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // different exponents and precisions
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();

        for i in 0..DECIMAL_PARTS
        {
            d1.m[i] = 9999;
        }
        d1.n = DECIMAL_POSITIONS as i16;
        d1.e = 5;
        d2.m[0] = 11;
        d2.n = 2;
        d2.e = 3;
        ref_num = d1;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.e = 4;
        d2.m[0] = 11;
        d2.n = 2;
        d2.e = 3;
        ref_num.m.iter_mut().for_each(|x| *x = 0);
        ref_num.e = 5;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 10;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.e = 5;   // 0000 0022 2..2 2211 0000e+5 + 1122 3346e+3
        for i in 0..DECIMAL_PARTS
        {
            ref_num.m[i] = 2222;
            d1.m[i] = 2222;
        }
        d1.m[0] = 0;
        d1.m[1] = 2211;
        d1.m[DECIMAL_PARTS - 1] = 0;
        d1.m[DECIMAL_PARTS - 2] = 22;
        d1.n = DECIMAL_POSITIONS as i16 - 6;
        d2.m[0] = 3346;
        d2.m[1] = 1122;
        d2.n = 8;
        d2.e = 3;
        ref_num.e = 3;
        ref_num.m[0] = 3346;
        ref_num.m[DECIMAL_PARTS - 1] = 0;
        ref_num.n = DECIMAL_POSITIONS as i16 - 4;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.m[DECIMAL_PARTS - 1] = 222;  // 0222 2..2 2211 0000e+5 + 1122 3346e+3
        d1.m[DECIMAL_PARTS - 2] = 2222;
        d1.n = DECIMAL_POSITIONS as i16 - 1;
        ref_num.e = 4;
        ref_num.m[0] = 2334;
        ref_num.m[DECIMAL_PARTS - 1] = 2222;
        ref_num.n = DECIMAL_POSITIONS as i16;
        d3 = d1.add(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);


        //
        // subtracton
        //

        d2.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_NEG;
        for i in 0..DECIMAL_PARTS {
            d1.m[i] = 9999;
            d2.m[i] = 0;
        }
        d1.m[0] = 9990;
        d2.m[0] = 10;
        d1.n = DECIMAL_POSITIONS as i16;
        d2.n = 2;
        d1.e = DECIMAL_MAX_EXPONENT;
        d2.e = DECIMAL_MAX_EXPONENT;
        assert!(d1.sub(&d2).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_NEG));

        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_POS;
        assert!(d1.sub(&d2).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));

        d1.e -= 1;
        ref_num.m.iter_mut().for_each(|x| *x = 0);
        ref_num.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 10;
        ref_num.m[0] = 9;
        ref_num.sign = DECIMAL_SIGN_POS;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = DECIMAL_MAX_EXPONENT;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;
        d1.e += 1;
        ref_num.sign = DECIMAL_SIGN_POS;
        for i in 0..DECIMAL_PARTS {
            ref_num.m[i] = 9999;
        }
        ref_num.m[0] = 9980;
        ref_num.n = DECIMAL_POSITIONS as i16;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        ref_num.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();
        d1.m[1] = 9998;
        d1.m[2] = 1;
        d1.n = 9;
        d2.m[1] = 9999;
        d2.n = 8;
        ref_num.m[1] = 9999;
        ref_num.n = 8;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // d1 - 0
        d2.m[1] = 0;
        d2.n = 0;
        d2.e = -5;
        d1.e = 5;
        ref_num = d1;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 - d2
        d1.m[1] = 0;
        d1.m[2] = 0;
        d1.n = 0;
        d2.m[3] = 345;
        d2.n = 15;
        ref_num = d2;
        ref_num.sign = -ref_num.sign;
        d3 = d1.sub(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);
    }
}
