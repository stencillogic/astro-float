//! Other operations.

use crate::defs::BigFloatNum;
use crate::defs::DECIMAL_POSITIONS;
use crate::defs::Error;
use crate::defs::DECIMAL_BASE_LOG10;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::DECIMAL_MAX_EXPONENT;
use crate::defs::RoundingMode;
use crate::defs::ZEROED_MANTISSA;

impl BigFloatNum {

    /// Return absolute value. 
    pub fn abs(&self) -> Self {
        let mut ret = *self;
        if ret.sign == DECIMAL_SIGN_NEG {
            ret.sign = DECIMAL_SIGN_POS;
        }
        ret
    }

    /// Returns the largest integer less than or equal to a number.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn floor(&self) -> Result<Self, Error> {
        self.floor_ceil(DECIMAL_SIGN_POS)
    }

    /// Returns the smallest integer greater than or equal to a number. 
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn ceil(&self) -> Result<Self, Error> {
        self.floor_ceil(DECIMAL_SIGN_NEG)
    }

    /// Return fractional part of a number,
    /// i.e. having self=12.345 it will return 0.345.
    pub fn frac(&self) -> Self {
        let mut ret = Self::extract_fract_part(self);
        ret.sign = self.sign;
        ret
    }

    /// Return integer part of a number,
    /// i.e. having self=12.345 it will return 12.0.
    pub fn int(&self) -> Self {
        let mut ret = Self::extract_int_part(self);
        if ret.n != 0 {
            ret.sign = self.sign;
        }
        ret
    }

    /// Returns the rounded number with `n` decimal positions in the fractional part of the number using rounding mode `rm`.
    pub fn round(&self, n: usize, rm: RoundingMode) -> Result<Self, Error> {
        let mut ret = *self;
        let e = (-self.e) as usize;
        if self.e < 0 && e > n {
            let m = e - n;
            if m > DECIMAL_POSITIONS {
                return Ok(Self::new());
            } else {
                if Self::round_mantissa(&mut ret.m, m as i16, rm, self.sign == DECIMAL_SIGN_POS) {
                    if ret.e == DECIMAL_MAX_EXPONENT {
                        return Err(Error::ExponentOverflow(ret.sign));
                    }
                    ret.e += 1;
                }
                if ret.m == ZEROED_MANTISSA {
                    return Ok(Self::new());
                }
            }
        }
        Ok(ret)
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

    // floor and ceil computation
    fn floor_ceil(&self, sign_check: i8) -> Result<Self, Error> {
        let mut int = Self::extract_int_part(self);
        int.sign = self.sign;
        if self.sign == sign_check {
            if self.e as i16 + self.n <= 0 {
                return Ok(Self::new());
            } else if self.e < 0 {
                return Ok(int);
            }
        } else {
            let fractional = Self::extract_fract_part(self);
            if fractional.n > 0 {
                let mut one = Self::one();
                one.sign = sign_check;
                return int.sub(&one);
            }
        }
        Ok(int)
    }
}



#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::DECIMAL_POSITIONS;
    use crate::defs::DECIMAL_PARTS;

    #[test]
    fn test_other() {
        let mut d1 = BigFloatNum::new(); 
        let mut d2 = BigFloatNum::new(); 
        let one = BigFloatNum::one();

        //
        // cmp
        //

        assert!(d1.cmp(&d2) == 0);

        d1.m[0] = 1;    // 1, 0
        d1.n = 1;
        assert!(d1.cmp(&d2) > 0);

        d2.m[0] = 2;    // 1, 2
        d2.n = 1;
        assert!(d1.cmp(&d2) < 0);

        d1.sign = DECIMAL_SIGN_NEG; // -1, 2
        assert!(d1.cmp(&d2) < 0);

        d2.sign = DECIMAL_SIGN_NEG; // -1, -2
        assert!(d1.cmp(&d2) > 0);

        d1.sign = DECIMAL_SIGN_POS; // 1, -2
        assert!(d1.cmp(&d2) > 0);

        d1.m[0] = 3;    // 3, -2
        assert!(d1.cmp(&d2) > 0);

        d2.sign = DECIMAL_SIGN_POS;    // 3, 2
        assert!(d1.cmp(&d2) > 0);

        d2.m[1] = 9;    // 3, 90002
        d2.n = 5;
        assert!(d1.cmp(&d2) < 0);

        d1.m[1] = 9;    // 90003, 90002
        d1.n = 5;
        assert!(d1.cmp(&d2) > 0);

        d2.m[0] = 3;    // 90003, 90003
        assert!(d1.cmp(&d2) == 0);

        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;    // -90003, -90003
        assert!(d1.cmp(&d2) == 0);

        //
        // abs
        //

        d1 = BigFloatNum::new();
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.abs().sign == DECIMAL_SIGN_POS);
        d1.sign = DECIMAL_SIGN_POS;
        assert!(d1.abs().sign == DECIMAL_SIGN_POS);


        //
        // ceil & floor
        //

        // 0
        d1 = BigFloatNum::new();
        assert!(d1.floor().unwrap().cmp(&d1) == 0);
        assert!(d1.ceil().unwrap().cmp(&d1) == 0);

        // positive
        d1 = BigFloatNum::new();
        d1.m[0] = 4560;
        d1.m[1] = 123;
        d1.m[2] = 6789;
        d1.m[3] = 2345;
        d1.m[4] = 651;
        d1.m[5] = 41;
        d1.m[6] = 671;
        d1.m[7] = 100;
        d1.m[8] = 10;
        d1.m[9] = 1234;
        d1.n = DECIMAL_POSITIONS as i16;
        d1.e = -38;
        d2 = BigFloatNum::new();
        d2.m[9] = 1200;
        d2.n = DECIMAL_POSITIONS as i16;
        d2.e = -38;
        assert!(d1.floor().unwrap().cmp(&d2) == 0);
        d2.m[9] = 1300;
        assert!(d1.ceil().unwrap().cmp(&d2) == 0);
        d1.e = -40;
        assert!(d1.floor().unwrap().n == 0);
        assert!(d1.ceil().unwrap().cmp(&one) == 0);
        d1 = BigFloatNum::new();
        d1.m[9] = 130;
        d1.n = DECIMAL_POSITIONS as i16-1;
        d1.e = -36;
        assert!(d1.ceil().unwrap().cmp(&d1) == 0);
        assert!(d1.floor().unwrap().cmp(&d1) == 0);

        // negative
        d1 = BigFloatNum::new();
        d1.m[8] = 10;
        d1.m[9] = 1234;
        d1.n = DECIMAL_POSITIONS as i16;
        d1.e = -38;
        d1.sign = DECIMAL_SIGN_NEG;
        d2 = BigFloatNum::new();
        d2.m[9] = 1300;
        d2.n = DECIMAL_POSITIONS as i16;
        d2.sign = DECIMAL_SIGN_NEG;
        d2.e = -38;
        assert!(d1.floor().unwrap().cmp(&d2) == 0);
        d2.m[9] = 1200;
        assert!(d1.ceil().unwrap().cmp(&d2) == 0);
        d1.e = -40;
        d2 = one;
        d2.sign = DECIMAL_SIGN_NEG;
        assert!(d1.floor().unwrap().cmp(&d2) == 0);
        assert!(d1.ceil().unwrap().n == 0);
        d1 = BigFloatNum::new();
        d1.m[9] = 130;
        d1.n = DECIMAL_POSITIONS as i16-1;
        d1.e = -36;
        d2.sign = DECIMAL_SIGN_NEG;
        assert!(d1.ceil().unwrap().cmp(&d1) == 0);
        assert!(d1.floor().unwrap().cmp(&d1) == 0);


        //
        // int & frac
        //

        // frac: no fractional
        d1 = BigFloatNum::new();
        d1.m[8] = 4567;
        d1.m[9] = 123;
        d1.n = DECIMAL_POSITIONS as i16-1;
        assert!(d1.frac().n == 0);
        d1.e = 123;
        assert!(d1.frac().n == 0);
        d1.e = -32;
        assert!(d1.frac().n == 0);

        // frac: some fractional
        d1.e = -37;
        d2 = BigFloatNum::new();
        d2.m[8] = 7000;
        d2.m[9] = 3456;
        d2.e = -40;
        d2.n = 40;
        assert!(d1.frac().cmp(&d2) == 0);

        // frac: fully fractional
        d1.e = -(d1.n as i8);
        assert!(d1.frac().cmp(&d1) == 0);
        d1.e -= 50;
        assert!(d1.frac().cmp(&d1) == 0);

        // negative
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.frac().cmp(&d1) == 0);


        // int: no fractional
        d1 = BigFloatNum::new();
        d1.m[8] = 4567;
        d1.m[9] = 123;
        d1.n = DECIMAL_POSITIONS as i16-1;
        assert!(d1.int().cmp(&d1) == 0);
        d1.e = 123;
        assert!(d1.int().cmp(&d1) == 0);
        d1.e = -32;
        assert!(d1.int().cmp(&d1) == 0);

        // negative
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.int().cmp(&d1) == 0);

        // int: some fractional
        d1.sign = DECIMAL_SIGN_POS;
        d1.e = -37;
        d2 = BigFloatNum::new();
        d2.m[9] = 1200;
        d2.e = -38;
        d2.n = 40;
        assert!(d1.int().cmp(&d2) == 0);

        // int: fully fractional
        d1.e = -(d1.n as i8);
        assert!(d1.int().n == 0);
        d1.e -= 50;
        assert!(d1.int().n == 0);


        //
        // round
        //

        // from zero
        d1 = BigFloatNum::new();
        d1.m[7] = 1250;
        d1.m[8] = 4527;
        d1.m[9] = 123;
        d1.e = -37;
        d1.n = 39;
        d2 = d1;
        assert!(d1.round(123, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        assert!(d1.round(9, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[7] = 1250;
        assert!(d1.round(8, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[7] = 1300;
        assert!(d1.round(7, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[7] = 1000;
        assert!(d1.round(6, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[7] = 0;
        assert!(d1.round(5, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 4530;
        assert!(d1.round(4, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 4500;
        assert!(d1.round(3, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        d2.m[9] = 123;
        assert!(d1.round(1, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.round(0, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d1 = BigFloatNum::new();
        d1.m[9] = 1234;
        d1.n = 39;
        d1.e = 10;
        assert!(d1.round(2, RoundingMode::FromZero).unwrap().cmp(&d1) == 0);
        d1 = BigFloatNum::new();
        d1.m[9] = 123;
        d1.e = -42;
        d1.n = 39;
        d2 = d1;
        d2.m[9] = 100;
        assert!(d1.round(4, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        d2 = BigFloatNum::new();
        assert!(d1.round(3, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);
        assert!(d1.round(2, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);

        for i in 0..DECIMAL_PARTS {
            d1.m[i] = DECIMAL_BASE as i16 - 1;
        }
        d1.n = DECIMAL_POSITIONS as i16;
        d1.e = -10;
        d2 = BigFloatNum::one();
        d2.e = -9;
        assert!(d1.round(2, RoundingMode::FromZero).unwrap().cmp(&d2) == 0);

        // toward zero
        d1 = BigFloatNum::new();
        d1.m[8] = 4550;
        d1.m[9] = 123;
        d1.e = -37;
        d1.n = 39;
        d2 = d1;
        d2.m[8] = 4550;
        assert!(d1.round(4, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 4500;
        assert!(d1.round(3, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d1.sign = DECIMAL_SIGN_NEG;
        d2 = d1;
        d2.m[8] = 4550;
        assert!(d1.round(4, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 4500;
        assert!(d1.round(3, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::ToZero).unwrap().cmp(&d2) == 0);

        // toward +inf
        d1 = BigFloatNum::new();
        d1.m[8] = 4555;
        d1.m[9] = 123;
        d1.e = -37;
        d1.n = 39;
        d2 = d1;
        d2.m[8] = 4560;
        assert!(d1.round(4, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d2.m[8] = 4600;
        assert!(d1.round(3, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d1.sign = DECIMAL_SIGN_NEG;
        d2 = d1;
        d2.m[8] = 4550;
        assert!(d1.round(4, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d2.m[8] = 4600;
        assert!(d1.round(3, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::Up).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::Up).unwrap().cmp(&d2) == 0);

        // toward -inf
        d1 = BigFloatNum::new();
        d1.m[8] = 4550;
        d1.m[9] = 123;
        d1.e = -37;
        d1.n = 39;
        d2 = d1;
        d2.m[8] = 4550;
        assert!(d1.round(4, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d2.m[8] = 4500;
        assert!(d1.round(3, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d1.sign = DECIMAL_SIGN_NEG;
        d2 = d1;
        d2.m[8] = 4550;
        assert!(d1.round(4, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d2.m[8] = 4600;
        assert!(d1.round(3, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::Down).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::Down).unwrap().cmp(&d2) == 0);

        // to even
        d1 = BigFloatNum::new();
        d1.m[8] = 4535;
        d1.m[9] = 123;
        d1.e = -37;
        d1.n = 39;
        d2 = d1;
        d2.m[8] = 4540;
        assert!(d1.round(4, RoundingMode::ToEven).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::ToEven).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::ToEven).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::ToEven).unwrap().cmp(&d2) == 0);
        d1.sign = DECIMAL_SIGN_NEG;
        d2 = d1;
        d2.m[8] = 4540;
        assert!(d1.round(4, RoundingMode::ToEven).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::ToEven).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::ToEven).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::ToEven).unwrap().cmp(&d2) == 0);

        // to odd
        d1 = BigFloatNum::new();
        d1.m[8] = 4535;
        d1.m[9] = 123;
        d1.e = -37;
        d1.n = 39;
        d2 = d1;
        d2.m[8] = 4530;
        assert!(d1.round(4, RoundingMode::ToOdd).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::ToOdd).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::ToOdd).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::ToOdd).unwrap().cmp(&d2) == 0);
        d1.sign = DECIMAL_SIGN_NEG;
        d2 = d1;
        d2.m[8] = 4530;
        assert!(d1.round(4, RoundingMode::ToOdd).unwrap().cmp(&d2) == 0);
        d2.m[8] = 5000;
        assert!(d1.round(2, RoundingMode::ToOdd).unwrap().cmp(&d2) == 0);
        d2.m[8] = 0;
        assert!(d1.round(1, RoundingMode::ToOdd).unwrap().cmp(&d2) == 0);
        d2.m[9] = 120;
        assert!(d1.round(0, RoundingMode::ToOdd).unwrap().cmp(&d2) == 0);
    }
}
