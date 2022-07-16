/// Multiplication and division.

use crate::defs::BigFloatNum;
use crate::defs::Error;

impl BigFloatNum {

    /// Multiply by d2 and return result of multiplication.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    pub fn mul(&self, d2: &Self) -> Result<Self, Error> {
        let n = Self::to_big_float_inc(self);
        let m = Self::to_big_float_inc(d2);
        let ret = n.mul(&m)?;
        Self::from_big_float_inc(ret)
    }

    /// Divide by d2 and return result of division.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big.
    /// DivisionByZero - in case of d2 equal to zero.
    /// InvalidArgument - in case both d1 and self are zeroes.
    pub fn div(&self, d2: &Self) -> Result<Self, Error> {
        let n = Self::to_big_float_inc(self);
        let m = Self::to_big_float_inc(d2);
        let ret = n.div(&m)?;
        Self::from_big_float_inc(ret)
    }
}


#[cfg(test)]
mod tests {

    use crate::defs::ONE;
    use crate::defs::DECIMAL_PARTS;
    use crate::defs::DECIMAL_POSITIONS;
    use crate::defs::DECIMAL_BASE;
    use crate::defs::DECIMAL_SIGN_POS;
    use crate::defs::DECIMAL_SIGN_NEG;
    use crate::defs::DECIMAL_MIN_EXPONENT;
    use crate::defs::DECIMAL_MAX_EXPONENT;

    use super::*;

    #[test]
    fn test_mul() {

        let mut d1;
        let mut d2;
        let mut d3: BigFloatNum; 
        let mut ref_num;

        // 0 * 0
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 99 0000 * 0
        d1.m[1] = 99;
        d1.n = 6;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 * 1234 9999
        d2.m[0] = 9999;
        d2.m[1] = 1234;
        d2.n = 8;
        d1.m[0] = 0;
        d1.m[1] = 0;
        d1.n = 0;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * 1
        d1.m[1] = 0;
        d2.m[1] = 0;
        d2.m[0] = 1;
        d1.m[0] = 1;
        ref_num.m[0] = 1;
        d1.n = 1;
        d2.n = 1;
        ref_num.n = 1;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * -1
        d2.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_NEG;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // -1 * 1
        d2.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_NEG;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // -1 * -1
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_POS;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 9999 * 9999
        d2.m[0] = 9999;
        d1.m[0] = 9999;
        d1.n = 4;
        d2.n = 4;
        ref_num.m[0] = 1;
        ref_num.m[1] = 9998;
        ref_num.n = 8;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 2 0000 9999 * 9999
        d1.m[2] = 2;
        d1.n = 9;
        ref_num.m[0] = 1;
        ref_num.m[1] = 9998;
        ref_num.m[2] = 9998;
        ref_num.m[3] = 1;
        ref_num.n = 13;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 2 0000 9999 * 5000 0000 9999
        d2.m[2] = 5000;
        d2.n = 12;
        ref_num.m[0] = 1;
        ref_num.m[1] = 9998;
        ref_num.m[2] = 4998;
        ref_num.m[3] = 5001;
        ref_num.m[4] = 0;
        ref_num.m[5] = 1;
        ref_num.n = 21;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // exponent modificaton and overflows
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();

        // 5000..0 * 2
        d1.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 2;
        d1.n = DECIMAL_POSITIONS as i16;
        d2.m[0] = 2;
        d2.n = 1;
        ref_num.m[DECIMAL_PARTS - 1] = DECIMAL_BASE as i16 / 10;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = 1;
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // overflow
        d2.e = 123;
        d1.e = DECIMAL_MAX_EXPONENT - d2.e;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));

        // no overflow
        d1.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/2-1;
        assert!(d1.mul(&d2).is_ok());

        // no overflow with negative e
        d1.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/2;
        d2.e = -123;
        d1.e = DECIMAL_MIN_EXPONENT + 122;  // d1.e + d2.e = min_exp - 1
        assert!(d1.mul(&d2).is_ok());

        // overflow
        d2.e = 123;
        d1.e = DECIMAL_MAX_EXPONENT - d2.e;
        d2.m[0] = 0;
        d1.m[DECIMAL_PARTS-1] = 0;
        d1.m[5] = 1;
        d2.m[5] = 1;
        d1.n = 21;
        d2.n = 21;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));

        // no overflow
        d1.m[5] = 0;
        d1.m[0] = 9999;
        d1.m[1] = 9999;
        d1.m[2] = 9999;
        d1.m[3] = 9999;
        d1.m[4] = 9999;
        d1.n = 20;
        assert!(d1.mul(&d2).is_ok());

        // overflow
        for i in 0..DECIMAL_PARTS {
            d1.m[i] = 9999;
            d2.m[i] = 9999;
        }
        d1.n = DECIMAL_POSITIONS as i16;
        d2.n = DECIMAL_POSITIONS as i16;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));


        // overflow with negative e: 0.0
        d1 = ONE;
        d1.e = DECIMAL_MIN_EXPONENT;
        d2 = ONE;
        d2.e = DECIMAL_MIN_EXPONENT+49;
        assert!(d1.mul(&d2).unwrap().n == 0);

        // minimum positive value (subnormal)
        d2.e = DECIMAL_MIN_EXPONENT+50;
        assert!(d1.mul(&d2).unwrap().n == 1);
        //
        // division
        //


        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();

        // 0 / 0
        assert!(d1.div(&d2).unwrap_err() == Error::InvalidArgument);

        // d2 / 0
        d2.m[0] = 1;
        d2.n = 1;
        assert!(d2.div(&d1).unwrap_err() == Error::DivisionByZero);

        // 0 / d2
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d2.sign = DECIMAL_SIGN_NEG;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // division by single digit
        // 9998 / 3
        ref_num.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;
        d2.m[0] = 3;
        d2.n = 1;
        d1.m[0] = 9998;
        d1.n = 4;
        ref_num.m[0] = 6667;
        for i in 1..DECIMAL_PARTS-1 {
            ref_num.m[i] = 6666;
        }
        ref_num.m[DECIMAL_PARTS - 1] = 3332;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = -36;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1998 / 3
        ref_num.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;
        d2.m[0] = 3;
        d2.n = 1;
        d1.m[0] = 1998;
        d1.n = 1;
        for i in 0..DECIMAL_PARTS-1 {
            ref_num.m[i] = 0;
        }
        ref_num.m[DECIMAL_PARTS - 1] = 666;
        ref_num.n = DECIMAL_POSITIONS as i16 - 1;
        ref_num.e = -36;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 91998 / 33
        d1.m[1] = 9;
        d1.n = 5;
        d2.m[0] = 33;
        d2.n = 1;
        ref_num.m[0] = 8182;
        for i in 1..DECIMAL_PARTS-1 {
            ref_num.m[i] = 8181;
        }
        ref_num.m[DECIMAL_PARTS - 1] = 2787;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = -36;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 9999 9..9 9999 / 3
        for i in 0..DECIMAL_PARTS {
            d1.m[i] = 9999;
            ref_num.m[i] = 3333;
        }
        ref_num.e = 0;
        d1.n = DECIMAL_POSITIONS as i16;
        ref_num.n = DECIMAL_POSITIONS as i16;
        d2.m[0] = 3;
        d2.n = 1;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 3333 3..3 3333 / 9999
        for i in 0..DECIMAL_PARTS {
            d1.m[i] = 3333;
            ref_num.m[i] = if i%3 == 1 { 0 } else if i%3 == 2 { 6667 } else { 3333 };
        }
        d2.m[0] = 9999;
        d2.n = 4;
        ref_num.e = -4;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // signs again but with non zero quotinent
        ref_num.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        ref_num.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_POS;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_POS;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);


        // division by divisor with two or more digits
        d1 = BigFloatNum::new();
        d2 = BigFloatNum::new();
        ref_num = BigFloatNum::new();

        // 1111 9999 9999 9999 / 3333 3333
        d1.m[3] = 1111;
        d1.m[2] = 9999;
        d1.m[1] = 9999;
        d1.m[0] = 9999;
        d1.n = 16;
        d2.m[1] = 3333;
        d2.m[0] = 3333;
        d2.n = 8;
        for i in 0..DECIMAL_PARTS-2 {
            ref_num.m[i] = if i % 2 > 0 { 3335 } else { 9997 };
        }
        ref_num.m[DECIMAL_PARTS - 2] = 0;
        ref_num.m[DECIMAL_PARTS - 1] = 3336;
        ref_num.n = DECIMAL_POSITIONS as i16;
        ref_num.e = -32;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 9999 9999. 9999 9999 / 3333 3333
        ref_num.sign = DECIMAL_SIGN_POS;
        d1.sign = DECIMAL_SIGN_POS;
        d2.sign = DECIMAL_SIGN_POS;
        d1.e = -8;
        d2.e = 0;
        d1.m[3] = 9999;
        d1.m[2] = 9999;
        d1.m[1] = 9999;
        d1.m[0] = 9999;
        d1.n = 16;
        d2.m[1] = 3333;
        d2.m[0] = 3333;
        d2.n = 8;
        ref_num.m.iter_mut().for_each(|x| *x = 0);
        ref_num.m[DECIMAL_PARTS - 1] = 3;
        ref_num.m[DECIMAL_PARTS - 3] = 3;
        ref_num.m[DECIMAL_PARTS - 2] = 0;
        ref_num.n = 37;
        ref_num.e = -36;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 9999 9999. 9999 9999 / 6666 6666
        ref_num.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_POS;
        d2.m[1] = 6666;
        d2.m[0] = 6666;
        ref_num.m[DECIMAL_PARTS-1] = 1;
        ref_num.m[DECIMAL_PARTS-3] = 1;
        ref_num.m[DECIMAL_PARTS-2] = 5000;
        ref_num.m[DECIMAL_PARTS-4] = 5000;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 6666 6665 / 6666 6666
        ref_num.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_POS;
        d1.m[3] = 0;
        d1.m[2] = 0;
        d1.m[0] = 6665;
        d1.m[1] = 6666;
        d2.m[1] = 6666;
        d2.m[0] = 6666;
        d1.e = DECIMAL_MAX_EXPONENT;
        d2.e = DECIMAL_MAX_EXPONENT;
        d1.n = 8;
        d2.n = 8;
        for i in 0..DECIMAL_PARTS - 1 {
            ref_num.m[i] = if i % 2 == 0 { 9998 } else { 4999 };
        }
        ref_num.m[0] = 9999;
        ref_num.m[DECIMAL_PARTS - 1] = 9999;
        ref_num.n = 40;
        ref_num.e = -40;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // special cases for 100% coverage of Knuth's div
        d1.sign = DECIMAL_SIGN_NEG;
        d2.sign = DECIMAL_SIGN_NEG;
        ref_num.sign = DECIMAL_SIGN_POS;
        d1.e = DECIMAL_MIN_EXPONENT;
        d2.e = DECIMAL_MIN_EXPONENT;
        d1.m[4] = 6666;
        d1.m[3] = 6666;
        d1.m[2] = 0;
        d1.m[1] = 0;
        d1.m[0] = 0;
        d1.n = 20;
        d2.m[2] = 6666;
        d2.m[1] = 6666;
        d2.m[0] = 9999;
        d2.n = 12;
        ref_num.m[9] = 9999;
        ref_num.m[8] = 9998;
        ref_num.m[7] = 5001;
        ref_num.m[6] = 5000;
        ref_num.m[5] = 7497;
        ref_num.m[4] = 1;
        ref_num.m[3] = 8752;
        ref_num.m[2] = 6244;
        ref_num.m[1] = 5626;
        ref_num.m[0] = 5007;
        ref_num.n = 40;
        ref_num.e = -32;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        d1.m[4] = 0;
        d1.m[3] = 0;
        d1.m[2] = 4999;
        d1.m[1] = 9997;
        d1.m[0] = 0;
        d1.n = 12;
        d1.e = -4;
        d2.m[2] = 0;
        d2.m[1] = 5003;
        d2.m[0] = 9999;
        d2.n = 8;
        d2.e = 3;
        ref_num.m[9] = 9992;
        ref_num.m[8] = 59;
        ref_num.m[7] = 9504;
        ref_num.m[6] = 4084;
        ref_num.m[5] = 6331;
        ref_num.m[4] = 7515;
        ref_num.m[3] = 2541;
        ref_num.m[2] = 4698;
        ref_num.m[1] = 7492;
        ref_num.m[0] = 9454;
        ref_num.n = 40;
        ref_num.e = -43;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // subnormal
        d2.e = -35;
        d1.e = DECIMAL_MIN_EXPONENT;
        assert!(d1.div(&d2).unwrap().n == 39);

        // zero
        d2.e = -35+39;
        d1.e = DECIMAL_MIN_EXPONENT;
        assert!(d1.div(&d2).unwrap().n == 0);

        // overflow
        d2.e = -37;
        d1.e = DECIMAL_MAX_EXPONENT;
        assert!(d1.div(&d2).unwrap_err() == Error::ExponentOverflow(DECIMAL_SIGN_POS));
    }
}
