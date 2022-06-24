/// Power.

use crate::defs::BigFloat;
use crate::defs::Error;
use crate::defs::DECIMAL_PARTS;
use crate::defs::DECIMAL_BASE_LOG10;
use crate::defs::DECIMAL_POSITIONS;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::DECIMAL_MAX_EXPONENT_POSITIONS;
use crate::defs::ZEROED_MANTISSA;


impl BigFloat {

    /// Return BigFloat to the power of `d1`.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    ///
    /// ArgumentIsNegative - when `d1` has fractional part and `self` is negative.
    pub fn pow(&self, d1: &BigFloat) -> Result<BigFloat, Error> {
        if self.n == 0 {
            return Ok(*self);
        }

        if d1.n == 0 {
            return Ok(Self::one());
        }

        if d1.n + d1.e as i16 > DECIMAL_MAX_EXPONENT_POSITIONS {
            return Err(Error::ExponentOverflow);
        }

        // split to fractional and integer parts 
        let mut fractional = Self::new();
        let i = -(d1.e as i32);
        if i > 0 && i < (DECIMAL_POSITIONS*2) as i32 {
            fractional.m = d1.m;
            if i < DECIMAL_POSITIONS as i32 {
                Self::shift_left(&mut fractional.m, DECIMAL_POSITIONS - i as usize);
            } else if i > DECIMAL_POSITIONS as i32 {
                Self::shift_right(&mut fractional.m, i as usize - DECIMAL_POSITIONS);
            }
            fractional.n = Self::num_digits(&fractional.m);
        }
        let mut int = Self::extract_int_part(d1);

        let mut ret = Self::one();
        let one = ret;
        let mut ml = *self;
        while int.n > 0 {
            if int.m[0] & 1 != 0 {
                ret = ret.mul(&ml)?;
            }
            ml = ml.mul(&ml)?;
            Self::divide_by_two_int(&mut int);
        }
        let mut m = [0; DECIMAL_PARTS + 1];
        let mut sq = self.sqrt()?;
        let mut err = sq;
        if fractional.m != ZEROED_MANTISSA {
            loop {
                Self::mul_by_digit(&fractional.m, 2, &mut m);
                if m[DECIMAL_PARTS] != 0 {
                    ret = ret.mul(&sq)?;
                    m[DECIMAL_PARTS] = 0;
                }
                fractional.m.as_mut_slice().copy_from_slice(&m[0..DECIMAL_PARTS]);
                let sq2 = sq.sqrt()?;
                let err2 = sq.sub(&sq2)?.abs();
                if fractional.m == ZEROED_MANTISSA || err2.cmp(&err) >= 0 {
                    break;
                }
                sq = sq2;
                err = err2;
            }
        }

        if d1.sign == DECIMAL_SIGN_NEG {
            ret = one.div(&ret)?;
        }

        Ok(ret)
    }

    // divide BigFloat by two as integer
    fn divide_by_two_int(d1: &mut BigFloat) {
        d1.m[0] >>= 1;
        for i in 1..(d1.n as usize + DECIMAL_BASE_LOG10 - 1) / DECIMAL_BASE_LOG10 {
            if d1.m[i] & 1 != 0 {
                d1.m[i - 1] += DECIMAL_BASE as i16 / 2;
            }
            d1.m[i] >>= 1;
        }
        d1.n = Self::num_digits(&d1.m);
    }

}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_pow() {

        let mut d1;
        let mut d2;
        let mut ref_num;
        let one = BigFloat::one();
        let mut epsilon = BigFloat::one();
        epsilon.e = - epsilon.n as i8 + 1 - (DECIMAL_POSITIONS as i8);

        // zero number
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        d1.m[0] = 123;
        d1.n = 3;
        d1.e = -1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // zero argument
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        ref_num.m[0] = 1;
        ref_num.n = 1;
        d2.m[0] = 123;
        d2.n = 3;
        d2.e = -1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // argument is too large
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        d2.m[0] = 2;
        d2.n = 1;
        d1.m[0] = 123;
        d1.n = 3;
        d1.e = 1;
        assert!(d2.pow(&d1).unwrap_err() == Error::ExponentOverflow);

        // argument is too small
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        ref_num.m[0] = 1;
        ref_num.n = 1;
        d1.m[0] = 123;
        d1.m[1] = 123;
        d1.n = 7;
        d1.e = -47;
        d2.m[0] = 2;
        d2.n = 1;
        assert!(d2.pow(&d1).unwrap().cmp(&ref_num) == 0);

        // 2^123.4567890
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
        ref_num.m[0] = 5307;
        ref_num.m[1] = 7857;
        ref_num.m[2] = 6147;
        ref_num.m[3] = 8828;
        ref_num.m[4] = 46;
        ref_num.m[5] = 873;
        ref_num.m[6] = 5984; 
        ref_num.m[7] = 9057; 
        ref_num.m[8] = 4749; 
        ref_num.m[9] = 1459;
        ref_num.n = 40;
        ref_num.e = -2;
        d1.m[7] = 9000;
        d1.m[8] = 5678;
        d1.m[9] = 1234;
        d1.n = 40;
        d1.e = -37;
        d2.m[9] = 2000;
        d2.n = 40;
        d2.e = -39;
        epsilon.e = -39;
        let ret = d2.pow(&d1).unwrap();
        assert!(ret.sub(&ref_num).unwrap().abs().cmp(&epsilon) <= 0);

        // negative argument
        ref_num = one.div(&ref_num).unwrap();
        d1.sign = DECIMAL_SIGN_NEG;
        let ret = d2.pow(&d1).unwrap();
        assert!(ret.sub(&ref_num).unwrap().abs().cmp(&epsilon) <= 0);

        let mut ret;
        let mut inv;
        d2 = BigFloat::new();
        d2.m[0] = 4560;
        d2.m[1] = 123;
        d2.m[2] = 6789;
        d2.m[3] = 2345;
        d2.m[4] = 651;
        d2.m[5] = 41;
        d2.m[6] = 671;
        d2.m[7] = 100;
        d2.m[8] = 10;
        d2.m[9] = 9999;
        d2.n = DECIMAL_POSITIONS as i16;
        d2.e = -38;
        d1 = BigFloat::new();
        d1.m[0] = 2;
        d1.m[1] = 0;
        d1.m[2] = 0;
        d1.n = 1;
        epsilon.e = -77; // 1*10^(-38)
        d1.e = 0;
        for i in 1..100 {
            for j in 0..10 {
                d2.m[2] = i;
                d2.m[5] = i;
                d1.m[1] = j*1000;
                d1.m[2] = 10+j;
                inv = one.div(&d1).unwrap();
                ret = d2.pow(&d1).unwrap();
                ret = ret.pow(&inv).unwrap();
                assert!(d2.sub(&ret).unwrap().abs().cmp(&epsilon) <= 0);
            }
        }
    }
}
