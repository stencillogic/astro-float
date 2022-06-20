/// Multiplication and division.

use crate::defs::BigFloat;
use crate::defs::Error;
use crate::defs::DECIMAL_PARTS;
use crate::defs::DECIMAL_BASE_LOG10;
use crate::defs::DECIMAL_POSITIONS;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_SIGN_NEG;
use crate::defs::DECIMAL_MIN_EXPONENT;
use crate::defs::DECIMAL_MAX_EXPONENT;

impl BigFloat {

    /// Multiply by d2 and return result of multiplication.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn mul(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        let mut d3 = Self::new();
        let mut m: i32;
        let mut k: i32;
        let mut n: i32;
        let mut nd: i32;
        let mut e: i32 = self.e as i32 + d2.e as i32;
        let mut d1mi: i32;
        let mut m3 = [0i16; DECIMAL_PARTS * 2 + 1];

        if self.n == 0 || d2.n == 0 {
            return Ok(Self::new());
        }

        for i in 0..DECIMAL_PARTS {
            d1mi = self.m[i] as i32;
            if d1mi == 0 {
                continue;
            }

            k = 0;
            let mut j = 0;
            while j < DECIMAL_PARTS {
                m = d1mi * (d2.m[j] as i32) + m3[i + j] as i32 + k;

                m3[i + j] = (m % DECIMAL_BASE as i32) as i16;
                k = m / DECIMAL_BASE as i32;
                j += 1;
            }
            m3[i + j] += k as i16;
        }

        n = Self::num_digits(&m3[DECIMAL_PARTS..]) as i32;
        if n > 0 {
            n += DECIMAL_POSITIONS as i32;
        } else {
            n = Self::num_digits(&m3) as i32;
        }

        // take care if result is not fitting in d3.m without truncating
        if n > DECIMAL_POSITIONS as i32 {
            // save as much digits as we can
            e += n - DECIMAL_POSITIONS as i32;
            nd = n % DECIMAL_BASE_LOG10 as i32;
            n = n / DECIMAL_BASE_LOG10 as i32 - DECIMAL_PARTS as i32 + 1;

            Self::shift_left(&mut m3[n as usize..], DECIMAL_BASE_LOG10 - nd as usize);

            k = 1;
            while nd > 0 {
                k *= 10;
                nd -= 1;
            }
            m3[n as usize] += m3[n as usize - 1] / k as i16;

            d3.n = DECIMAL_POSITIONS as i16;
        } else {
            d3.n = n as i16;
            n = 0;
        }

        if e > DECIMAL_MAX_EXPONENT as i32 || e < DECIMAL_MIN_EXPONENT as i32 {
            return Err(Error::ExponentOverflow);
        }

        for i in 0..d3.m.len() {
            d3.m[i] = m3[n as usize + i];
        }
        d3.e = e as i8;
        d3.sign = if self.sign == d2.sign || self.n == 0 {
            DECIMAL_SIGN_POS
        } else {
            DECIMAL_SIGN_NEG
        };

        Ok(d3)
    }

    /// Divide by d2 and return result of division.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    /// DivisionByZero - in case of d2 equal to zero.
    pub fn div(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        // Knuth's division
        let mut d3 = Self::new();
        let mut d: i32;
        let mut c: i16;
        let mut i: i32;
        let mut j: i32;
        let n: i32;
        let m: i32;
        let e: i32;
        let mut qh: i32;
        let mut k: i32;
        let mut rh: i32;
        let mut p: i32;
        let mut buf = [0i16; DECIMAL_PARTS * 3 + 4];
        let v1: i32;
        let v2: i32;
        let n1: usize = 2 + DECIMAL_PARTS;
        let n2: usize = DECIMAL_PARTS * 2 + 3;
        let mut n1j: usize;

        if d2.n == 0 {
            return Err(Error::DivisionByZero);
        }
        n = (d2.n as i32 - 1) / DECIMAL_BASE_LOG10 as i32;

        if self.n == 0 {
            return Ok(d3); // d1 / d2 = 0
        }
        m = (self.n as i32 - 1) / DECIMAL_BASE_LOG10 as i32;

        i = DECIMAL_PARTS as i32 - 1;
        p = 1;

        if n == 0 {
            // division by single digit
            d = d2.m[0] as i32;
            rh = 0;
            j = m;
            if (self.m[j as usize] as i32) < d {
                rh = self.m[j as usize] as i32;
                j -= 1;
                p -= 1;
            }

            while i >= 0 {
                qh = rh * DECIMAL_BASE as i32 + if j >= 0 { self.m[j as usize] as i32 } else { 0 };
                rh = qh % d;
                d3.m[i as usize] = (qh / d) as i16;

                if rh == 0 && j <= 0 {
                    break;
                }

                j -= 1;
                i -= 1;
            }

            while i > 0 {
                i -= 1;
                d3.m[i as usize] = 0;
            }
        } else {
            // normalize: n1 = d1 * d, n2 = d2 * d
            d = DECIMAL_BASE as i32 / (d2.m[n as usize] as i32 + 1); // factor d: d * d2[most significant] is close to DECIMAL_BASE

            if d == 1 {
                for w in 0..self.m.len() {
                    buf[n1 + w] = self.m[w];
                }
                for w in 0..d2.m.len() {
                    buf[n2 + w] = d2.m[w];
                }
            } else {
                Self::mul_by_digit(&self.m, d, &mut buf[n1..]);
                Self::mul_by_digit(&d2.m, d, &mut buf[n2..]);
            }

            v1 = buf[n2 + n as usize] as i32;
            v2 = buf[n2 + n as usize - 1] as i32;

            j = m - n;
            loop {
                n1j = (n1 as i32 + j) as usize;
                qh = buf[n1j + n as usize + 1] as i32 * DECIMAL_BASE as i32
                    + buf[n1j + n as usize] as i32;
                rh = qh % v1;
                qh /= v1;

                if qh >= DECIMAL_BASE as i32
                    || (qh * v2 > DECIMAL_BASE as i32 * rh + buf[n1j + n as usize - 1] as i32)
                {
                    qh -= 1;
                    rh += v1;
                    if rh < DECIMAL_BASE as i32 {
                        if qh >= DECIMAL_BASE as i32
                            || (qh * v2
                                > DECIMAL_BASE as i32 * rh + buf[n1j + n as usize - 1] as i32)
                        {
                            qh -= 1;
                        }
                    }
                }

                // n1_j = n1_j - n2 * qh
                c = 0;
                k = 0;
                for l in 0..n + 2 {
                    k = buf[n2 + l as usize] as i32 * qh + k / DECIMAL_BASE as i32;
                    buf[n1j + l as usize] -= (k % DECIMAL_BASE as i32) as i16 + c;
                    if buf[n1j + l as usize] < 0 {
                        buf[n1j + l as usize] += DECIMAL_BASE as i16;
                        c = 1;
                    } else {
                        c = 0;
                    }
                }

                if c > 0 {
                    // compensate
                    qh -= 1;
                    c = 0;
                    for l in 0..n + 2 {
                        buf[n1j + l as usize] += buf[n2 + l as usize] + c;
                        if buf[n1j + l as usize] >= DECIMAL_BASE as i16 {
                            buf[n1j + l as usize] -= DECIMAL_BASE as i16;
                            c = 1;
                        } else {
                            c = 0;
                        }
                    }
                    assert!(c > 0);
                }

                if i < DECIMAL_PARTS as i32 - 1 || qh > 0 {
                    d3.m[i as usize] = qh as i16;
                    i -= 1;
                } else {
                    p -= 1;
                }

                j -= 1;
                if i < 0 || n1 as i32 + j < 0 {
                    break;
                }
            }
        }

        // exponent
        j = 0;
        d = d3.m[DECIMAL_PARTS - 1] as i32;
        while d > 0 {
            d /= 10;
            j += 1;
        }

        e = self.e as i32
            - d2.e as i32
            - (DECIMAL_PARTS as i32 - m + n - p) * DECIMAL_BASE_LOG10 as i32;

        if e > DECIMAL_MAX_EXPONENT as i32 || e < DECIMAL_MIN_EXPONENT as i32 {
            return Err(Error::ExponentOverflow);
        }

        d3.e = e as i8;

        d3.n = DECIMAL_POSITIONS as i16 - DECIMAL_BASE_LOG10 as i16 + j as i16;

        d3.sign = if self.sign == d2.sign {
            DECIMAL_SIGN_POS
        } else {
            DECIMAL_SIGN_NEG
        };

        Ok(d3)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_mul() {

        let mut d1;
        let mut d2;
        let mut d3: BigFloat; 
        let mut ref_num;

        // 0 * 0
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
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
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();

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
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow);

        // no overflow
        d1.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/2-1;
        assert!(d1.mul(&d2).is_ok());

        // no overflow with negative e
        d1.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/2;
        d2.e = -123;
        d1.e = DECIMAL_MIN_EXPONENT + 122;  // d1.e + d2.e = min_exp - 1
        assert!(d1.mul(&d2).is_ok());

        // overflow with negative e
        d1.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/2-1;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow);

        // overflow
        d2.e = 123;
        d1.e = DECIMAL_MAX_EXPONENT - d2.e;
        d2.m[0] = 0;
        d1.m[DECIMAL_PARTS-1] = 0;
        d1.m[5] = 1;
        d2.m[5] = 1;
        d1.n = 21;
        d2.n = 21;
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow);

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
        assert!(d1.mul(&d2).unwrap_err() == Error::ExponentOverflow);


        //
        // division
        //


        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();

        // division by zero
        assert!(d1.div(&d2).unwrap_err() == Error::DivisionByZero);

        // 0 / d2
        d2.m[0] = 1;
        d2.n = 1;
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
        for i in 0..DECIMAL_PARTS-1 {
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
        for i in 0..DECIMAL_PARTS-1 {
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
        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();

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
        ref_num.m[0] = 5006;
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
        ref_num.m[0] = 9453;
        ref_num.n = 40;
        ref_num.e = -43;
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // overflow
        d2.e = -35;
        d1.e = DECIMAL_MIN_EXPONENT;
        assert!(d1.div(&d2).unwrap_err() == Error::ExponentOverflow);

        d2.e = -37;
        d1.e = DECIMAL_MAX_EXPONENT;
        assert!(d1.div(&d2).unwrap_err() == Error::ExponentOverflow);
    }
}
