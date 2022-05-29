//! Multiple precision floating point numbers implemented purely in Rust. 
//!
//! Characteristics:
//!
//! | Name                          | Value  |
//! |:------------------------------|-------:|
//! | Decimal positions in mantissa |     40 |
//! | Exponent minimum value        |   -128 |
//! | Exponent maximum value        |    127 |
//!
//!


const DECIMAL_PARTS: usize = 10;
const DECIMAL_BASE_LOG10: usize = 4;
const DECIMAL_POSITIONS: usize = DECIMAL_PARTS * DECIMAL_BASE_LOG10;
const DECIMAL_BASE: usize = 10000;
const DECIMAL_SIGN_POS: i8 = 1;
const DECIMAL_SIGN_NEG: i8 = -1;
const DECIMAL_MIN_EXPONENT: i8 = -128;
const DECIMAL_MAX_EXPONENT: i8 = 127;

/// Possible errors.
#[derive(Eq, PartialEq, Debug)]
pub enum Error {
    /// Exponent value becomes greater than the upper bound or smaller than the lower bound for exponent value.
    ExponentOverflow,   

    /// Divizor is zero.
    DivisionByZero,     
}

/// Number representation.
#[derive(Copy, Clone, Debug)]
pub struct BigFloat {
    sign: i8,                // sign
    e: i8,                   // exponent
    n: i16,                  // the number of decimal positions in the mantissa excluding leading zeroes
    m: [i16; DECIMAL_PARTS], // mantissa
}

impl BigFloat {

    /// Return new BigFloat with value zero.
    pub fn new() -> Self {
        return BigFloat {
            sign: DECIMAL_SIGN_POS,
            e: 0,
            n: 0,
            m: [0; DECIMAL_PARTS],
        };
    }

    /// Create a BigFloat value from a sequence of `bytes`. Each byte must represent a decimal digit.
    /// First byte is the most significant. The length of `bytes` can be any. If the length of
    /// `bytes` is greater than required, then the remaining part is ignored.
    /// If `sign` is negative, then the resulting BigFloat will be
    /// negative.
    pub fn from_bytes(bytes: &[u8], sign: i8, exponent: i8) -> BigFloat {
        let mut mantissa = [0; DECIMAL_PARTS];
        let mut n: usize = 0;
        let mut p: i16 = 1;
        let d = if bytes.len() > DECIMAL_POSITIONS { DECIMAL_POSITIONS } else { bytes.len() };
        for i in 1..d+1 {
            mantissa[n] += (bytes[d - i] % 10) as i16 * p;
            p *= 10;
            if p == DECIMAL_BASE as i16 {
                n += 1;
                p = 1;
            }
        }

        return BigFloat {
            sign: if sign >= 0 { DECIMAL_SIGN_POS } else { DECIMAL_SIGN_NEG },
            e: exponent,
            n: d as i16,
            m: mantissa,
        };
    }

    /// Get BigFloat's mantissa as bytes. Each byte represents a decimal digit.
    /// First byte is the most significant. The length of `bytes` can be any. If the length of
    /// `bytes` is smaller than required, then remaining part of mantissa will be omitted.
    ///
    /// The length of mantissa can be determined using `get_mantissa_len`.
    pub fn get_mantissa_bytes(&self, bytes: &mut [u8]) {
        let mut n: usize = 0;
        let mut p: i16 = 1;
        let d = if bytes.len() < self.n as usize { bytes.len() } else { self.n as usize };
        for i in 1..d+1 {
            bytes[d - i] = ((self.m[n] / p) % 10) as u8;
            p *= 10;
            if p == DECIMAL_BASE as i16 {
                n += 1;
                p = 1;
            }
        }
    }

    /// Return the number of decimal positions filled in the mantissa.
    pub fn get_mantissa_len(&self) -> usize {
        self.n as usize
    }

    /// Return 1 if BigFloat is positive, -1 otherwise.
    pub fn get_sign(&self) -> i8 {
        self.sign
    }

    /// Return exponent part.
    pub fn get_exponent(&self) -> i8 {
        self.e
    }


    /// Add d2 and return result of addition.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - in case of too big or too small numbers.
    pub fn add(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        return self.add_sub(d2, 1);
    }

    /// Subtract d2 and return result of subtraction.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - in case of too big or too small numbers.
    pub fn sub(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        return self.add_sub(d2, -1);
    }

    /// Multiply by d2 and return result of multiplication.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - in case of too big or too small numbers.
    pub fn mul(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        let mut d3 = BigFloat::new();
        let mut m: i32;
        let mut k: i32;
        let mut n: i32;
        let mut nd: i32;
        let mut e: i32 = self.e as i32 + d2.e as i32;
        let mut d1mi: i32;
        let mut m3 = [0i16; DECIMAL_PARTS * 2];

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
            m3[i + j] = m3[i + j] + k as i16;
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
            n = (n + DECIMAL_BASE_LOG10 as i32 - 1) / DECIMAL_BASE_LOG10 as i32
                - DECIMAL_PARTS as i32;

            Self::shift_left(&mut m3[n as usize..], DECIMAL_BASE_LOG10 - nd as usize);

            k = DECIMAL_BASE as i32;
            while nd > 0 {
                k /= 10;
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

        return Ok(d3);
    }

    /// Divide by d2 and return result of division.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - in case of too big or too small numbers.
    /// DivisionByZero - in case of d2 equal to zero.
    pub fn div(&self, d2: &BigFloat) -> Result<BigFloat, Error> {
        // Knuth's division
        let mut d3 = BigFloat::new();
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

        return Ok(d3);
    }

    /// Compare to d2.
    /// Returns positive if self > d2, negative if self < d2, 0 otherwise.
    pub fn cmp(&self, d2: &BigFloat) -> i16 {
        if self.sign != d2.sign {
            return self.sign as i16;
        }

        let diff: i32 = self.e as i32 + self.n as i32 - d2.e as i32 - d2.n as i32;

        if diff > 0 {
            return 1;
        }
        if diff < 0 {
            return -1;
        }

        if self.n != d2.n {
            return Self::abs_cmp_with_shift(&self.m, self.n, &d2.m, d2.n) * self.sign as i16;
        }

        return Self::abs_cmp(&self.m, &d2.m) * self.sign as i16;
    }

    // auxiliary functions

    // compare absolute values of two big floats
    // return positive if d1 > d2, negative if d1 < d2, 0 otherwise
    fn abs_cmp(d1: &[i16], d2: &[i16]) -> i16 {
        let mut i: i32 = DECIMAL_PARTS as i32 - 1;
        while i >= 0 {
            if d1[i as usize] != d2[i as usize] {
                return d1[i as usize] - d2[i as usize];
            }
            i -= 1;
        }
        return 0;
    }

    // compare absolute values of two floats with shifts n1, n2
    // return positive if self > d2, negative if self < d2, 0 otherwise
    fn abs_cmp_with_shift(d1: &[i16], mut n1: i16, d2: &[i16], mut n2: i16) -> i16 {
        let mut t1: i16 = DECIMAL_BASE as i16 / 10;
        let mut t2: i16 = DECIMAL_BASE as i16 / 10;
        let mut s: i16;
        let mut v1: i16;
        let mut v2: i16;

        s = n1 / DECIMAL_BASE_LOG10 as i16;
        while s > 0 {
            s -= 1;
            t1 /= 10
        }
        s = n2 / DECIMAL_BASE_LOG10 as i16;
        while s > 0 {
            s -= 1;
            t2 /= 10
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
                t1 = DECIMAL_BASE as i16 / 10
            };
            t2 /= 10;
            if t2 == 0 {
                t2 = DECIMAL_BASE as i16 / 10
            };
            n1 -= 1;
            n2 -= 1;
        }
        return 0;
    }

    // add if op >= 0 subtract if op < 0
    fn add_sub(&self, d2: &BigFloat, op: i8) -> Result<BigFloat, Error> {
        let mut d3 = BigFloat::new();
        let shift: i32;
        let free: i32;
        let mut e: i32;
        let cmp: i16;
        let mut n1: &BigFloat;
        let mut n2: &BigFloat;
        let mut s1: BigFloat;
        let mut s2: BigFloat;

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
            n1 = d2;
            n2 = self;
        } else {
            n1 = self;
            n2 = d2;
        }
        shift = n1.e as i32 - n2.e as i32;
        e = n1.e as i32;

        // bring n1 and n2 to having common exponent
        if shift > 0 {
            s1 = *n1;
            s2 = *n2;

            free = DECIMAL_POSITIONS as i32 - s1.n as i32;

            if shift > free {
                if shift - free > s2.n as i32 {
                    // n2 is too small
                    d3 = *n1;
                    return Ok(d3);
                } else {
                    if free > 0 {
                        Self::shift_left(&mut s1.m, free as usize);
                    }
                    Self::shift_right(&mut s2.m, (shift - free) as usize);
                    e -= free;
                }
            } else {
                Self::shift_left(&mut s1.m, shift as usize);
                e -= shift;
            }
            n1 = &s1;
            n2 = &s2;
        } else if shift < 0 {
            s2 = *n2;
            Self::shift_left(&mut s2.m, (-shift) as usize);
            n2 = &s2;
        }

        if (n1.sign != n2.sign && op >= 0) || (op < 0 && n1.sign == n2.sign) {
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
                d3.m.iter_mut().for_each(|x| *x = 0);
            }
        } else {
            // add
            d3.sign = self.sign;
            d3.e = e as i8;
            if Self::abs_add(&n1.m, &n2.m, &mut d3.m) > 0 {
                if e == DECIMAL_MAX_EXPONENT as i32 {
                    return Err(Error::ExponentOverflow);
                }
                d3.e += 1;
                Self::shift_right(&mut d3.m, 1);
                d3.m[DECIMAL_PARTS - 1] += DECIMAL_BASE as i16 / 10;
                d3.n = DECIMAL_POSITIONS as i16;
            } else {
                d3.n = Self::num_digits(&d3.m);
            }
        }
        return Ok(d3);
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

        return c;
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

    // shift decimal m to the right by n digits
    fn shift_right(m: &mut [i16], mut n: usize) {
        assert!(n > 0 && n <= DECIMAL_POSITIONS);

        let mut s: i16;
        let mut t: i16;
        let mut x: i32 = (n % DECIMAL_BASE_LOG10) as i32;
        n = n / DECIMAL_BASE_LOG10;
        if x == 0 {
            if n > 0 {
                for i in 0..DECIMAL_PARTS - n {
                    m[i] = m[i + n];
                }
            }
        } else {
            s = 10;
            t = DECIMAL_BASE as i16 / 10;
            x -= 1;
            while x > 0 {
                s *= 10;
                t /= 10;
                x -= 1;
            }

            let mut i = 0;
            while i < DECIMAL_PARTS - n - 1 {
                m[i] = (m[i + n + 1] % s) * t + m[i + n] / s;
                i += 1;
            }
            m[i] = m[i + n] / s;
        }
        for i in 0..n {
            m[i + DECIMAL_PARTS - n] = 0;
        }
    }

    // shift decimal m to the left by n digits
    fn shift_left(m: &mut [i16], mut n: usize) {
        assert!(n > 0 && n <= DECIMAL_POSITIONS);

        let mut i: usize;
        let mut s: i16;
        let mut t: i16;
        let mut x: i32 = (n % DECIMAL_BASE_LOG10) as i32;
        n = n / DECIMAL_BASE_LOG10;
        if x == 0 {
            if n > 0 {
                i = DECIMAL_PARTS - 1;
                while i >= n {
                    m[i] = m[i - n];
                    i -= 1;
                }
            }
        } else {
            s = 10;
            t = DECIMAL_BASE as i16 / 10;
            x -= 1;
            while x > 0 {
                s *= 10;
                t /= 10;
                x -= 1;
            }

            i = DECIMAL_PARTS - 1;
            while i > n {
                m[i] = (m[i - n] % t) * s + m[i - n - 1] / t;
                i -= 1;
            }
            m[i] = (m[i - n] % t) * s;
        }
        for k in 0..n {
            m[k] = 0;
        }
    }

    // return number of digits taken in mantissa
    fn num_digits(m: &[i16]) -> i16 {
        let mut n: i16 = DECIMAL_POSITIONS as i16;
        let mut t: i16;
        let mut p: i16 = DECIMAL_PARTS as i16 - 1;

        while p >= 0 && 0 == m[p as usize] {
            p -= 1;
            n -= DECIMAL_BASE_LOG10 as i16;
        }

        if n > 0 {
            t = m[p as usize];
            n -= DECIMAL_BASE_LOG10 as i16;
            loop {
                n += 1;
                t /= 10;
                if t == 0 {
                    break;
                }
            }
        }

        return n;
    }

    // multiply d1 by digit d and put result to d3 with overflow
    fn mul_by_digit(d1: &[i16], d: i32, d3: &mut [i16]) {
        let mut m: i32 = 0;
        for i in 0..DECIMAL_PARTS {
            m = d1[i] as i32 * d + m / DECIMAL_BASE as i32;
            d3[i] = (m % DECIMAL_BASE as i32) as i16;
        }
        d3[DECIMAL_PARTS] = (m / DECIMAL_BASE as i32) as i16;
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_bigfloat() {


        println!("Testing creation and deconstruction");

        let mut d1 = BigFloat::new(); 
        let mut d2 = BigFloat::new(); 
        let mut d3: BigFloat; 
        let mut ref_num = BigFloat::new();

        assert!(DECIMAL_PARTS >= 10);

        // regular buf
        let bytes1: [u8; 20] = [1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20];
        let expected1: [u8; 30] = [1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,0,0,0,0,0,0,0,0,0,0];
        let exp1 = 123;
        let d4 = BigFloat::from_bytes(&bytes1, 1, exp1);

        let mut mantissa_buf1 = [0; 30];
        d4.get_mantissa_bytes(&mut mantissa_buf1);
        assert!(mantissa_buf1 == expected1);
        assert!(d4.get_mantissa_len() == bytes1.len());
        assert!(d4.get_sign() == 1);
        assert!(d4.get_exponent() == exp1);

        // too long buf
        let bytes2: [u8; 45] = [1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20,1,2,3,4,5,6,7,8,9,10,11,112,13,14,15,16,17,18,19,20,21,22,3,4,5];
        let expected2: [u8; 42] = [1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9,0,0,0];
        let exp2 = -128;
        let d4 = BigFloat::from_bytes(&bytes2, -2, exp2);

        let mut mantissa_buf2 = [0; 42];
        d4.get_mantissa_bytes(&mut mantissa_buf2);
        assert!(mantissa_buf2 == expected2);
        assert!(d4.get_mantissa_len() == 40);
        assert!(d4.get_sign() == -1);
        assert!(d4.get_exponent() == exp2);


        println!("Testing comparisons");

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


        println!("Testing additions");

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

        assert!(d1.add(&d2).unwrap_err() == Error::ExponentOverflow);

        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_NEG;
        assert!(d1.add(&d2).unwrap_err() == Error::ExponentOverflow);

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

        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
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
        d1 = BigFloat::new();
        d2 = BigFloat::new();

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


        println!("Testing decimal subtraction");

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
        assert!(d1.sub(&d2).unwrap_err() == Error::ExponentOverflow);

        d2.sign = DECIMAL_SIGN_NEG;
        d1.sign = DECIMAL_SIGN_POS;
        assert!(d1.sub(&d2).unwrap_err() == Error::ExponentOverflow);

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

        d1 = BigFloat::new();
        d2 = BigFloat::new();
        ref_num = BigFloat::new();
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


        println!("Testing multiplication");

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


        println!("Testing division");

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
            ref_num.m[i] = if i%3 == 1 { 0 } else { 
                if i%3 == 2 { 6667 } else { 3333 }
            };
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
