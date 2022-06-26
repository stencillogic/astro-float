//! Increased precision float to prevent error accumulation.
use crate::defs::DECIMAL_PARTS as DECIMAL_PARTS_BASE;
use crate::defs::Error;


const DECIMAL_PARTS: usize = DECIMAL_PARTS_BASE + 1;
const DECIMAL_BASE_LOG10: usize = 4;    // number decimal positions in a digit = log10(DECIMAL_BASE)
const DECIMAL_POSITIONS: usize = DECIMAL_PARTS * DECIMAL_BASE_LOG10;
const DECIMAL_BASE: usize = 10000;      // 9999 is the maximum of a digit
const DECIMAL_SIGN_POS: i8 = 1;         // + sign
const DECIMAL_SIGN_NEG: i8 = -1;        // - sign
const DECIMAL_MIN_EXPONENT: i8 = -128;  // min exponent value
const DECIMAL_MAX_EXPONENT: i8 = 127;   // max exponent value
const ZEROED_MANTISSA: [i16; DECIMAL_PARTS] = [0; DECIMAL_PARTS];


/// BigFloat with increased precision. For internal use only.
#[derive(Copy, Clone, Debug)]
pub (crate) struct BigFloatInc {
    pub (crate) sign: i8,                // sign
    pub (crate) e: i8,                   // exponent
    pub (crate) n: i16,                  // the number of decimal positions in the mantissa excluding leading zeroes
    pub (crate) m: [i16; DECIMAL_PARTS], // mantissa
}


impl BigFloatInc {

    /// Return new BigFloatInc with value zero.
    pub fn new() -> Self {
        BigFloatInc {
            sign: DECIMAL_SIGN_POS,
            e: 0,
            n: 0,
            m: ZEROED_MANTISSA,
        }
    }

    /// Return new BigFloatInc with value one.
    pub fn one() -> Self {
        let mut val = Self::new();
        val.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/10;
        val.n = DECIMAL_POSITIONS as i16;
        val.e = 1 - DECIMAL_POSITIONS as i8;
        val
    }

    /// Return new BigFloat with value two.
    pub fn two() -> Self {
        let mut val = Self::new();
        val.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/5;
        val.n = DECIMAL_POSITIONS as i16;
        val.e = 1 - DECIMAL_POSITIONS as i8;
        val
    }

    /// Return absolute value.
    pub fn abs(&self) -> Self {
        let mut ret = *self;
        if ret.sign == DECIMAL_SIGN_NEG {
            ret.sign = DECIMAL_SIGN_POS;
        }
        ret
    }

    /// Add d2 and return result of addition.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn add(&self, d2: &BigFloatInc) -> Result<Self, Error> {
        self.add_sub(d2, 1)
    }

    /// Subtract d2 and return result of subtraction.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn sub(&self, d2: &BigFloatInc) -> Result<Self, Error> {
        self.add_sub(d2, -1)
    }

    /// Multiply by d2 and return result of multiplication.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    pub fn mul(&self, d2: &BigFloatInc) -> Result<Self, Error> {
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

        for i in 0..d3.m.len() {
            d3.m[i] = m3[n as usize + i];
        }
        d3.sign = if self.sign == d2.sign || self.n == 0 {
            DECIMAL_SIGN_POS
        } else {
            DECIMAL_SIGN_NEG
        };

        if e < DECIMAL_MIN_EXPONENT as i32 {
            return Ok(d3.process_subnormal(e));
        }

        if e > DECIMAL_MAX_EXPONENT as i32 {
            return Err(Error::ExponentOverflow(d3.sign));
        }

        d3.e = e as i8;

        Ok(d3)
    }

    /// Compare to d2.
    /// Returns positive if self > d2, negative if self < d2, 0 otherwise.
    pub fn cmp(&self, d2: &BigFloatInc) -> i16 {
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

        Self::abs_cmp(&self.m, &d2.m) * self.sign as i16
    }

    /// Divide by d2 and return result of division.
    ///
    /// # Errors
    ///
    /// ExponentOverflow - when result is too big or too small.
    /// DivisionByZero - in case of d2 equal to zero.
    pub fn div(&self, d2: &BigFloatInc) -> Result<Self, Error> {
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

        d3.sign = if self.sign == d2.sign {
            DECIMAL_SIGN_POS
        } else {
            DECIMAL_SIGN_NEG
        };

        if e < DECIMAL_MIN_EXPONENT as i32 {
            return Ok(d3.process_subnormal(e));
        }
        
        if e > DECIMAL_MAX_EXPONENT as i32 {
            return Err(Error::ExponentOverflow(d3.sign));
        }

        d3.e = e as i8;
        d3.n = DECIMAL_POSITIONS as i16 - DECIMAL_BASE_LOG10 as i16 + j as i16;

        Ok(d3)
    }

    /// Shift to the left as much as possibe.
    pub fn maximize_mantissa(&mut self) {
        if self.n < DECIMAL_POSITIONS as i16 {
            let mut shift = DECIMAL_POSITIONS - self.n as usize;
            if shift > (self.e as i32 - DECIMAL_MIN_EXPONENT as i32) as usize {
                shift = (self.e - DECIMAL_MIN_EXPONENT) as usize; 
            }
            if shift > 0 {
                Self::shift_left(&mut self.m, shift);
                self.e -= shift as i8;
                self.n += shift as i16;
            }
        }
    }

    /// Use extra digits to increase precision by rounding.
    pub fn round(&mut self) -> Result<(), Error> {
        let mut c = 0;
        let mut t = 1;
        let dd = self.m[0];
        for _ in 0..DECIMAL_BASE_LOG10 {
            let d = (dd / t) % 10 + c;
            c = if d >= 5 { 1 } else { 0 };
            t *= 10;
        }
        if c > 0 {
            for i in 1..DECIMAL_PARTS {
                if self.m[i] < DECIMAL_BASE as i16 - 1 {
                    self.m[i] += 1;
                    self.n = Self::num_digits(&self.m);
                    return Ok(());
                } else {
                    self.m[i] = 0;
                }
            }
            if self.e == DECIMAL_MAX_EXPONENT {
                return Err(Error::ExponentOverflow(self.sign));
            }
            self.e += 1;
            Self::shift_right(&mut self.m, 1);
            self.m[DECIMAL_PARTS - 1] += DECIMAL_BASE as i16 / 10;
        }
        Ok(())
    }

    /// Return fractional part of number with positive sign.
    pub fn get_fractional_part(&self) -> Self {
        let mut fractional = Self::new();
        let e = -(self.e as i16);
        if e >= self.n {
            fractional = *self;
            fractional.sign = DECIMAL_SIGN_POS;
        } else if e > 0 {
            let mut i = 0;
            while i + (DECIMAL_BASE_LOG10 as i16) <= e {
                fractional.m[i as usize / DECIMAL_BASE_LOG10] = self.m[i as usize / DECIMAL_BASE_LOG10];
                i += DECIMAL_BASE_LOG10 as i16;
            }
            if i < e {
                let mut t = 1;
                while i < e {
                    t *= 10;
                    i += 1;
                }
                fractional.m[i as usize / DECIMAL_BASE_LOG10] += self.m[i as usize / DECIMAL_BASE_LOG10 as usize] % t;
            }
            fractional.n = Self::num_digits(&fractional.m);
            if fractional.n > 0 {
                fractional.e = self.e;
            }
        }
        fractional
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
        0
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

    // add if op >= 0 subtract if op < 0
    fn add_sub(&self, d2: &BigFloatInc, op: i8) -> Result<BigFloatInc, Error> {
        let mut d3 = Self::new();
        let shift: i32;
        let free: i32;
        let mut e: i32;
        let cmp: i16;
        let mut n1: &BigFloatInc;
        let mut n2: &BigFloatInc;
        let mut s1: BigFloatInc;
        let mut s2: BigFloatInc;

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
                    return Err(Error::ExponentOverflow(d3.sign));
                }
                d3.e += 1;
                Self::shift_right(&mut d3.m, 1);
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

    // shift m to the right by n digits
    fn shift_right(m: &mut [i16], mut n: usize) {
        assert!(n > 0 && n <= DECIMAL_POSITIONS);

        let mut s: i16;
        let mut t: i16;
        let mut x: i32 = (n % DECIMAL_BASE_LOG10) as i32;
        n /= DECIMAL_BASE_LOG10;
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

    // Shift m to the left by n digits.
    fn shift_left(m: &mut [i16], mut n: usize) {
        assert!(n > 0 && n <= DECIMAL_POSITIONS);

        let mut i: usize;
        let mut s: i16;
        let mut t: i16;
        let mut x: i32 = (n % DECIMAL_BASE_LOG10) as i32;
        n /= DECIMAL_BASE_LOG10;
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
        n
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


    /// If exponent is too small try to present number in subnormal form.
    /// If not successful, then return 0.0
    fn process_subnormal(&mut self, e: i32) -> Self {
        if (DECIMAL_POSITIONS as i32) + e > DECIMAL_MIN_EXPONENT as i32 {
            // subnormal
            let shift = (DECIMAL_MIN_EXPONENT as i32 - e) as usize;
            Self::shift_right(&mut self.m, shift);
            self.n = (DECIMAL_POSITIONS - shift) as i16;
            self.e = DECIMAL_MIN_EXPONENT;
            *self
        } else {
            // zero
            Self::new()
        }
    }
}
