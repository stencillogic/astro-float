//! Utility functions.

use crate::inc::inc::BigFloatInc;
use crate::RoundingMode;
use crate::defs::DECIMAL_MIN_EXPONENT;
use crate::defs::DECIMAL_BASE_LOG10;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::inc::inc::DECIMAL_POSITIONS;
use crate::inc::inc::DECIMAL_PARTS;

impl BigFloatInc {

    // compare absolute values of two big floats
    // return positive if d1 > d2, negative if d1 < d2, 0 otherwise
    pub(super) fn abs_cmp(d1: &[i16], d2: &[i16]) -> i16 {
        let mut i: i32 = DECIMAL_PARTS as i32 - 1;
        while i >= 0 {
            if d1[i as usize] != d2[i as usize] {
                return d1[i as usize] - d2[i as usize];
            }
            i -= 1;
        }
        0
    }


    // shift m to the right by n digits
    pub(super) fn shift_right(m: &mut [i16], mut n: usize) {
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

    // shift m to the left by n digits
    pub(crate) fn shift_left(m: &mut [i16], mut n: usize) {
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
    pub(crate) fn num_digits(m: &[i16]) -> i16 {
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
    pub(super) fn mul_by_digit(d1: &[i16], d: i32, d3: &mut [i16]) {
        let mut m: i32 = 0;
        for i in 0..DECIMAL_PARTS {
            m = d1[i] as i32 * d + m / DECIMAL_BASE as i32;
            d3[i] = (m % DECIMAL_BASE as i32) as i16;
        }
        d3[DECIMAL_PARTS] = (m / DECIMAL_BASE as i32) as i16;
    }

    // fractional part of d1 
    pub(super) fn extract_fract_part(d1: &Self) -> Self {
        let mut fractional = Self::new();
        let e = -(d1.e as i16);
        if e >= d1.n {
            fractional = *d1;
            fractional.sign = DECIMAL_SIGN_POS;
        } else if e > 0 {
            let mut i = 0;
            while i + (DECIMAL_BASE_LOG10 as i16) <= e {
                fractional.m[i as usize / DECIMAL_BASE_LOG10] = d1.m[i as usize / DECIMAL_BASE_LOG10];
                i += DECIMAL_BASE_LOG10 as i16;
            }
            if i < e {
                let mut t = 1;
                while i < e {
                    t *= 10;
                    i += 1;
                }
                fractional.m[i as usize / DECIMAL_BASE_LOG10] += d1.m[i as usize / DECIMAL_BASE_LOG10 as usize] % t;
            }
            fractional.n = Self::num_digits(&fractional.m);
            if fractional.n > 0 {
                fractional.e = d1.e;
            }
        }
        fractional
    }

    // integer part of d1
    pub(super) fn extract_int_part(d1: &Self) -> Self {
        if d1.e >= 0 {
            return *d1;
        }
        if d1.e as i16 + d1.n < 0 {
            return Self::new();
        }
        let mut int = Self::new();
        let mut i = -(d1.e as i16);
        let mut t = Self::get_div_factor(i);
        if i < 0 {
            i = 0;
        }
        let mut t2 = 1;
        while i < d1.n {
            int.m[int.n as usize / DECIMAL_BASE_LOG10] += (d1.m[i as usize / DECIMAL_BASE_LOG10 as usize] / t % 10) * t2;
            int.n += 1;
            i += 1;
            t *= 10;
            if t == DECIMAL_BASE as i16 {
                t = 1;
            }
            t2 *= 10;
            if t2 == DECIMAL_BASE as i16 {
                t2 = 1;
            }
        }
        if int.n > 0 {
            int.e = d1.e + (i - int.n) as i8;
        }
        int
    }

    // factor to divide by to get a digit at position n
    pub(super) fn get_div_factor(n: i16) -> i16 {
        let mut x = n % DECIMAL_BASE_LOG10 as i16;
        let mut t = 1;
        while x > 0 {
            t *= 10;
            x -= 1;
        }
        t
    }

    // determine parameters for computation of trig function
    pub(super) fn get_trig_params(x: &mut BigFloatInc, add_one: i32) -> (usize, BigFloatInc) {
        x.maximize_mantissa();
        let mut i = add_one - (x.n as i32 + x.e as i32);
        let mut idx = 0;
        let mut dx = *x;

        // x = s + dx
        if i < DECIMAL_BASE_LOG10 as i32 {
            idx = x.m[DECIMAL_PARTS-1] as usize;
            let mut m = 1;
            while i > 0 {
                idx /= 10;
                i -= 1;
                m *= 10;
            }
            dx.m[DECIMAL_PARTS-1] = x.m[DECIMAL_PARTS-1] % m;
            dx.n = Self::num_digits(&dx.m);
        }
        (idx, dx)
    }


    /// If exponent is too small try to present number in subnormal form.
    /// If not successful, then return 0.0
    pub(crate) fn process_subnormal(&mut self, e: i32) -> Self {
        if (DECIMAL_POSITIONS as i32) + e > DECIMAL_MIN_EXPONENT as i32 {
            // subnormal
            let shift = (DECIMAL_MIN_EXPONENT as i32 - e) as usize;
            Self::shift_right(&mut self.m, shift);
            self.n -= shift as i16;
            self.e = DECIMAL_MIN_EXPONENT;
            *self
        } else {
            // zero
            Self::new()
        }
    }


    // Round n positons to even, return true if exponent is to be incremented.
    pub(crate) fn round_mantissa(m: &mut [i16], n: i16, rm: RoundingMode, is_positive: bool) -> bool {

        if n > 0 && n <= DECIMAL_POSITIONS as i16 {
            let n = n-1;
            // anything before n'th digit becomes 0
            for i in 0..n as usize / DECIMAL_BASE_LOG10 {
                m[i] = 0;
            }

            // analyze digits at n and at n+1
            // to decide if we need to add 1 or not.
            let mut c = false;
            let np1 = n + 1;
            let mut i = n as usize / DECIMAL_BASE_LOG10;
            let i1 = np1 as usize / DECIMAL_BASE_LOG10;
            let t = Self::get_div_factor(n);
            let t2 = Self::get_div_factor(np1);
            let num = m[i] / t % 10;

            let num2 = if i1 < m.len() {
                m[i1] / t2 % 10
            } else {
                0
            };

            match rm {
                RoundingMode::Up => if num >= 5 && is_positive || num > 5 && !is_positive {
                    // add 1
                    c = true;
                },
                RoundingMode::Down => if num > 5 && is_positive || num >= 5 && !is_positive {
                    // add 1
                    c = true;
                },
                RoundingMode::FromZero => if num >= 5 {
                    // add 1
                    c = true;
                },
                RoundingMode::ToZero => if num > 5 {
                    // add 1
                    c = true;
                },
                RoundingMode::ToEven => if num > 5 || (num == 5 && num2 & 1 != 0) {
                    // add 1
                    c = true;
                },
                RoundingMode::ToOdd => if num > 5 || (num == 5 && num2 & 1 == 0) {
                    // add 1
                    c = true;
                },
            };

            if c {
                // add 1 at (n+1)'th position
                if i1 > i {
                    m[i] = 0;
                }
                i = i1;
                if i < m.len() {
                    if m[i] / t2 + 1 < DECIMAL_BASE as i16 / t2 {
                        m[i] = (m[i] / t2 + 1) * t2;
                        return false;
                    } else {
                        m[i] = 0;
                    }
                }

                // process overflows
                i += 1;
                while i < m.len() {
                    if m[i] < DECIMAL_BASE as i16 - 1 {
                        m[i] += 1;
                        return false;
                    } else {
                        m[i] = 0;
                    }
                    i += 1;
                }
                m[m.len() - 1] = DECIMAL_BASE as i16 / 10;
                return true;
            } else {
                // just remove trailing digits
                let t = t*10;
                m[i] = (m[i] / t) * t;
            }
        }
        false
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
}

