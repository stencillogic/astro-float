/// Utility functions.

use crate::defs::BigFloat;
use crate::defs::Error;
use crate::defs::DECIMAL_BASE_LOG10;
use crate::defs::DECIMAL_POSITIONS;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_PARTS;
use crate::increased::BigFloatInc;

impl BigFloat {

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
    pub(super) fn shift_left(m: &mut [i16], mut n: usize) {
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
    pub(super) fn num_digits(m: &[i16]) -> i16 {
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

    // Convert to BigFloatInc.
    pub(super) fn to_big_float_inc(d1: &BigFloat) -> BigFloatInc {
        let mut ret = BigFloatInc::new();
        (&mut ret.m[0..DECIMAL_PARTS]).copy_from_slice(&d1.m);
        ret.n = d1.n;
        ret.e = d1.e;
        ret.sign = d1.sign;
        ret
    }

    // Convert from BigFloatInc.
    pub(super) fn from_big_float_inc(d1: &mut BigFloatInc) -> Result<BigFloat, Error> {
        let mut ret = BigFloat::new();
        d1.maximize_mantissa();
        d1.round()?;
        (&mut ret.m).copy_from_slice(&d1.m[1..]);
        ret.n = if d1.n > DECIMAL_PARTS as i16 { d1.n - DECIMAL_BASE_LOG10 as i16 } else { 0 };
        ret.e = d1.e + DECIMAL_BASE_LOG10 as i8;
        ret.sign = d1.sign;
        Ok(ret)
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
    pub(super) fn get_trig_params(x: &mut BigFloatInc, add: i32) -> (usize, BigFloatInc) {
        x.maximize_mantissa();
        let mut i = add - (x.n as i32 + x.e as i32);
        let mut idx = 0;
        let mut dx = *x;

        // x = s + dx
        if i < DECIMAL_BASE_LOG10 as i32 {
            idx = x.m[DECIMAL_PARTS] as usize;
            let mut m = 1;
            while i > 0 {
                idx /= 10;
                i -= 1;
                m *= 10;
            }
            dx.m[DECIMAL_PARTS] = x.m[DECIMAL_PARTS] % m;
        }
        (idx, dx)
    }
}

