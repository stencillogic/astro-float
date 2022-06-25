/// BigFloatNumber definition and basic arithmetic, comparison, and number manipulation operations.

use std::mem::size_of;

/// Number of "digits" in mantissa.
const NUM_DIGITS: usize = 10;

/// Maximum exponent value.
const EXPONENT_MAX: Exponent = Exponent::MAX;

/// Minimum exponent value.
const EXPONENT_MIN: Exponent = Exponent::MIN;

/// Maximum value of a "digit".
const DIGIT_MAX: Digit = Digit::MAX;

/// Base of digits.
const DIGIT_BASE: DoubleDigit = DIGIT_MAX as DoubleDigit + 1;

/// Size of a "digit" in bits.
const DIGIT_BIT_SIZE: usize = size_of::<Digit>() * 8;

/// Length of mantissa in bits.
const NUM_BIT_LEN: usize = NUM_DIGITS*DIGIT_BIT_SIZE;

const DIGIT_SIGNIFICANT_BIT: Digit = DIGIT_MAX << (DIGIT_BIT_SIZE - 1);
const ZEROED_MANTISSA: [Digit; NUM_DIGITS] = [0; NUM_DIGITS];
const ONED_MANTISSA: [Digit; NUM_DIGITS] = [DIGIT_MAX; NUM_DIGITS];
const MIN_MANTISSA: [Digit; NUM_DIGITS] = {
    let mut m = ZEROED_MANTISSA;
    m[0] = 1;
    m
};
const ONE_MANTISSA: [Digit; NUM_DIGITS] = {
    let mut m = ZEROED_MANTISSA;
    m[NUM_DIGITS - 1] = (DIGIT_BASE >> 1) as Digit;
    m
};

/// Maximum value.
const MAX: BigFloatNumber = BigFloatNumber {
    e: EXPONENT_MAX,
    s: Sign::Pos,
    m: Mantissa { m:ONED_MANTISSA, n: DIGIT_BIT_SIZE*NUM_DIGITS },
};

/// Minimum value.
const MIN: BigFloatNumber = BigFloatNumber {
    e: EXPONENT_MAX,
    s: Sign::Neg,
    m: Mantissa { m:ONED_MANTISSA, n: DIGIT_BIT_SIZE*NUM_DIGITS },
};

/// Minimum positive value (subnormal).
const MIN_POSITIVE: BigFloatNumber = BigFloatNumber {
    e: EXPONENT_MIN,
    s: Sign::Pos,
    m: Mantissa { m:MIN_MANTISSA, n: 1 },
};

/// Value of 1.
const ONE: BigFloatNumber = BigFloatNumber {
    e: 1,
    s: Sign::Pos,
    m: Mantissa { m:ONE_MANTISSA, n: DIGIT_BIT_SIZE*NUM_DIGITS },
};

/// BigFloatNumber represents floating point number with mantissa of a fixed size, and exponent.
#[derive(Copy, Clone, Debug)]
pub struct BigFloatNumber {
    e: Exponent,
    s: Sign,
    m: Mantissa,
}

pub type Digit = u16;
pub type Exponent = i16;
type DoubleDigit = u32;
type DigitSigned = i32;
type DoubleExponent = i32;

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Sign {
    Neg = -1,
    Pos = 1,
}

impl Sign {
    pub fn invert(&self) -> Self {
        match *self {
            Sign::Pos => Sign::Neg,
            Sign::Neg => Sign::Pos,
        }
    }
}

/// Possible errors.
#[derive(Eq, PartialEq, Debug)]
pub enum Error {
    /// Exponent value becomes greater than the upper bound for exponent value.
    ExponentOverflow,

    /// Divizor is zero.
    DivisionByZero,

    /// Invalid argument
    InvalidArgument,
}


/// Mantissa representation.
#[derive(Copy, Clone, Debug)]
struct Mantissa {
    m: [Digit; NUM_DIGITS],
    n: usize,   // number of bits, 0 is for number 0
}

impl Mantissa {

    /// New mantissa with length of `len` bits filled with zeroes.
    fn new () -> Self {
        Mantissa {
            m: ZEROED_MANTISSA,
            n: 0,
        }
    }

    /// Return true if mantissa represents zero.
    fn is_zero(&self) -> bool {
        self.n == 0
    }

    /// Shift right by n bits.
    fn shift_right(&mut self, n: usize) {
        let idx = n / DIGIT_BIT_SIZE;
        let shift = n % DIGIT_BIT_SIZE;
        let mut d;
        if idx >= NUM_DIGITS {
            self.m.fill(0);
        } else if shift > 0 {
            for i in 0..self.m.len() {
                d = 0;
                if idx + i + 1 < self.m.len() {
                    d = self.m[idx + i + 1] as DoubleDigit;
                    d <<= DIGIT_BIT_SIZE;
                }
                if i + idx < self.m.len() {
                    d |= self.m[idx + i] as DoubleDigit;    
                }
                d >>= shift;
                self.m[i] = d as Digit;
            }
        } else if idx > 0 {
            for i in 0..NUM_DIGITS {
                self.m[i] = if i + idx < NUM_DIGITS {
                    self.m[i + idx]
                } else {
                    0
                }
            }
        }
    }

    /// Shift left by n bits.
    fn shift_left(m: &mut [Digit], n: usize) {
        let idx = n / DIGIT_BIT_SIZE;
        let shift = n % DIGIT_BIT_SIZE;
        let mut d;
        if idx >= NUM_DIGITS {
            m.fill(0);
        } else if shift > 0 {
            let mut i = m.len() - 1;
            loop {
                d = 0;
                if i >= idx {
                    d = m[i - idx] as DoubleDigit;
                    d <<= DIGIT_BIT_SIZE;
                }
                if i > idx {
                    d |= m[i - idx - 1] as DoubleDigit;    
                }
                d >>= DIGIT_BIT_SIZE - shift;
                m[i] = d as Digit;
                if i == 0 {
                    break;
                }
                i -= 1;
            }
        } else if idx > 0 {
            let mut i = m.len() - 1;
            loop {
                m[i] = if i >= idx {
                    m[i - idx]
                } else {
                    0
                };
                if i == 0 {
                    break;
                }
                i -= 1;
            }
        }
    }

    /// Shift to the left, returns exponent shift as positive value.
    fn maximize(m: &mut [Digit]) -> Exponent {
        let mut i = m.len() as isize - 1;
        let mut shift = 0;
        while i >= 0 {
            if m[i as usize] != 0 {
                break;
            }
            shift += (DIGIT_BIT_SIZE) as Exponent;
            i -= 1;
        }
        let mut d = m[i as usize];
        while DIGIT_SIGNIFICANT_BIT & d == 0 {
            d <<= 1;
            shift += 1;
        }
        Self::shift_left(m, shift as usize);
        shift
    }

    /// Compare to m2 and return positive is self > m2, negative if self < m2, 0 otherwise.
    fn abs_cmp(&self, m2: &Self) -> DigitSigned {
        let len = self.m.len();
        for i in 1..len+1 {
            let diff = self.m[len - i] as DigitSigned - m2.m[len - i] as DigitSigned;
            if diff != 0 {
                return diff;
            }
        }
        0
    }

    /// Subtracts m2 from self.
    fn abs_sub(&self, m2: &Self) -> (Exponent, Mantissa) {
        let mut c: DoubleDigit = 0;
        let mut i: usize = 0;
        let mut m3 = Mantissa::new();
        while i < self.m.len() {
            if (self.m[i] as DoubleDigit) < m2.m[i] as DoubleDigit + c {
                m3.m[i] = (self.m[i] as DoubleDigit + DIGIT_BASE - m2.m[i] as DoubleDigit - c) as Digit;
                c = 1;
            } else {
                m3.m[i] = self.m[i] - m2.m[i] - c as Digit;
                c = 0;
            }
            i += 1;
        }
        assert!(c == 0);
        let e = Self::maximize(&mut m3.m);
        m3.n = NUM_BIT_LEN;
        (e, m3)
    }

    /// Returns carry flag, and self + m2.
    fn abs_add(&self, m2: &Self) -> (bool, Mantissa) {
        let mut c = 0;
        let mut i: usize = 0;
        let mut m3 = Mantissa::new();
        while i < self.m.len() {
            let mut s = self.m[i] as DoubleDigit + m2.m[i] as DoubleDigit + c;
            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }
            m3.m[i] = s as Digit;
            i += 1;
        }
        if c > 0 {
            m3.shift_right(1);
            m3.m[m3.m.len()-1] |= DIGIT_SIGNIFICANT_BIT;
        }
        m3.n = NUM_BIT_LEN;
        (c > 0, m3)
    }

    /// Multiply two mantissas, return result and exponent shift as positive value.
    fn mul(&self, m2: &Self) -> (Exponent, Self) {
        let mut m3: [Digit; NUM_DIGITS*2] = [0; NUM_DIGITS*2];

        for i in 0..self.m.len() {
            let d1mi = self.m[i] as DoubleDigit;
            if d1mi == 0 {
                continue;
            }

            let mut k = 0;
            let mut j = 0;
            while j < self.m.len() {
                let m = d1mi * (m2.m[j] as DoubleDigit) + m3[i + j] as DoubleDigit + k;

                m3[i + j] = m as Digit;
                k = m >> (DIGIT_BIT_SIZE);
                j += 1;
            }
            m3[i + j] += k as Digit;
        }
        // TODO: since leading digit is always >= 0x8000 (most significant bit is set),
        // then shift is always = 1
        let mut shift = Self::maximize(&mut m3);
        let mut truncated = ZEROED_MANTISSA;
        truncated.copy_from_slice(&m3[NUM_DIGITS..]);
        let ret = Mantissa {
            m: truncated, 
            n: NUM_BIT_LEN
        };
        (shift, ret)
    }

    /// Divide mantissa by mantissa, return result and exponent ajustment.
    fn div(&self, m2: &Mantissa) -> Mantissa {
        // Knuth's division
        let mut d3 = Self::new();
        let mut c: DoubleDigit;
        let mut j: isize;
        let mut qh: DoubleDigit;
        let mut k: DoubleDigit;
        let mut rh: DoubleDigit;
        let mut buf = [0; NUM_DIGITS * 3 + 4];
        let n1: usize = 2 + NUM_DIGITS;
        let n2: usize = NUM_DIGITS * 2 + 3;
        let mut n1j: usize;
        let n = NUM_DIGITS as isize - 1;
        let m = NUM_DIGITS as isize - 1;
        let mut i = NUM_DIGITS as isize - 1;

        // normalize: n1 = d1 * d, n2 = d2 * d
        let d = DIGIT_BASE / (m2.m[n as usize] as DoubleDigit + 1); // factor d: d * m2[most significant] is close to DIGIT_MAX

        if d == 1 {
            buf[n1..(self.m.len() + n1)].clone_from_slice(&self.m[..]);
            buf[n2..(m2.m.len() + n2)].clone_from_slice(&m2.m[..]);
        } else {
            Self::mul_by_digit(&self.m, d, &mut buf[n1..]);
            Self::mul_by_digit(&m2.m, d, &mut buf[n2..]);
        }

        let v1 = buf[n2 + n as usize] as DoubleDigit;
        let v2 = buf[n2 + n as usize - 1] as DoubleDigit;

        j = m - n;
        loop {
            n1j = (n1 as isize + j) as usize;
            qh = buf[n1j + n as usize + 1] as DoubleDigit * DIGIT_BASE
                + buf[n1j + n as usize] as DoubleDigit;
            rh = qh % v1;
            qh /= v1;

            if qh >= DIGIT_BASE
                || (qh * v2 > DIGIT_BASE * rh + buf[n1j + n as usize - 1] as DoubleDigit)
            {
                qh -= 1;
                rh += v1;
                if rh < DIGIT_BASE {
                    if qh >= DIGIT_BASE
                        || (qh * v2
                            > DIGIT_BASE * rh + buf[n1j + n as usize - 1] as DoubleDigit)
                    {
                        qh -= 1;
                    }
                }
            }

            // n1_j = n1_j - n2 * qh
            c = 0;
            k = 0;
            for l in 0..n + 2 {
                k = buf[n2 + l as usize] as DoubleDigit * qh + k / DIGIT_BASE;
                let val = k % DIGIT_BASE + c;
                if (buf[n1j + l as usize] as DoubleDigit) < val {
                    buf[n1j + l as usize] += (DIGIT_BASE - val) as Digit;
                    c = 1;
                } else {
                    buf[n1j + l as usize] -= val as Digit;
                    c = 0;
                }
            }

            if c > 0 {
                // compensate
                qh -= 1;
                c = 0;
                for l in 0..n + 2 {
                    let mut val = buf[n1j + l as usize] as DoubleDigit;
                    val += buf[n2 + l as usize] as DoubleDigit + c;
                    if val >= DIGIT_BASE {
                        val -= DIGIT_BASE;
                        c = 1;
                    } else {
                        c = 0;
                    }
                    buf[n1j + l as usize] = val as Digit;
                }
                assert!(c > 0);
            }

            if i < NUM_DIGITS as isize - 1 || qh > 0 {
                d3.m[i as usize] = qh as Digit;
                i -= 1;
            }
            j -= 1;
            if i < 0 || n1 as isize + j < 0 {
                break;
            }
        }
        let _ = Self::maximize(&mut d3.m);
        d3.n = NUM_BIT_LEN;
        d3
    }

    // Multiply d1 by digit d and put result to d3 with overflow.
    fn mul_by_digit(d1: &[Digit], d: DoubleDigit, d3: &mut [Digit]) {
        let mut m: DoubleDigit = 0;
        for i in 0..NUM_DIGITS {
            m = d1[i] as DoubleDigit * d + m / DIGIT_BASE;
            d3[i] = (m % DIGIT_BASE) as Digit;
        }
        d3[NUM_DIGITS] = (m / DIGIT_BASE) as Digit;
    }

    fn from_u64(mut u: u64) -> (Exponent, Self) {
        let mut m = ZEROED_MANTISSA;
        let nd = size_of::<u64>()/size_of::<Digit>();
        for i in NUM_DIGITS - nd..NUM_DIGITS {
            m[i] = u as Digit;
            u >>= DIGIT_BIT_SIZE;
        }
        let shift = Self::maximize(&mut m);
        let ret = Mantissa {
            m,
            n: NUM_BIT_LEN,
        };
        (shift, ret)
    }

    fn to_u64(&self) -> u64 {
        let mut ret: u64 = 0;
        let nd = size_of::<u64>()/size_of::<Digit>();
        ret |= self.m[NUM_DIGITS - 1] as u64;
        for i in 1..nd {
            ret <<= DIGIT_BIT_SIZE;
            ret |= self.m[NUM_DIGITS - i - 1] as u64;
        }
        ret
    }

    fn is_subnormal(&self)-> bool {
        self.n < NUM_BIT_LEN
    }

    /// Shift to the left and return shift value.
    fn normilize(&self) -> (usize, Mantissa) {
        let shift = NUM_BIT_LEN - self.n;
        let mut m = *self;
        if shift > 0 {
            Self::shift_left(&mut m.m, shift);
            m.n = NUM_BIT_LEN;
        }
        (shift, m)
    }

    /// Set n bits to 0 from the right.
    fn mask_bits(&mut self, mut n: usize) {
        for i in 0..NUM_DIGITS {
            if n >= DIGIT_BIT_SIZE {
                self.m[i] = 0;
                n -= DIGIT_BIT_SIZE;
            } else {
                let mask = DIGIT_MAX << n;
                self.m[i] &= mask;
            }
        }
    }
}


/// Basic functions on a number.
impl BigFloatNumber {

    /// Returns new number with value of 0.
    pub fn new() -> Self {
        BigFloatNumber {
            m: Mantissa::new(),
            e: 0,
            s: Sign::Pos,
        }
    }

    /// Summation operation.
    pub fn add(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, 1)
    }

    /// Negation operation.
    pub fn neg(&self) -> Self {
        let mut ret = *self;
        ret.s = ret.s.invert();
        ret
    }

    /// Subtraction operation.
    pub fn sub(&self, d2: &Self) -> Result<Self, Error> {
        self.add_sub(d2, -1)
    }

    /// Multiplication operation.
    pub fn mul(&self, d2: &Self) -> Result<Self, Error> {
        if self.m.is_zero() || d2.m.is_zero() {
            return Ok(Self::new());
        }

        let (e1, m1_normalized) = self.normalized();
        let (e2, m2_normalized) = d2.normalized();

        let (e_shift, mut m3) = m1_normalized.mul(&m2_normalized);

        let mut e = e1 + e2 - e_shift as DoubleExponent;
        if e > EXPONENT_MAX as DoubleExponent {
            return Err(Error::ExponentOverflow);
        }

        if e < EXPONENT_MIN as DoubleExponent {
            if !Self::process_subnormal(&mut m3, &mut e) {
                return Ok(Self::new());
            }
        }

        let ret = BigFloatNumber {
            m: m3,
            s: if self.s == d2.s { Sign::Pos } else {Sign::Neg},
            e: e as Exponent,
        };

        Ok(ret)
    }

    /// Return reciprocal.
    pub fn recip(&self) -> Result<Self, Error> {
        ONE.div(self)
    }

    /// division operation.
    pub fn div(&self, d2: &Self) -> Result<Self, Error> {

        if d2.m.is_zero() {
            return Err(Error::DivisionByZero);
        }

        if self.m.is_zero() {
            return Ok(Self::new()); // self / d2 = 0
        }

        let (e1, m1_normalized) = self.normalized();
        let (e2, m2_normalized) = d2.normalized();

        let mut m3 = m1_normalized.div(&m2_normalized);

        let cmp = m1_normalized.abs_cmp(&m2_normalized);
        let shift= if cmp >= 0 {
            1
        } else {
            0
        };

        let mut e = e1 - e2 + shift as DoubleExponent;

        if e > EXPONENT_MAX as DoubleExponent {
            return Err(Error::ExponentOverflow);
        }
        if e < EXPONENT_MIN as DoubleExponent {
            if !Self::process_subnormal(&mut m3, &mut e) {
                return Ok(Self::new());
            }
        }

        let ret = BigFloatNumber {
            m: m3,
            s: if self.s == d2.s { Sign::Pos } else {Sign::Neg},
            e: e as Exponent,
        };

        Ok(ret)
    }

    /// Fast division by 2.
    pub fn div_by_2(&self) -> Self {
        let mut ret = *self;
        if self.m.is_zero() {
            return ret;
        }
        if ret.e > EXPONENT_MIN {
            ret.e -= 1;
        } else {
            ret.m.shift_right(1);
            ret.m.n -= 1;
        }
        ret
    }

    /// Return normilized mantissa and exponent with corresponding shift.
    fn normalized(&self) -> (DoubleExponent, Mantissa) {
        if self.m.is_subnormal() {
            let (shift, mantissa) = self.m.normilize();
            (self.e as DoubleExponent - shift as DoubleExponent, mantissa)
        } else {
            (self.e as DoubleExponent, self.m)
        }
    }

    /// Combined add and sub operations.
    fn add_sub(&self, d2: &Self, op: i8) -> Result<Self, Error> {
        let mut d3 = Self::new();

        // one of the numbers is zero
        if self.m.is_zero() {
            if op < 0 {
                return Ok(d2.neg());
            } else {
                return Ok(*d2);
            }
        }
        if d2.m.is_zero() {
            return Ok(*self);
        }

        let (e1, mut m1) = self.normalized();
        let (e2, mut m2) = d2.normalized();

        // shift manitissa of the smaller number.
        let mut e = if e1 >= e2 {
            m2.shift_right((e1 - e2) as usize);
            e1
        } else {
            m1.shift_right((e2 - e1) as usize);
            e2
        };

        if (self.s != d2.s && op >= 0) || (op < 0 && self.s == d2.s) {
            // subtract
            let cmp = m1.abs_cmp(&m2);
            let (shift, mut m3) = if cmp > 0 {
                d3.s = self.s;
                m1.abs_sub(&m2)
            } else if cmp < 0 {
                d3.s = if op >= 0 { d2.s } else { d2.s.invert() };
                m2.abs_sub(&m1)
            } else {
                return Ok(Self::new());
            };
            e -= shift as DoubleExponent;
            if e < EXPONENT_MIN as DoubleExponent {
                if !Self::process_subnormal(&mut m3, &mut e) {
                    return Ok(Self::new());
                }
            }
            d3.e = e as Exponent;
            d3.m = m3;
        } else {
            // add
            d3.s = self.s;
            let (c, mut m3) = m1.abs_add(&m2);
            if c {
                if e == EXPONENT_MAX as DoubleExponent {
                    return Err(Error::ExponentOverflow);
                }
                e += 1;
            }
            if e < EXPONENT_MIN as DoubleExponent {
                if !Self::process_subnormal(&mut m3, &mut e) {
                    return Ok(Self::new());
                }
            }
            d3.e = e as Exponent;
            d3.m = m3;
        }
        Ok(d3)
    }

    /// If exponent is too small try to present number in subnormal form.
    /// If sucessful return true.
    fn process_subnormal(m3: &mut Mantissa, e: &mut DoubleExponent) -> bool {
        if ((NUM_BIT_LEN) as DoubleExponent) + *e > EXPONENT_MIN as DoubleExponent {
            // subnormal
            let shift = EXPONENT_MIN as DoubleExponent - *e;
            m3.shift_right(shift as usize);
            m3.n = ((NUM_BIT_LEN) as DoubleExponent - shift) as usize;
            *e = EXPONENT_MIN as DoubleExponent;
            true
        } else {
            false
        }
    }

    /// Compare to d2.
    /// Returns positive if self > d2, negative if self < d2, 0 otherwise.
    pub fn cmp(&self, d2: &Self) -> i32 {
        if self.s != d2.s {
            return self.s as i32;
        }

        if self.m.is_zero() || d2.m.is_zero() {
            if !d2.m.is_zero() {
                return d2.s.invert() as i32;
            } else if !self.m.is_zero() {
                return self.s as i32;
            } else {
                return 0;
            }
        }

        let e: DoubleExponent = self.e as DoubleExponent - d2.e as DoubleExponent;
        if e > 0 {
            return 1*self.s as i32;
        }
        if e < 0 {
            return -1*self.s as i32;
        }

        self.m.abs_cmp(&d2.m) as i32 * self.s as i32
    }

    /// Return absolute value of a number.
    pub fn abs(&self) -> Self {
        let mut ret = *self;
        ret.s = Sign::Pos;
        ret
    }

    /// Construct from f64.
    pub fn from_f64(mut f: f64) -> Result<Self, Error> {
        let mut ret = BigFloatNumber::new();
        if f == 0.0f64 {
            return Ok(ret);
        }
        if f.is_infinite() {
            return Err(Error::ExponentOverflow)
        }
        if f.is_nan() {
            return Err(Error::InvalidArgument);
        }
        if f < 0.0f64 {
            ret.s = Sign::Neg;
            f = -f;
        }

        let p: * const f64 = &f;
        let u = unsafe {*(p as *const u64)};
        let mut mantissa = u << 12;
        let mut exponent: Exponent = (u >> 52) as Exponent & 0b11111111111;

        if exponent != 0 {
            mantissa >>= 1;
            mantissa |= 0x8000000000000000u64;
            exponent += 1;
        }

        let (shift, m) = Mantissa::from_u64(mantissa);

        ret.m = m;
        ret.e = exponent - 0b1111111111 - shift;

        Ok(ret)
    }

    /// Convert to f64.
    pub fn to_f64(&self) -> f64 {
        if self.m.is_zero() {
            return 0.0;
        }
        let mantissa = self.m.to_u64();
        let mut e: DoubleExponent = self.e as DoubleExponent + 0b1111111111;
        let mut ret = 0;
        if e >= 0b11111111111 {
            match self.s {
                Sign::Pos => f64::INFINITY,
                Sign::Neg => f64::NEG_INFINITY,
            }
        } else if e <= 0 {
            let shift = -e;
            if shift < 52 {
                ret |= mantissa >> (shift + 12);
                if self.s == Sign::Neg {
                    ret |= 0x8000000000000000u64;
                }
                let p: * const u64 = &ret;
                unsafe { *(p as * const f64) }
            } else {
                0.0
            }
        } else {
            let mantissa = mantissa << 1;
            e -= 1;
            if self.s == Sign::Neg {
                ret |= 1;
            }
            ret <<= 11;
            ret |= e as u64;
            ret <<= 52;
            ret |= mantissa >> 12;
            let p: * const u64 = &ret;
            unsafe { *(p as * const f64) }
        }
    }

    /// Construct from f32.
    pub fn from_f32(f: f32) -> Result<Self, Error> {
        Self::from_f64(f as f64)
    }

    /// Convert to f32.
    pub fn to_f32(&self) -> f32 {
        self.to_f64() as f32
    }

    /// Return true if number is subnormal.
    pub fn is_subnormal(&self) -> bool {
        self.m.is_subnormal()
    }

    /// Decompose to raw parts.
    pub fn to_raw_parts(&self) -> ([Digit; NUM_DIGITS], usize, Sign, Exponent) {
        (self.m.m, self.m.n, self.s, self.e)
    }

    /// Construct from raw parts.
    pub fn from_raw_parts(m: [Digit; NUM_DIGITS], n: usize, s: Sign, e: Exponent) -> Self {
        BigFloatNumber { e, s, m: Mantissa { m, n } }
    }

    /// Returns sign of a number.
    pub fn get_sign(&self) -> Sign {
        self.s
    }

    /// Returns true if number is positive.
    pub fn is_positive(&self) -> bool {
        self.s == Sign::Pos
    }

    /// Returns true if number is negative.
    pub fn is_negative(&self) -> bool {
        self.s == Sign::Neg
    }

    /// Returns exponent of a number.
    pub fn get_exponent(&self) -> Exponent {
        self.e
    }

    // Return true if number is zero.
    pub fn is_zero(&self) -> bool {
        self.m.is_zero()
    }

    /// Returns the largest integer less than or equal to a number.
    pub fn floor(&self) -> Result<Self, Error> {
        let int = self.int();
        if self.is_negative() {
            if !self.fract().m.is_zero() {
                return int.sub(&ONE);
            }
        }
        Ok(int)
    }

    /// Returns the smallest integer greater than or equal to a number.
    pub fn ceil(&self) -> Result<Self, Error> {
        let int = self.int();
        if self.is_positive() {
            if !self.fract().m.is_zero() {
                return int.add(&ONE);
            }
        }
        Ok(int)
    }

    /// Return fractional part of a number.
    pub fn fract(&self) -> Self {
        let mut ret = *self;
        if self.e > 0 {
            if (self.e as usize) < NUM_BIT_LEN {
                // remove integer part of mantissa & normalize at the same time
                Mantissa::shift_left(&mut ret.m.m, self.e as usize);
                if ret.m.m == ZEROED_MANTISSA {
                    return Self::new();
                }
                ret.e = 0;
            } else {
                return Self::new();
            }
        }
        ret
    }

    /// Return integer part of a number.
    pub fn int(&self) -> Self {
        let mut ret = *self;
        if self.e > 0 {
            if (self.e as usize) < NUM_BIT_LEN {
                ret.m.mask_bits(NUM_BIT_LEN - self.e as usize)
            }
            return ret;
        }
        Self::new()
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use rand::random;

    #[test]
    fn test_number() {

        let mut d1;
        let mut d2;
        let mut d3;
        let mut ref_num;

        // inf
        assert!(BigFloatNumber::from_f64(f64::INFINITY).unwrap_err() == Error::ExponentOverflow);
        assert!(BigFloatNumber::from_f64(f64::NEG_INFINITY).unwrap_err() == Error::ExponentOverflow);

        // nan
        assert!(BigFloatNumber::from_f64(f64::NAN).unwrap_err() == Error::InvalidArgument);

        // 0.0
        assert!(BigFloatNumber::from_f64(0.0).unwrap().to_f64() == 0.0);

        d1 = BigFloatNumber::from_f64(5e-324).unwrap();
        d1.to_f64();

        // conversions
        for _ in 0..10000 {
            let f: f64 = random_f64();
            if f.is_finite() {
                d1 = BigFloatNumber::from_f64(f).unwrap();
                assert!(d1.to_f64() == f);
                d1 = BigFloatNumber::from_f32(f as f32).unwrap();
                assert!(d1.to_f32() == f as f32);
            }
        }

        // 0 * 0
        d1 = BigFloatNumber::new();
        d2 = BigFloatNumber::new();
        ref_num = BigFloatNumber::new();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0.99 * 0
        d1 = BigFloatNumber::from_f64(0.99).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 * 12349999
        d1 = BigFloatNumber::new();
        d2 = BigFloatNumber::from_f64(12349999.0).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 1 * 1
        d1 = BigFloatNumber::from_f64(1.0).unwrap();
        d2 = BigFloatNumber::from_f64(1.0).unwrap();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&d1) == 0);

        // 1 * -1
        d1 = BigFloatNumber::from_f64(1.0).unwrap();
        d2 = BigFloatNumber::from_f64(1.0).unwrap().neg();
        d3 = d1.mul(&d2).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * 1
        d3 = d2.mul(&d1).unwrap();
        assert!(d3.cmp(&d2) == 0);

        // -1 * -1
        d1 = d1.neg();
        d3 = d1.mul(&d2).unwrap();
        ref_num = BigFloatNumber::from_f64(1.0).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / 0 
        d1 = BigFloatNumber::new();
        d2 = BigFloatNumber::new();
        assert!(d1.div(&d2).unwrap_err() == Error::DivisionByZero);

        // d2 / 0
        d2 = BigFloatNumber::from_f64(123.0).unwrap();
        assert!(d2.div(&d1).unwrap_err() == Error::DivisionByZero);

        // 0 / d2
        d3 = d1.div(&d2).unwrap();
        ref_num = BigFloatNumber::new();
        assert!(d3.cmp(&ref_num) == 0);

        // 0 / -d2
        d2 = d2.neg();
        d3 = d1.div(&d2).unwrap();
        assert!(d3.cmp(&ref_num) == 0);

        // add & sub & cmp
        for _ in 0..10000 {
            // avoid subnormal numbers
            let f1 = random_f64_exp(50, 25);
            let f2 = random_f64_exp(50, 25);
            if f1.is_finite() && f2.is_finite() {
                let f3 = f1 + f2;
                let f4 = f1 - f2;
                d1 = BigFloatNumber::from_f64(f1).unwrap();
                d2 = BigFloatNumber::from_f64(f2).unwrap();
                if f3 == 0.0 {
                    assert!(d1.add(&d2).unwrap().to_f64().abs() <= f64::EPSILON);
                } else {
                    assert!((d1.add(&d2).unwrap().to_f64() / f3 - 1.0).abs() <= f64::EPSILON);
                }
                if f4 == 0.0 {
                    assert!(d1.sub(&d2).unwrap().to_f64().abs() <= f64::EPSILON);
                } else {
                    assert!((d1.sub(&d2).unwrap().to_f64() / f4 - 1.0).abs() <= f64::EPSILON);
                }
                if f1 > f2 {
                    assert!(d1.cmp(&d2) > 0);
                } else if f1 < f2 {
                    assert!(d1.cmp(&d2) < 0);
                } else {
                    assert!(d1.cmp(&d2) == 0);
                }
            }
        }

        // mul & div
        for _ in 0..10000 {
            // avoid subnormal numbers
            let f1 = random_f64_exp(100, 50);
            let f2 = random_f64_exp(100, 50);
            if f1.is_finite() && f2.is_finite() && f2 != 0.0 {
                let f3 = f1*f2;
                let f4 = f1/f2;
                d1 = BigFloatNumber::from_f64(f1).unwrap();
                d2 = BigFloatNumber::from_f64(f2).unwrap();
                assert!((d1.mul(&d2).unwrap().to_f64() / f3 - 1.0).abs() <= f64::EPSILON);
                assert!((d1.div(&d2).unwrap().to_f64() / f4 - 1.0).abs() <= f64::EPSILON);
            }
        }

        // reciprocal
        let f1 = random_f64_exp(50, 25);
        d1 = BigFloatNumber::from_f64(f1).unwrap();
        assert!((d1.recip().unwrap().to_f64() * f1 - 1.0).abs() <= f64::EPSILON);

        // subnormal numbers
        d1 = MIN_POSITIVE;
        d2 = MIN_POSITIVE;
        ref_num = MIN_POSITIVE;
        ref_num.m.m[0] = 2;
        ref_num.m.n = 2;

        // min_positive + min_positive = 2*min_positive
        assert!(d1.add(&d2).unwrap().cmp(&ref_num) == 0);
        assert!(d1.add(&d2).unwrap().cmp(&d1) > 0);
        assert!(d1.cmp(&d1.add(&d2).unwrap()) < 0);

        // min_positive - min_positive = 0
        ref_num = BigFloatNumber::new();
        assert!(d1.sub(&d2).unwrap().cmp(&ref_num) == 0);

        // 1 * min_positive = min_positive
        assert!(ONE.mul(&d2).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&ONE).unwrap().cmp(&d2) == 0);

        // min_positive / 1 = min_positive
        assert!(d2.div(&ONE).unwrap().cmp(&d2) == 0);

        // normal -> subnormal -> normal
        d1 = ONE;
        d1.e = EXPONENT_MIN;
        d2 = MIN_POSITIVE;
        assert!(!d1.is_subnormal());
        assert!(d1.sub(&d2).unwrap().cmp(&d1) < 0);
        assert!(d1.cmp(&d1.sub(&d2).unwrap()) > 0);
        d1 = d1.sub(&d2).unwrap();
        assert!(d1.is_subnormal());
        d1 = d1.add(&d2).unwrap();
        assert!(!d1.is_subnormal());

        // overflow
        d1 = ONE;
        d1.e = EXPONENT_MAX - (NUM_BIT_LEN - 1) as Exponent;
        assert!(MAX.add(&d1).unwrap_err() == Error::ExponentOverflow);
        assert!(MIN.sub(&d1).unwrap_err() == Error::ExponentOverflow);
        assert!(MAX.mul(&MAX).unwrap_err() == Error::ExponentOverflow);
        d1 = ONE;
        d1.e = EXPONENT_MIN;
        assert!(MAX.div(&d1).unwrap_err() == Error::ExponentOverflow);

        // decompose and compose
        let f1 = random_f64_exp(50, 25);
        d1 = BigFloatNumber::from_f64(f1).unwrap();
        let (m,n,s,e) = d1.to_raw_parts();
        d2 = BigFloatNumber::from_raw_parts(m, n, s, e);
        assert!(d1.cmp(&d2) == 0);

        // sign and exponent
        d1 = ONE;
        assert!(d1.get_sign() == Sign::Pos);
        assert!(d1.is_positive());
        d1 = d1.neg();
        assert!(d1.get_sign() == Sign::Neg);
        assert!(d1.is_negative());
        assert!(d1.get_exponent() == 1);

        // fract & int
        let f1 = 12345.6789;
        d1 = BigFloatNumber::from_f64(f1).unwrap();
        assert!(d1.fract().to_f64() == f1.fract());
        assert!(d1.int().to_f64() == (f1 as u64) as f64);

        let f1 = -0.006789;
        d1 = BigFloatNumber::from_f64(f1).unwrap();
        assert!(d1.fract().cmp(&d1) == 0);
        assert!(d1.int().is_zero());

        let f1 = -1234567890.0;
        d1 = BigFloatNumber::from_f64(f1).unwrap();
        assert!(d1.fract().is_zero());
        assert!(d1.int().cmp(&d1) == 0);

        assert!(MIN_POSITIVE.fract().cmp(&MIN_POSITIVE) == 0);
        assert!(MIN_POSITIVE.int().is_zero());

        d1 = BigFloatNumber::new();
        assert!(d1.fract().is_zero());
        assert!(d1.int().is_zero());

        // ceil & floor
        d1 = BigFloatNumber::from_f64(12.3).unwrap();
        assert!(d1.floor().unwrap().to_f64() == 12.0);
        assert!(d1.ceil().unwrap().to_f64() == 13.0);
        d1 = BigFloatNumber::from_f64(12.0).unwrap();
        assert!(d1.floor().unwrap().to_f64() == 12.0);
        assert!(d1.ceil().unwrap().to_f64() == 12.0);

        d1 = BigFloatNumber::from_f64(-12.3).unwrap();
        assert!(d1.floor().unwrap().to_f64() == -13.0);
        assert!(d1.ceil().unwrap().to_f64() == -12.0);
        d1 = BigFloatNumber::from_f64(-12.0).unwrap();
        assert!(d1.floor().unwrap().to_f64() == -12.0);
        assert!(d1.ceil().unwrap().to_f64() == -12.0);

        // abs
        d1 = BigFloatNumber::from_f64(12.3).unwrap();
        assert!(d1.abs().to_f64() == 12.3);
        d1 = BigFloatNumber::from_f64(-12.3).unwrap();
        assert!(d1.abs().to_f64() == 12.3);
    }

    fn random_f64() -> f64 {
        random_f64_exp(f64::MAX_10_EXP, f64::MIN_10_EXP)
    }

    fn random_f64_exp(max_exp: i32, min_exp: i32) -> f64 {
        let mut f: f64 = random();
        f = f.powi(random::<i32>().abs() % max_exp - min_exp);
        if random::<i8>() & 1 == 0 {
            f = -f;
        }
        f
    }
}
