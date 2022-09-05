//! Mantissa of a number.


use crate::defs::Word;
use crate::defs::Error;
use crate::defs::DoubleWord;
use crate::defs::SignedWord;
use crate::defs::WORD_MAX;
use crate::defs::WORD_BASE;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_SIGNIFICANT_BIT;
use crate::defs::RoundingMode;
use crate::mantissa::util::ExtendedSlice;
use crate::mantissa::util::RightShiftedSlice;
use crate::common::util::shift_slice_left;
use crate::common::util::shift_slice_right;
use crate::common::buf::WordBuf;
use crate::common::util::sub_borrow;
use crate::common::util::add_carry;
use core::mem::size_of;
use itertools::izip;



/// Mantissa representation.
#[derive(Debug)]
pub struct Mantissa {
    pub(super) m: WordBuf,
    pub(super) n: usize,   // number of bits, 0 is for number 0
}

impl Mantissa {

    // bit lenth to length in words.
    #[inline]
    fn bit_len_to_word_len(p: usize) -> usize {
        (p + WORD_BIT_SIZE - 1) / size_of::<Word>() / 8
    }

    // reserve a buffer for mantissa.
    fn reserve_new(sz: usize) -> Result<WordBuf, Error> {
        WordBuf::new(sz)
    }

    /// New mantissa with length of at least `p` bits filled with zeroes.
    pub fn new(p: usize) -> Result<Self, Error> {

        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        m.fill(0);

        Ok(Mantissa {
            m,
            n: 0,
        })
    }

    /// New mantissa with length of at least `p` bits filled with 1.
    pub fn oned_mantissa(p: usize) -> Result<Self, Error> {

        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        let n = WORD_BIT_SIZE*m.len();

        m.fill(WORD_MAX);

        Ok(Mantissa {
            m,
            n,
        })
    }

    /// New mantissa with length of at least `p` bits for the value of minimum positive value.
    pub fn min(p: usize) -> Result<Self, Error> {

        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        m.fill(0);

        m[0] = 1;

        Ok(Mantissa {
            m,
            n: 1,
        })
    }

    /// New mantissa with length of at least `p` bits for the value of 1.
    pub fn from_word(p: usize, mut d: Word) -> Result<Self, Error> {

        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        m.fill(0);

        let l = m.len();

        if d > 0 {
            while d & WORD_SIGNIFICANT_BIT == 0 {
                d <<= 1;
            }
        }

        m[l - 1] = d;

        let n = WORD_BIT_SIZE*m.len();

        Ok(Mantissa {
            m,
            n,
        })
    }

    /// Return true if mantissa represents zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.n == 0
    }

    #[inline]
    pub fn set_zero(&mut self) {
        self.n = 0;
    }

    /// Shift right by n bits.
    pub fn shift_right(&mut self, n: usize) {
        shift_slice_right(&mut self.m, n)
    }

    /// Shift self left by n digits.
    #[inline]
    pub fn shift_left(&mut self, n: usize) {
        shift_slice_left(&mut self.m, n)
    }

    /// Shift to the left, returns exponent shift as positive value.
    fn maximize(m: &mut [Word]) -> usize {

        let mut shift = 0;
        let mut d = 0;

        for v in m.iter().rev() {

            d = *v;

            if d != 0 {
                break;
            }

            shift += WORD_BIT_SIZE;
        }

        if d != 0 {

            while WORD_SIGNIFICANT_BIT & d == 0 {
                d <<= 1;
                shift += 1;
            }

            shift_slice_left(m, shift);
            shift

        } else {

            0
        }
    }

    /// Find the position of the first occurence of "1" starting from start_pos.
    pub fn find_one_from(&self, start_pos: usize) -> Option<usize> {

        let mut d;
        let start_idx = start_pos / WORD_BIT_SIZE;
        let mut shift = start_pos;

        if start_idx >= self.m.len() {

            None

        } else {
            
            let start_bit = start_pos % WORD_BIT_SIZE;

            d = self.m[self.m.len() - 1 - start_idx];
            d <<= start_bit;

            if d != 0 {

                while WORD_SIGNIFICANT_BIT & d == 0 {
                    d <<= 1;
                    shift += 1;
                }

                Some(shift)

            } else {

                shift += WORD_BIT_SIZE;
                let start_idx = start_idx + 1;

                if start_idx < self.m.len() {

                    for v in self.m.iter().rev().skip(start_idx) {

                        d = *v;

                        if d != 0 {
                            break;
                        }

                        shift += WORD_BIT_SIZE;
                    }

                    if d != 0 {

                        while WORD_SIGNIFICANT_BIT & d == 0 {
                            d <<= 1;
                            shift += 1;
                        }

                        Some(shift)

                    } else {

                        None
                    }

                } else {

                    None
                }
            }
        }
    }

    /// Compare to m2 and return positive if self > m2, negative if self < m2, 0 otherwise.
    pub fn abs_cmp(&self, m2: &Self) -> SignedWord {

        let len = self.len().min(m2.len());

        for (a, b) in core::iter::zip(self.m.iter().rev(), m2.m.iter().rev()) {
            let diff = *a as SignedWord - *b as SignedWord;
            if diff != 0 {
                return diff;
            }
        }

        for v in &self.m[..self.m.len() - len] {
            if *v != 0 {
                return 1;
            }
        }

        for v in &m2.m[..m2.m.len() - len] {
            if *v != 0 {
                return -1;
            }
        }

        0
    }

    /// Subtracts m2 from self. m2 is supposed to be shifted right by m2_shift bits.
    pub fn abs_sub(&self, m2: &Self, m2_shift: usize, rm: RoundingMode, is_positive: bool, full_prec: bool) -> Result<(usize, Self), Error> {

        // Input is expected to be normalized.
        debug_assert!(self.m[self.len() - 1] & WORD_SIGNIFICANT_BIT != 0);
        debug_assert!(m2.m[m2.len() - 1] & WORD_SIGNIFICANT_BIT != 0);

        let mut c = 0;

        let l = if full_prec {

            self.len().max(m2.len() + (m2_shift + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE)

        } else {

            self.len().max(m2.len()) + if m2_shift > 0 { 1 } else { 0 }
        };

        let mut m3 = Mantissa::new(l * WORD_BIT_SIZE)?;

        let m1iter = ExtendedSlice::new(self.m.iter(), l - self.len(), &0);
        let m2iter = RightShiftedSlice::new(&m2.m, m2_shift, 0, l - m2.len());
        let m3iter = m3.m.iter_mut();

        for (d, a, b) in izip!(m3iter, m1iter, m2iter) {
            c = sub_borrow(*a, b, c, d);
        }

        debug_assert!(c == 0);

        let mut shift = Self::maximize(&mut m3.m);

        if full_prec {

            m3.m.trunc_trailing_zeroes();

        } else if m2_shift > 0 {

            // remove guard
            if m3.round_mantissa(WORD_BIT_SIZE, rm, is_positive) {
                shift -= 1;
            }
            m3.m.trunc_to((l - 1) * WORD_BIT_SIZE);
        }

        m3.n = m3.max_bit_len();

        Ok((shift, m3))
    }

    /// Returns carry flag, and self + m2.
    pub fn abs_add(&self, m2: &Self, m2_shift: usize, rm: RoundingMode, is_positive: bool, full_prec: bool) -> Result<(bool, Self), Error> {

        debug_assert!(self.m[self.len() - 1] & WORD_SIGNIFICANT_BIT != 0);
        debug_assert!(m2.m[m2.len() - 1] & WORD_SIGNIFICANT_BIT != 0);

        let mut c = 0;

        let l = if full_prec {
            self.len().max(m2.len() + m2_shift / WORD_BIT_SIZE) + 1
        } else {
            self.len().max(m2.len()) + 1
        };

        let mut m3 = Mantissa::new(l * WORD_BIT_SIZE)?;

        if m2_shift == 0 {

            let m1iter = RightShiftedSlice::new(&self.m, 1, 0, l - self.len());
            let m2iter = RightShiftedSlice::new(&m2.m, 1, 0, l - m2.len());
            let m3iter = m3.m.iter_mut();

            for (d, a, b) in izip!(m3iter, m1iter, m2iter) {
                c = add_carry(a, b, c, d);
            }

            debug_assert!(c == 0);
            c = 1;

            if full_prec {
                m3.m.trunc_trailing_zeroes();
            } else {
                debug_assert!(!m3.round_mantissa(WORD_BIT_SIZE, rm, is_positive));
                m3.m.trunc_to((l - 1) * WORD_BIT_SIZE);
            }

        } else {

            let m1iter = ExtendedSlice::new(self.m.iter(), l - self.len(), &0);
            let m2iter = RightShiftedSlice::new(&m2.m, m2_shift, 0, l - m2.len());
            let m3iter = m3.m.iter_mut();

            for (d, a, b) in izip!(m3iter, m1iter, m2iter) {
                c = add_carry(*a, b, c, d);
            }

            if full_prec {

                if c > 0 {

                    m3.shift_right(1);

                    let l = m3.m.len();
                    m3.m[l - 1] |= WORD_SIGNIFICANT_BIT;
                }

                m3.m.trunc_trailing_zeroes();

            } else {

                if c > 0 {

                    let mut g = 0;
                    let mut n = m2_shift / WORD_BIT_SIZE;
                    if n > 0 {
                        for v in m2.m.iter().rev() {
                            if *v != 0 {
                                g = 1;
                                break;
                            }
                            n -= 1;
                            if n == 0 {
                                break;
                            }
                        }
                    }
                    m3.m[0] |= g;

                    debug_assert!(!m3.round_mantissa(WORD_BIT_SIZE + 1, rm, is_positive));  // it is not possible that rounding overflows, and c > 0 at the same time.

                    m3.shift_right(1);

                    let l = m3.m.len();
                    m3.m[l - 1] |= WORD_SIGNIFICANT_BIT;

                } else if m3.round_mantissa(WORD_BIT_SIZE, rm, is_positive) {

                    c = 1;
                }

                m3.m.trunc_to((l - 1) * WORD_BIT_SIZE);
            }
        }

        m3.n = m3.max_bit_len();

        Ok((c > 0, m3))
    }

    /// Multiply two mantissas, return result and exponent shift as positive value.
    pub fn mul(&self, m2: &Self, rm: RoundingMode, is_positive: bool, full_prec: bool) -> Result<(isize, Self), Error> {

        let mut m3 = Self::reserve_new(self.len() + m2.len())?;

        Self::mul_unbalanced(&self.m, &m2.m, &mut m3)?;

        let mut shift = Self::maximize(&mut m3) as isize;

        let mut m3 = Mantissa { m: m3, n: 0 };

        if full_prec {

            m3.m.trunc_trailing_zeroes();
            m3.n = m3.m.len() * WORD_BIT_SIZE; 

        } else {

            let l = self.len().max(m2.len()) * WORD_BIT_SIZE;

            if m3.round_mantissa(m3.m.len() * WORD_BIT_SIZE - l, rm, is_positive) {
                shift -= 1;
            }

            m3.m.trunc_to(l);
            m3.n = l;

            debug_assert!(shift >= -1 && shift <= 1);  // prevent exponent overflow
        }

        Ok((shift, m3))
    }

    /// Divide mantissa by mantissa, return result and exponent ajustment.
    pub fn div(&self, m2: &Self, rm: RoundingMode, is_positive: bool) -> Result<(isize, Self), Error> {

        let extra_p = 1;
        let l = m2.len().max(self.len());
        let k = extra_p + l - self.len() + m2.len();

        let mut m1 = Self::reserve_new(self.len() + k)?;
        m1[k..].copy_from_slice(&self.m);
        m1[..k].fill(0);

        let (q, _r) = Self::div_unbalanced(&m1, &m2.m)?;

        let n = q.len() * WORD_BIT_SIZE;
        let mut m3 = Mantissa {
            m: q,
            n,
        };

        let mut e_shift = if self.m[self.len() - 1] >= m2.m[m2.len() - 1] {
            1
        } else {
            0
        };

        let _ = Self::maximize(&mut m3.m) as isize;
        if m3.round_mantissa((extra_p + 1) * WORD_BIT_SIZE, rm, is_positive) {
            e_shift -= 1;
        }

        m3.m.trunc_to(l * WORD_BIT_SIZE);
        m3.n = m3.max_bit_len();

        debug_assert!(e_shift >= -1 && e_shift <= 1);

        Ok((e_shift, m3))
    }

    // Multiply d1 by word d and put result to d3 with overflow.
    pub(super) fn mul_by_word(d1: &[Word], d: DoubleWord, d3: &mut [Word]) {
        let mut m: DoubleWord = 0;
        for (v1, v2) in d1.iter().zip(d3.iter_mut()) {
            m = *v1 as DoubleWord * d + m / WORD_BASE;
            *v2 = (m % WORD_BASE) as Word;
        }
        d3[d1.len()] = (m / WORD_BASE) as Word;
    }

    pub fn from_u64(p: usize, mut u: u64) -> Result<(usize, Self), Error> {
        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;
        let nd = m.len() - size_of::<u64>()/size_of::<Word>();
        m[..nd].fill(0);
        for v in &mut m[nd..] {
            *v = u as Word;
            u >>= WORD_BIT_SIZE;
        }
        let shift = Self::maximize(&mut m);
        let mut ret = Mantissa {
            m,
            n: 0,
        };
        ret.n = ret.max_bit_len();
        Ok((shift, ret))
    }

    pub fn from_usize(mut u: usize) -> Result<(usize, Self), Error> {

        let mut n = 0;
        let mut v = u;

        while v & WORD_MAX as usize != 0 {
            v >>= WORD_BIT_SIZE;
            n += 1;
        }

        let mut m = Self::reserve_new(n)?;

        for v in m.iter_mut() {
            *v = u as Word;
            u >>= WORD_BIT_SIZE;
        }

        let shift = Self::maximize(&mut m);
        let mut ret = Mantissa {
            m,
            n: 0,
        };
        
        ret.n = ret.max_bit_len();

        Ok((shift, ret))
    }

    pub fn to_u64(&self) -> u64 {
        let mut ret: u64 = 0;
        let nd = size_of::<u64>()/size_of::<Word>();
        ret |= self.m[self.len() - 1] as u64;
        for i in 1..nd {
            ret <<= WORD_BIT_SIZE;
            ret |= if self.len() > i { self.m[self.len() - i - 1] as u64 } else { 0 };
        }
        ret
    }

    /// Returns true if `self` is subnormal.
    #[inline]
    pub fn is_subnormal(&self)-> bool {
        self.n < self.max_bit_len()
    }

    /// Shift to the left and return shift value.
    pub fn normilize(&self) -> Result<(usize, Self), Error> {
        let shift = self.max_bit_len() - self.n;
        let mut m = self.clone()?;
        if shift > 0 {
            shift_slice_left(&mut m.m, shift);
            m.n = self.max_bit_len();
        }
        Ok((shift, m))
    }

    /// Set n bits to 0 from the right.
    pub fn mask_bits(&mut self, mut n: usize) {
        for v in self.m.iter_mut() {
            if n >= WORD_BIT_SIZE {
                *v = 0;
                n -= WORD_BIT_SIZE;
            } else {
                let mask = WORD_MAX << n;
                *v &= mask;
            }
        }
    }

    /// Decompose to raw parts.
    pub fn to_raw_parts(&self) -> (&[Word], usize) {
        (&self.m, self.n)
    }

    /// Construct from raw parts.
    pub fn from_raw_parts(m: &[Word], n: usize) -> Result<Self, Error> {
        let mut mm = Self::reserve_new(m.len())?;
        mm.copy_from_slice(m);
        Ok(Mantissa {m: mm, n})
    }

    /// Returns true if all digits are equal to 0.
    pub fn is_all_zero(&self) -> bool {
        for v in (&self.m).iter() {
            if *v != 0 {
                return false;
            }
        }
        true
    }

    /// Decrement length by l, or set lentgh = 0, if l > length
    pub fn dec_len(&mut self, l: usize) {
        if self.n > l {
            self.n -= l;
        } else {
            self.n = 0;
        }
    }

    /// Returns length of the mantissa in words.
    #[inline]
    pub fn len(&self) -> usize {
        self.m.len()
    }

    /// Returns maximum possible length of the mantissa in digits of the mantissa's base.
    #[inline]
    pub fn max_bit_len(&self) -> usize {
        self.len()*WORD_BIT_SIZE
    }

    // Round n positons, return true if exponent is to be incremented.
    pub fn round_mantissa(&mut self, n: usize, rm: RoundingMode, is_positive: bool) -> bool {

        if rm == RoundingMode::None {
            return false;
        }

        let self_len = self.m.len();
        if n > 0 && n <= self.max_bit_len() {

            let n = n-1;
            let mut rem_zero = true;

            // anything before n'th word becomes 0
            for v in &mut self.m[..n / WORD_BIT_SIZE] {
                if *v != 0 {
                    rem_zero = false;
                }
                *v = 0;
            }

            // analyze words at n and at n+1
            // to decide if we need to add 1 or not.
            let mut c = false;
            let np1 = n + 1;
            let mut i = n / WORD_BIT_SIZE;
            let i1 = np1 / WORD_BIT_SIZE;
            let t = n % WORD_BIT_SIZE;
            let t2 = np1 % WORD_BIT_SIZE;
            let num = (self.m[i] >> t) & 1;
            if t > 0 && self.m[i] << (WORD_BIT_SIZE - t) as Word != 0 {
                rem_zero = false;
            }

            let num2 = if i1 < self_len {
                (self.m[i1] >> t2) & 1
            } else {
                0
            };

            let eq1 = num == 1 && rem_zero;
            let gt1 = num == 1 && !rem_zero;
            let gte1 = num == 1;

            match rm {
                RoundingMode::Up => if gte1 && is_positive || gt1 && !is_positive {
                    // add 1
                    c = true;
                },
                RoundingMode::Down => if gt1 && is_positive || gte1 && !is_positive {
                    // add 1
                    c = true;
                },
                RoundingMode::FromZero => if gte1 {
                    // add 1
                    c = true;
                },
                RoundingMode::ToZero => if gt1 {
                    // add 1
                    c = true;
                },
                RoundingMode::ToEven => if gt1 || (eq1 && num2 & 1 != 0) {
                    // add 1
                    c = true;
                },
                RoundingMode::ToOdd => if gt1 || (eq1 && num2 & 1 == 0) {
                    // add 1
                    c = true;
                },
                RoundingMode::None => unreachable!(),
            };

            if c {
                // add 1 at (n+1)'th position
                if i1 > i {
                    self.m[i] = 0;
                }
                i = i1;
                if i < self_len {
                    if (self.m[i] >> t2) as DoubleWord + 1 < (WORD_BASE >> t2) {
                        self.m[i] = ((self.m[i] >> t2) + 1) << t2;
                        return false;
                    } else {
                        self.m[i] = 0;
                    }
                }

                // process overflows
                i += 1;
                for v in &mut self.m[i..] {
                    if *v < WORD_MAX {
                        *v += 1;
                        return false;
                    } else {
                        *v = 0;
                    }
                    i += 1;
                }
                self.m[self_len - 1] = WORD_SIGNIFICANT_BIT;
                return true;
            } else {
                // just remove trailing words
                let t = t + 1;
                self.m[i] = if t >= WORD_BIT_SIZE { 0 } else { (self.m[i] >> t) << t };
            }
        }
        false
    }

    pub fn set_length(&mut self, p: usize) -> Result<(), Error> {
        let sz = Self::bit_len_to_word_len(p);
        let orig_len = self.m.len();
        if sz < orig_len {
            self.m.trunc_to(p);
            self.n -= (orig_len - sz)*WORD_BIT_SIZE;
        } else if sz > orig_len {
            self.m.try_extend(p)?;
            self.n += (sz - orig_len)*WORD_BIT_SIZE;
        }
        Ok(())
    }

    pub fn get_most_significant_word(&self) -> Word {
        if self.n > 0 {
            self.m[(self.n - 1) / WORD_BIT_SIZE]
        } else {
            0
        }
    }

    #[cfg(feature="random")]
    /// Returns randomized mantissa with at least p bits of length.
    pub fn random_normal(p: usize) -> Result<Self, Error> {
        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;
        for v in (&mut m).iter_mut() {
            *v = rand::random::<Word>();
        }
        let mut ret = Mantissa {
            m,
            n: 0,
        };
        if !ret.is_all_zero() {
            Self::maximize(&mut ret.m);
            ret.n = WORD_BIT_SIZE*ret.m.len();
            ret.m[0] ^= rand::random::<Word>();
        }
        Ok(ret)
    }

    /// Clones the mantissa.
    pub fn clone(&self) -> Result<Self, Error> {
        let mut m = Self::reserve_new(self.m.len())?;
        (&mut m).copy_from_slice(&self.m);
        Ok(Mantissa {
            m,
            n: self.n,
        })
    }
}
