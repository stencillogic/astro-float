//! Mantissa of a number.

use crate::common::buf::WordBuf;
use crate::common::util::add_carry;
use crate::common::util::find_one_from;
use crate::common::util::shift_slice_left;
use crate::common::util::shift_slice_right;
use crate::common::util::sub_borrow;
use crate::defs::DoubleWord;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::defs::SignedWord;
use crate::defs::Word;
use crate::defs::WORD_BASE;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_MAX;
use crate::defs::WORD_SIGNIFICANT_BIT;
use crate::mantissa::util::ExtendedSlice;
use crate::mantissa::util::NormalizedView;
use crate::mantissa::util::RightShiftedSlice;
use core::mem::size_of;
use itertools::izip;

/// Mantissa representation.
#[derive(Debug, Hash)]
pub struct Mantissa {
    m: WordBuf,
    n: usize, // number of bits, 0 is for number 0
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

        Ok(Mantissa { m, n: 0 })
    }

    /// New mantissa with length of at least `p` bits filled with 1.
    pub fn oned_mantissa(p: usize) -> Result<Self, Error> {
        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        let n = WORD_BIT_SIZE * m.len();

        m.fill(WORD_MAX);

        Ok(Mantissa { m, n })
    }

    /// New mantissa with length of at least `p` bits for the value of minimum positive value.
    pub fn min(p: usize) -> Result<Self, Error> {
        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        m.fill(0);

        m[0] = 1;

        Ok(Mantissa { m, n: 1 })
    }

    /// New mantissa with length of at least `p` bits for the value of 1.
    pub fn from_word(p: usize, mut d: Word) -> Result<Self, Error> {
        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        if m.len() == 0 {
            return Err(Error::InvalidArgument);
        }

        m.fill(0);

        let l = m.len();

        if d > 0 {
            while d & WORD_SIGNIFICANT_BIT == 0 {
                d <<= 1;
            }
        }

        m[l - 1] = d;

        let n = WORD_BIT_SIZE * m.len();

        Ok(Mantissa { m, n })
    }

    /// New mantissa with length of at least `p` bits prefilled with `words`.
    pub fn from_words(p: usize, w: &[Word]) -> Result<Self, Error> {
        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        if m.len() < w.len() {
            return Err(Error::InvalidArgument);
        }

        let b = m.len() - w.len();
        (&mut m)[..b].fill(0);
        (&mut m)[b..].copy_from_slice(w);

        let n = Self::find_bit_len(&m);

        Ok(Mantissa { m, n })
    }

    /// Return true if mantissa represents zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.n == 0
    }

    /// Fill with zeroes, ad set bit length to 0.
    #[inline]
    pub fn set_zero(&mut self) {
        self.m.fill(0);
        self.n = 0;
    }

    #[inline]
    pub fn set_bit_len(&mut self, n: usize) {
        self.n = n;
    }

    /// Recalculate bit length.
    pub fn update_bit_len(&mut self) {
        let n = Self::find_bit_len(&self.m);
        self.n = n;
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
        find_one_from(&self.m, start_pos)
    }

    /// Compare to m2 and return positive if self > m2, negative if self < m2, 0 otherwise.
    pub fn abs_cmp(&self, m2: &Self, normalized: bool) -> SignedWord {
        let deref = |x: &Word| *x;
        let n = self.len().min(m2.len());

        if normalized {
            Self::cmp_iters(
                self.m.iter().rev().map(deref),
                m2.m.iter().rev().map(deref),
                n,
            )
        } else {
            Self::cmp_iters(
                NormalizedView::new(self.m.iter().rev().map(deref)),
                NormalizedView::new(m2.m.iter().rev().map(deref)),
                n,
            )
        }
    }

    fn cmp_iters<T>(mut iter1: T, mut iter2: T, n: usize) -> SignedWord
    where
        T: Iterator<Item = Word>,
    {
        for (a, b) in core::iter::zip(iter1.by_ref(), iter2.by_ref()).take(n) {
            let diff = a as SignedWord - b as SignedWord;
            if diff != 0 {
                return diff;
            }
        }

        for v in iter1 {
            if v != 0 {
                return 1;
            }
        }

        for v in iter2 {
            if v != 0 {
                return -1;
            }
        }

        0
    }

    /// Subtracts m2 from self. m2 is supposed to be shifted right by m2_shift bits.
    /// `inexact` is set to true if the result is not exact.
    pub fn abs_sub(
        &self,
        m2: &Self,
        p: usize,
        m2_shift: usize,
        rm: RoundingMode,
        is_positive: bool,
        full_prec: bool,
        inexact: &mut bool,
    ) -> Result<(isize, Self), Error> {
        // Input is expected to be normalized.
        debug_assert!(self.m[self.len() - 1] & WORD_SIGNIFICANT_BIT != 0);
        debug_assert!(m2.m[m2.len() - 1] & WORD_SIGNIFICANT_BIT != 0);

        let p = Self::bit_len_to_word_len(p);
        let mut c = 0;

        let l2 = (m2_shift + WORD_BIT_SIZE - 2) / WORD_BIT_SIZE;
        let mut m3 = if l2 > p && l2 > self.len() && !full_prec {
            // m2 lays outside of m1's mantissa range and outside the desired precision
            //
            // m1 1XXXX00000000   - m1 and trailing zeroes
            // m2 000000001XXXX   - m2_shift, m2

            *inexact |= true;

            let m3l = self.len().max(p) + 1;
            let mut m3 = Mantissa::new(m3l * WORD_BIT_SIZE)?;

            // subtract 1
            let m1iter = ExtendedSlice::new(self.m.iter(), m3l - self.len(), &0);
            let m3iter = m3.m.iter_mut();

            c = 1;
            for (d, &a) in izip!(m3iter, m1iter) {
                if c > 0 {
                    if a == 0 {
                        *d = WORD_MAX;
                    } else {
                        *d = a - c;
                        c = 0;
                    }
                } else {
                    *d = a;
                }
            }

            m3
        } else {
            // m2_shift is smaller than the precision of m1
            // or m2_shift is smaller than the desired precision
            //
            // m1 1XXXXXX00000   - m1 and trailing zeroes
            // m2 0000001XXXXX   - m2_shift, m2

            let l = self
                .len()
                .max((m2_shift + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE + m2.len());

            let mut m3 = Mantissa::new(l * WORD_BIT_SIZE)?;

            let m1iter = ExtendedSlice::new(self.m.iter(), l - self.len(), &0);
            let m2iter = RightShiftedSlice::new(&m2.m, m2_shift, 0, l - m2.len());
            let m3iter = m3.m.iter_mut();

            for (d, a, b) in izip!(m3iter, m1iter, m2iter) {
                c = sub_borrow(*a, b, c, d);
            }

            m3
        };

        debug_assert!(c == 0);

        let mut shift = Self::maximize(&mut m3.m) as isize;

        if full_prec {
            m3.m.trunc_trailing_zeroes();
        } else if m3.len() < p {
            let n = m3.len();
            m3.m.try_extend(p * WORD_BIT_SIZE)?;
            m3.m[..p - n].fill(0);
        } else if m3.len() > p {
            if m3.round_mantissa(
                (m3.len() - p) * WORD_BIT_SIZE,
                rm,
                is_positive,
                &mut false,
                m3.max_bit_len(),
                inexact,
            ) {
                shift -= 1;
            }
            m3.m.trunc_to(p * WORD_BIT_SIZE);
        }

        m3.n = m3.max_bit_len();

        Ok((shift, m3))
    }

    /// Returns exponent shift, and self + m2.
    pub fn abs_add(
        &self,
        m2: &Self,
        p: usize,
        m2_shift: usize,
        rm: RoundingMode,
        is_positive: bool,
        full_prec: bool,
        inexact: &mut bool,
    ) -> Result<(isize, Self), Error> {
        debug_assert!(self.m[self.len() - 1] & WORD_SIGNIFICANT_BIT != 0);
        debug_assert!(m2.m[m2.len() - 1] & WORD_SIGNIFICANT_BIT != 0);

        let p = Self::bit_len_to_word_len(p);
        let mut c = 0;

        let (mut m3, c) = if m2_shift == 0 {
            let l = self.len().max(m2.len()) + 1;

            let mut m3 = Mantissa::new(l * WORD_BIT_SIZE)?;

            let m1iter = RightShiftedSlice::new(&self.m, 1, 0, l - self.len());
            let m2iter = RightShiftedSlice::new(&m2.m, 1, 0, l - m2.len());
            let m3iter = m3.m.iter_mut();

            for (d, a, b) in izip!(m3iter, m1iter, m2iter) {
                c = add_carry(a, b, c, d);
            }

            debug_assert!(c == 0);
            c = 1;

            (m3, c)
        } else {
            let l2 = (m2_shift + WORD_BIT_SIZE - 2) / WORD_BIT_SIZE;
            if l2 > p && l2 > self.len() && !full_prec {
                // m2 lays outside of m1's mantissa range and outside the desired precision
                //
                // m1 1XXXX00000000   - m1 and trailing zeroes
                // m2 000000001XXXX   - m2_shift, m2

                *inexact |= true;

                let mut m3 = Mantissa::new((p + 1) * WORD_BIT_SIZE)?;

                if m3.len() >= self.m.len() {
                    let l = m3.len() - self.len();
                    m3.m[l..].copy_from_slice(&self.m);
                } else {
                    let l = self.len() - m3.len();
                    m3.m.copy_from_slice(&self.m[l..]);
                }

                m3.m[0] |= 1; // add sticky for rounding

                (m3, 0)
            } else {
                // m2_shift is smaller than the precision of m1
                // or m2_shift is smaller than the desired precision
                //
                // m1 1XXXXXX00000   - m1 and trailing zeroes
                // m2 0000001XXXXX   - m2_shift, m2

                let l = self
                    .len()
                    .max((m2_shift + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE + m2.len())
                    + 1;

                let mut m3 = Mantissa::new(l * WORD_BIT_SIZE)?;

                let m1iter = ExtendedSlice::new(self.m.iter(), l - self.len(), &0);
                let m2iter = RightShiftedSlice::new(&m2.m, m2_shift, 0, l - m2.len());
                let m3iter = m3.m.iter_mut();

                for (d, a, b) in izip!(m3iter, m1iter, m2iter) {
                    c = add_carry(*a, b, c, d);
                }

                if c > 0 {
                    m3.shift_right(1);
                    let l = m3.m.len();
                    m3.m[l - 1] |= WORD_SIGNIFICANT_BIT;
                }

                (m3, c)
            }
        };

        let mut shift = -(c as isize);

        if full_prec {
            m3.m.trunc_trailing_zeroes();
        } else if m3.len() < p {
            let n = m3.len();
            m3.m.try_extend(p * WORD_BIT_SIZE)?;
            m3.m[..p - n].fill(0);
        } else if m3.len() > p {
            if m3.round_mantissa(
                (m3.len() - p) * WORD_BIT_SIZE,
                rm,
                is_positive,
                &mut false,
                m3.max_bit_len(),
                inexact,
            ) {
                shift -= 1;
            }
            m3.m.trunc_to(p * WORD_BIT_SIZE);
        }

        m3.n = m3.max_bit_len();

        Ok((shift, m3))
    }

    /// Multiply two mantissas, return result, exponent shift, and inexact flag.
    pub fn mul(
        &self,
        m2: &Self,
        p: usize,
        rm: RoundingMode,
        is_positive: bool,
        full_prec: bool,
        inexact: &mut bool,
    ) -> Result<(isize, Self), Error> {
        debug_assert!(self.m[self.len() - 1] & WORD_SIGNIFICANT_BIT != 0);
        debug_assert!(m2.m[m2.len() - 1] & WORD_SIGNIFICANT_BIT != 0);

        let mut m3 = Self::reserve_new(self.len() + m2.len())?;

        Self::mul_unbalanced(&self.m, &m2.m, &mut m3)?;

        let mut shift = Self::maximize(&mut m3) as isize;

        let mut m3 = Mantissa { m: m3, n: 0 };

        let p = Self::bit_len_to_word_len(p);

        if full_prec {
            m3.m.trunc_trailing_zeroes();
        } else if m3.len() < p {
            let n = m3.len();
            m3.m.try_extend(p * WORD_BIT_SIZE)?;
            m3.m[..p - n].fill(0);
        } else if m3.len() > p {
            if m3.round_mantissa(
                (m3.len() - p) * WORD_BIT_SIZE,
                rm,
                is_positive,
                &mut false,
                m3.max_bit_len(),
                inexact,
            ) {
                shift -= 1;
            }
            m3.m.trunc_to(p * WORD_BIT_SIZE);
        }

        debug_assert!((-1..=1).contains(&shift)); // prevent exponent overflow

        m3.n = m3.max_bit_len();

        Ok((shift, m3))
    }

    /// Divide mantissa by mantissa, return result and exponent ajustment.
    pub fn div(
        &self,
        m2: &Self,
        p: usize,
        rm: RoundingMode,
        is_positive: bool,
        inexact: &mut bool,
    ) -> Result<(isize, Self), Error> {
        let p = Self::bit_len_to_word_len(p);

        let k = (p + m2.len()).max(self.len()) + 1;

        let mut e_shift = (m2.len() as isize - k as isize) * WORD_BIT_SIZE as isize;

        let mut m1 = Self::reserve_new(k)?;
        if k > self.len() {
            let l = k - self.len();
            m1[l..].copy_from_slice(&self.m);
            m1[..l].fill(0);
        } else {
            m1.copy_from_slice(&self.m);
        }

        let (q, r) = Self::div_unbalanced(&m1, &m2.m)?;

        e_shift += q.len() as isize * WORD_BIT_SIZE as isize;

        let mut m3 = Mantissa { m: q, n: 0 };

        let r_sticky = r.iter().any(|&x| x != 0);

        // rounding
        if r_sticky {
            *inexact |= true;

            if rm as u32 & 0b1100000 != 0 {
                m3.m[0] |= 1;
            } else if rm == RoundingMode::FromZero
                || (is_positive && rm == RoundingMode::Up)
                || (!is_positive && rm == RoundingMode::Down)
            {
                if m3.add_ulp() {
                    let m3l = m3.len() - 1;
                    m3.m[m3l] = WORD_SIGNIFICANT_BIT;
                    e_shift += 1;
                }
            }
        }

        e_shift -= Self::maximize(&mut m3.m) as isize;

        if m3.round_mantissa(
            (m3.len() - p) * WORD_BIT_SIZE,
            rm,
            is_positive,
            &mut false,
            m3.max_bit_len(),
            inexact,
        ) {
            e_shift += 1;
        }

        m3.m.trunc_to(p * WORD_BIT_SIZE);
        m3.n = m3.max_bit_len();

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

    /// `self` to power of `i` mod `n`
    pub fn pow_mod(&self, mut i: usize, n: &Self) -> Result<Self, Error> {
        // first non-zero bit in i
        let mut bit_pos = WORD_BIT_SIZE;

        while bit_pos > 0 {
            bit_pos -= 1;
            i <<= 1;
            if i & WORD_SIGNIFICANT_BIT as usize != 0 {
                bit_pos -= 1;
                i <<= 1;
                break;
            }
        }

        let mut x = self.clone()?;
        while bit_pos > 0 {
            bit_pos -= 1;

            x = x.mul_mod(&x, n)?;

            if i & WORD_SIGNIFICANT_BIT as usize != 0 {
                x = x.mul_mod(self, n)?;
            }

            i <<= 1;
        }

        Ok(x)
    }

    /// Multiply `self` by 2 ^ i
    pub fn pow2(&mut self, i: usize) -> Result<(), Error> {
        if self.n + i > self.max_bit_len() {
            self.m.try_extend_2(self.n + i)?;
        }

        self.shift_left(i);

        Ok(())
    }

    /// Add n bits of precision, data is not moved
    pub fn extend_subnormal(&mut self, n: usize) -> Result<(), Error> {
        self.m.try_extend_2(self.n + n)
    }

    // self * m1 mod n
    pub fn mul_mod(&self, m1: &Self, n: &Self) -> Result<Self, Error> {
        // TODO: consider other methods, e.g. Barrett's

        debug_assert!(n.m[n.len() - 1] & WORD_SIGNIFICANT_BIT != 0);

        let mut m = Self::reserve_new(self.len() + m1.len())?;

        Self::mul_unbalanced(&self.m, &m1.m, &mut m)?;

        m.trunc_leading_zeroes();

        let (_q, r) = Self::div_unbalanced(&m, &n.m)?;

        let n = Self::find_bit_len(&r);

        Ok(Mantissa { m: r, n })
    }

    // Returns remainder of division of `self` by `n`.
    pub fn rem(&self, n: &Self) -> Result<Self, Error> {
        let (_q, r) = Self::div_unbalanced(&self.m, &n.m)?;
        let n = Self::find_bit_len(&r);
        Ok(Mantissa { m: r, n })
    }

    fn find_bit_len(m: &[Word]) -> usize {
        let mut n = 0;

        for &v in m.iter().rev() {
            if v != 0 {
                let mut v = v;
                while v & WORD_SIGNIFICANT_BIT == 0 {
                    n += 1;
                    v <<= 1;
                }
                break;
            }
            n += WORD_BIT_SIZE;
        }

        m.len() * WORD_BIT_SIZE - n
    }

    pub fn from_u64(p: usize, u: u64) -> Result<(usize, Self), Error> {
        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;

        if m.len() < size_of::<u64>() / size_of::<Word>() {
            return Err(Error::InvalidArgument);
        }

        let nd = m.len() - size_of::<u64>() / size_of::<Word>();
        m[..nd].fill(0);

        #[cfg(target_arch = "x86_64")]
        {
            m[nd] = u;
        }

        #[cfg(target_arch = "x86")]
        {
            let mut u = u;
            for v in &mut m[nd..] {
                *v = u as Word;
                u >>= WORD_BIT_SIZE;
            }
        }

        let shift = Self::maximize(&mut m);
        let mut ret = Mantissa { m, n: 0 };

        ret.n = ret.max_bit_len();

        Ok((shift, ret))
    }

    pub fn from_usize(u: usize) -> Result<(usize, Self), Error> {
        let mut m;

        if u == 0 {
            m = Self::reserve_new(1)?;
            m[0] = 0 as Word;

            let ret = Mantissa { m, n: 0 };

            return Ok((0, ret));
        }

        m = Self::reserve_new(1)?;
        m[0] = u as Word;

        let shift = Self::maximize(&mut m);
        let mut ret = Mantissa { m, n: 0 };

        ret.n = ret.max_bit_len();

        Ok((shift, ret))
    }

    #[cfg(test)]
    pub fn to_u64(&self) -> u64 {
        #[cfg(target_arch = "x86_64")]
        {
            self.m[self.m.len() - 1]
        }

        #[cfg(target_arch = "x86")]
        {
            let mut ret: u64 = 0;
            let nd = size_of::<u64>() / size_of::<Word>();
            ret |= self.m[self.len() - 1] as u64;
            for i in 1..nd {
                ret <<= WORD_BIT_SIZE;
                ret |= if self.len() > i { self.m[self.len() - i - 1] as u64 } else { 0 };
            }
            ret
        }
    }

    /// Returns true if `self` is subnormal.
    #[inline]
    pub fn is_subnormal(&self) -> bool {
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

    /// Shift `self` to the left and return shift value.
    pub fn normilize2(&mut self) -> usize {
        self.n = self.max_bit_len();
        Self::maximize(&mut self.m)
    }

    /// Set n bits to 0 from the left/right.
    pub fn mask_bits(&mut self, mut n: usize, from_left: bool) {
        if from_left {
            for v in self.m.iter_mut().rev() {
                if n >= WORD_BIT_SIZE {
                    *v = 0;
                    n -= WORD_BIT_SIZE;
                } else {
                    let mask = WORD_MAX >> n;
                    *v &= mask;
                    break;
                }
            }
        } else {
            for v in self.m.iter_mut() {
                if n >= WORD_BIT_SIZE {
                    *v = 0;
                    n -= WORD_BIT_SIZE;
                } else {
                    let mask = WORD_MAX << n;
                    *v &= mask;
                    break;
                }
            }
        }
    }

    /// Decompose to raw parts.
    pub fn as_raw_parts(&self) -> (&[Word], usize) {
        (&self.m, self.n)
    }

    /// Construct from raw parts.
    pub fn from_raw_parts(m: &[Word], n: usize) -> Result<Self, Error> {
        let mut mm = Self::reserve_new(m.len())?;
        mm.copy_from_slice(m);
        Ok(Mantissa { m: mm, n })
    }

    /// Returns true if all digits are equal to 0.
    pub fn is_all_zero(&self) -> bool {
        for v in (self.m).iter() {
            if *v != 0 {
                return false;
            }
        }
        true
    }

    /// Returns length of the mantissa in words.
    #[inline]
    pub fn len(&self) -> usize {
        self.m.len()
    }

    /// Returns maximum possible length of the mantissa in digits of the mantissa's base.
    #[inline]
    pub fn max_bit_len(&self) -> usize {
        self.len() * WORD_BIT_SIZE
    }

    /// Round n positions, return true if exponent is to be incremented.
    /// If `check_roundable` is true on input, the function verifies whether the mantissa is roundable, given it contains `s` correct digits.
    /// If `check_roundable` is set to false on return, in any case it means rounding was successful.
    /// If some bits set to 1 during rounding were set to 0, `inexact` will take value true.
    pub fn round_mantissa(
        &mut self,
        n: usize,
        rm: RoundingMode,
        is_positive: bool,
        check_roundable: &mut bool,
        s: usize,
        inexact: &mut bool,
    ) -> bool {
        debug_assert!(s % WORD_BIT_SIZE == 0); // assume s is aligned to the word size.

        // TODO: this function is too complex, because it combines rounding for all rounding modes
        // and checks for roundability at the same time.

        if rm == RoundingMode::None {
            *check_roundable = false;

            // inexact?
            if !(*inexact) && n > 0 && n < self.max_bit_len() {
                if self.find_one_from(self.max_bit_len() - n).is_some() {
                    *inexact |= true;
                }
            }

            return false;
        }

        let self_len = self.m.len();
        if n > 0 && n < self.max_bit_len() {
            let mut i;
            let mut t;
            let mut c = false;
            let mut cc = (n - (self.max_bit_len() - s)) / WORD_BIT_SIZE; // num of roundable significant words

            if rm == RoundingMode::ToEven || rm == RoundingMode::ToOdd {
                let n = n - 1;
                let mut rem_zero = true;
                let mut td = 0; // either all bits set, or zero (default)

                // analyze bits at n and at n+1
                // to decide if we need to add 1 or not.
                let np1 = n + 1;
                i = n / WORD_BIT_SIZE;
                let mut z = i;
                t = n % WORD_BIT_SIZE;
                let ip1 = np1 / WORD_BIT_SIZE;
                let tp1 = np1 % WORD_BIT_SIZE;
                let num = (self.m[i] >> t) & 1;
                if t > 0 {
                    let rb = self.m[i] << (WORD_BIT_SIZE - t);
                    if rb != 0 {
                        rem_zero = false;

                        if *check_roundable {
                            // try to get information from preceding bits
                            let msk = rb & (WORD_MAX << (WORD_BIT_SIZE - t));
                            if msk == rb {
                                td = WORD_MAX;
                            } else if msk != 0 {
                                *check_roundable = false; // self is roundable
                            }
                        }
                    }
                } else if *check_roundable && cc > 0 && z > 0 {
                    // try to get information from preceding word
                    z -= 1;
                    if self.m[z] == WORD_MAX {
                        td = WORD_MAX;
                        rem_zero = false; // sticky is set
                    } else if self.m[z] != 0 {
                        *check_roundable = false; // self is roundable
                        rem_zero = false; // sticky is set
                    }
                    cc -= 1;
                }

                let nump1 = if ip1 < self_len { (self.m[ip1] >> tp1) & 1 } else { 0 };

                // anything before n'th word becomes 0
                for v in &mut self.m[..n / WORD_BIT_SIZE] {
                    if *check_roundable && cc > 0 {
                        if *v != td {
                            *check_roundable = false; // self is roundable
                        } else {
                            cc -= 1;
                        }
                    }
                    if *v != 0 {
                        rem_zero = false;
                    }
                    *v = 0;
                }

                if *check_roundable {
                    return false; // self is not roundable
                }

                // inexactness
                *inexact |= !rem_zero || num == 1;

                // rounding
                let eq1 = num == 1 && rem_zero;
                let gt1 = num == 1 && !rem_zero;

                match rm {
                    RoundingMode::ToEven => {
                        if gt1 || (eq1 && (nump1 & 1) != 0) {
                            // add 1
                            c = true;
                        }
                    }
                    RoundingMode::ToOdd => {
                        if gt1 || (eq1 && (nump1 & 1) == 0) {
                            // add 1
                            c = true;
                        }
                    }
                    _ => unreachable!(),
                };

                if c {
                    // add 1 at (n+1)'th position
                    if ip1 > i {
                        self.m[i] = 0;
                    }
                    i = ip1;
                    t = tp1;
                } else {
                    t += 1;
                }
            } else {
                let mut rem_zero = true;
                let mut td = 0; // either all bits set, or zero (default)

                i = n / WORD_BIT_SIZE;
                let mut z = i;
                t = n % WORD_BIT_SIZE;
                if t > 0 {
                    // bits coming before the least significant bit
                    let rb = self.m[i] << (WORD_BIT_SIZE - t);
                    if rb != 0 {
                        rem_zero = false;

                        if *check_roundable {
                            // try to get information from preceding bits
                            let msk = rb & (WORD_MAX << (WORD_BIT_SIZE - t));
                            if msk == rb {
                                td = WORD_MAX;
                            } else if msk != 0 {
                                *check_roundable = false; // self is roundable
                            }
                        }
                    }
                } else if *check_roundable && cc > 0 && z > 0 {
                    // try to get information from preceding word
                    z -= 1;
                    if self.m[z] == WORD_MAX {
                        td = WORD_MAX;
                        rem_zero = false; // sticky is set
                    } else if self.m[z] != 0 {
                        *check_roundable = false; // self is roundable
                        rem_zero = false; // sticky is set
                    }
                    cc -= 1;
                }

                // anything before n'th word becomes 0
                for v in self.m[..z].iter_mut().rev() {
                    if *check_roundable && cc > 0 {
                        if *v != td {
                            *check_roundable = false; // self is roundable
                        } else {
                            cc -= 1;
                        }
                    }
                    if *v != 0 {
                        rem_zero = false; // sticky is set
                    }
                    *v = 0;
                }

                if *check_roundable {
                    return false; // self is not roundable
                }

                // inexactness
                *inexact |= !rem_zero;

                // rounding
                match rm {
                    RoundingMode::ToZero => {}
                    RoundingMode::FromZero => {
                        if !rem_zero {
                            // add 1
                            c = true;
                        }
                    }
                    RoundingMode::Up => {
                        if !rem_zero && is_positive {
                            // add 1
                            c = true;
                        }
                    }
                    RoundingMode::Down => {
                        if !rem_zero && !is_positive {
                            // add 1
                            c = true;
                        }
                    }
                    _ => unreachable!(),
                };
            }

            debug_assert!(!(*check_roundable));

            if c {
                if i < self_len {
                    if (self.m[i] >> t) as DoubleWord + 1 < (WORD_BASE >> t) {
                        self.m[i] = ((self.m[i] >> t) + 1) << t;
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
                // just remove trailing bits
                self.m[i] = if t >= WORD_BIT_SIZE { 0 } else { (self.m[i] >> t) << t };
            }
        }
        false
    }

    /// Sets the precision to `p`.
    pub fn set_length(&mut self, p: usize) -> Result<(), Error> {
        let sz = Self::bit_len_to_word_len(p);
        let orig_len = self.m.len();
        if sz < orig_len {
            self.m.trunc_to(p);
            let nn = (orig_len - sz) * WORD_BIT_SIZE;
            if self.n >= nn {
                self.n -= nn;
            } else {
                self.n = 0;
            }
        } else if sz > orig_len {
            self.m.try_extend(p)?;
            if self.n != 0 {
                self.n += (sz - orig_len) * WORD_BIT_SIZE;
            }
        }
        Ok(())
    }

    pub fn most_significant_word(&self) -> Word {
        if self.n > 0 {
            self.m[(self.n - 1) / WORD_BIT_SIZE]
        } else {
            0
        }
    }

    #[cfg(feature = "random")]
    /// Returns randomized mantissa with at least p bits of length.
    pub fn random_normal(p: usize) -> Result<Self, Error> {
        let mut m = Self::reserve_new(Self::bit_len_to_word_len(p))?;
        for v in m.iter_mut() {
            *v = rand::random::<Word>();
        }
        let mut ret = Mantissa { m, n: 0 };
        if !ret.is_all_zero() {
            Self::maximize(&mut ret.m);
            ret.n = WORD_BIT_SIZE * ret.m.len();
            ret.m[0] ^= rand::random::<Word>() >> 1;
        }
        Ok(ret)
    }

    /// Clones the mantissa.
    pub fn clone(&self) -> Result<Self, Error> {
        let mut m = Self::reserve_new(self.m.len())?;
        m.copy_from_slice(&self.m);
        Ok(Mantissa { m, n: self.n })
    }

    pub fn digits(&self) -> &[Word] {
        &self.m
    }

    pub fn digits_mut(&mut self) -> &mut [Word] {
        &mut self.m
    }

    pub fn bit_len(&self) -> usize {
        self.n
    }

    /// returns true if `self` represents odd integer.
    pub fn is_odd_int(&self, n: usize) -> bool {
        debug_assert!(n < self.max_bit_len() && n > 0);

        if ((self.m[n / WORD_BIT_SIZE]) >> (n % WORD_BIT_SIZE)) & 1 != 0 {
            let b = (n - 1) % WORD_BIT_SIZE;
            let i = (n - 1) / WORD_BIT_SIZE;

            if b > 0 && self.m[i] << (WORD_BIT_SIZE - b) != 0 {
                return false;
            }

            self.m.iter().take(i).all(|x| *x == 0)
        } else {
            false
        }
    }

    // Add 1 ulp to mantissa, return true if carry occures
    fn add_ulp(&mut self) -> bool {
        let mut c = 1;
        for v in self.m.iter_mut() {
            c = add_carry(*v, 0, c, v);
            if c == 0 {
                break;
            }
        }
        c > 0
    }

    /// Compute the square root.
    pub fn sqrt(
        &self,
        p: usize,
        rm: RoundingMode,
        is_positive: bool,
        inexact: &mut bool,
        odd_exp: bool,
    ) -> Result<(isize, Self), Error> {
        let p = Self::bit_len_to_word_len(p);

        let k = (p.max(self.len()) + 1) * 2;

        let mut e_shift = 0;

        let mut m1 = Self::reserve_new(k)?;

        let l = k - self.len();
        m1[l..].copy_from_slice(&self.m);
        m1[..l].fill(0);

        if odd_exp {
            shift_slice_right(&mut m1, 1);
        }

        let (q, r) = Self::sqrt_rem(&m1)?;

        let mut m3 = Mantissa { m: q, n: 0 };

        let r_sticky = r.iter().any(|&x| x != 0);

        // rounding
        if r_sticky {
            *inexact |= true;

            if rm as u32 & 0b1100000 != 0 {
                m3.m[0] |= 1;
            } else if rm == RoundingMode::FromZero
                || (is_positive && rm == RoundingMode::Up)
                || (!is_positive && rm == RoundingMode::Down)
            {
                if m3.add_ulp() {
                    let m3l = m3.len() - 1;
                    m3.m[m3l] = WORD_SIGNIFICANT_BIT;
                    e_shift += 1;
                }
            }
        }

        _ = Self::maximize(&mut m3.m) as isize;

        if m3.round_mantissa(
            (m3.len() - p) * WORD_BIT_SIZE,
            rm,
            is_positive,
            &mut false,
            m3.max_bit_len(),
            inexact,
        ) {
            e_shift += 1;
        }

        m3.m.trunc_to(p * WORD_BIT_SIZE);
        m3.n = m3.max_bit_len();

        Ok((e_shift, m3))
    }

    /// Compute the cube root.
    pub fn cbrt(
        &self,
        p: usize,
        rm: RoundingMode,
        is_positive: bool,
        inexact: &mut bool,
        add_exp: isize,
    ) -> Result<(isize, Self), Error> {
        let p = Self::bit_len_to_word_len(p);

        let k = p.max(self.len()) + 1;
        let k3 = k * 3;

        let mut e_shift = -((k * WORD_BIT_SIZE) as isize);

        let mut m1 = Self::reserve_new(k3)?;

        let l = k3 - self.len();
        m1[l..].copy_from_slice(&self.m);
        m1[..l].fill(0);

        debug_assert!(add_exp >= 0);

        shift_slice_right(&mut m1, add_exp as usize);

        let (q, r) = Self::cbrt_rem(m1)?;

        let mut m3 = Mantissa { m: q, n: 0 };

        let r_sticky = r.iter().any(|&x| x != 0);

        // rounding
        if r_sticky {
            *inexact |= true;

            if rm as u32 & 0b1100000 != 0 {
                m3.m[0] |= 1;
            } else if rm == RoundingMode::FromZero
                || (is_positive && rm == RoundingMode::Up)
                || (!is_positive && rm == RoundingMode::Down)
            {
                if m3.add_ulp() {
                    let m3l = m3.len() - 1;
                    m3.m[m3l] = WORD_SIGNIFICANT_BIT;
                    e_shift += 1;
                }
            }
        }

        e_shift += (m3.len() * WORD_BIT_SIZE) as isize;

        e_shift -= Self::maximize(&mut m3.m) as isize;

        if m3.round_mantissa(
            (m3.len() - p) * WORD_BIT_SIZE,
            rm,
            is_positive,
            &mut false,
            m3.max_bit_len(),
            inexact,
        ) {
            e_shift += 1;
        }

        m3.m.trunc_to(p * WORD_BIT_SIZE);
        m3.n = m3.max_bit_len();

        Ok((e_shift, m3))
    }
}
