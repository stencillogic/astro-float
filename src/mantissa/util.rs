//! Auxiliary structures.


use itertools::izip;
use crate::defs::DIGIT_MAX;
use crate::defs::Digit;
use crate::defs::DIGIT_BASE;
use crate::defs::DIGIT_BIT_SIZE;
use crate::defs::DoubleDigit;
use crate::defs::DigitSigned;
use core::ops::DerefMut;
use core::ops::Deref;


/// Length of the slice extended by extra size.
pub struct ExtendedSlice<T, V> where V: Iterator<Item = T> {
    s: V,
    extra: usize,
    default: T,
}

impl<T, V> ExtendedSlice<T, V> where V: Iterator<Item = T> {
    pub fn new(s: V, extra: usize, default: T) -> Self {
        ExtendedSlice {
            s,
            extra,
            default,
        }
    }
}

impl<T, V> Iterator for ExtendedSlice<T, V> where V: Iterator<Item = T>, T: Copy + Clone {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.extra > 0 {
            self.extra -= 1;
            Some(self.default)
        } else {
            self.s.next()
        }
    }
}

/// Slice values shifted to the right by the specified amount of bits.
pub struct RightShiftedSlice<'a, T> {
    s: core::slice::Iter<'a, T>,
    bits: usize,
    prev: Option<T>,
    default: T,
    extend_sz: usize,
}

impl<'a, T> RightShiftedSlice<'a, T> where T: Copy + Clone {
    pub fn new(s: &'a [T], shift: usize, default: T, mut extend_sz: usize) -> Self {
        let elsz = core::mem::size_of::<T>()*8;
        let mut idx = shift / elsz;
        let bits = shift % elsz;

        if extend_sz > idx {
            extend_sz -= idx;
            idx = 0;
        } else {
            idx -= extend_sz;
            extend_sz = 0;
        } 

        let mut prev = None;
        let iter = if idx < s.len() {
            let mut iter = s[idx..].iter();
            prev = iter.next().copied();
            iter
        } else {
            [].iter()
        };
        RightShiftedSlice {
            s: iter,
            bits,
            prev,
            default,
            extend_sz,
        }
    }
}


impl<'a, T> Iterator for RightShiftedSlice<'a, T> 
    where T: core::ops::Shl<usize, Output = T> 
        + core::ops::Shr<usize, Output = T> 
        + core::ops::BitOr<T, Output = T> 
        + Copy
        + Clone
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.extend_sz > 0 {
            self.extend_sz -= 1;
            if self.extend_sz == 0 && self.bits > 0 {
                if let Some(hi) = self.prev {
                    Some(hi << (core::mem::size_of::<T>()*8 - self.bits))
                } else {
                    Some(self.default)
                }
            } else {
                Some(self.default)
            }
        } else if let Some(lo) = self.prev {
            self.prev = self.s.next().copied();
            if self.bits == 0 {
                Some(lo)
            } else if let Some(hi) = self.prev {
                Some((hi << (core::mem::size_of::<T>()*8 - self.bits)) | (lo >> self.bits))
            } else {
                Some(lo >> self.bits)
            }
        } else {
            Some(self.default)
        }
    }
}

// Shift m right by n digits.
pub fn shift_slice_right(m: &mut [Digit], n: usize) {
    let idx = n / DIGIT_BIT_SIZE;
    let shift = n % DIGIT_BIT_SIZE;
    let mut d;
    if idx >= m.len() {
        m.fill(0);
    } else if shift > 0 {
        for i in 0..m.len() {
            d = 0;
            if idx + i + 1 < m.len() {
                d = m[idx + i + 1] as DoubleDigit;
                d <<= DIGIT_BIT_SIZE;
            }
            if i + idx < m.len() {
                d |= m[idx + i] as DoubleDigit;    
            }
            d >>= shift;
            m[i] = d as Digit;
        }
    } else if idx > 0 {
        let src = m[idx..].as_ptr();
        let dst = m.as_mut_ptr();
        let cnt = m.len() - idx;
        unsafe {
            core::intrinsics::copy(src, dst, cnt);
        };
        m[cnt..].fill(0);
    }
}


// Shift m left by n digits.
pub fn shift_slice_left(m: &mut [Digit], n: usize) {
    let idx = n / DIGIT_BIT_SIZE;
    let shift = n % DIGIT_BIT_SIZE;
    let mut d;
    if idx >= m.len() {
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
        let dst = m[idx..].as_mut_ptr();
        let src = m.as_ptr();
        unsafe {
            core::intrinsics::copy(src, dst, m.len()-idx);
        };
        m[..idx].fill(0);
    }
}



// Internal repr of SliceWithSign.
enum SliceWithSignType<'a> {
    Mut(&'a mut [Digit]),
    Immut(&'a [Digit])
}

// Slice of digits with sign is a simplified integer number representation.
pub struct SliceWithSign<'a> {
    m: SliceWithSignType<'a>,
    sign: i8,
}

impl<'a> SliceWithSign<'a> {
    pub fn new_mut(m: &'a mut [Digit], sign: i8) -> Self {
        SliceWithSign {
            m: SliceWithSignType::Mut(m),
            sign,
        }
    }

    pub fn new(m: &'a[Digit], sign: i8) -> Self {
        SliceWithSign {
            m: SliceWithSignType::Immut(m),
            sign,
        }
    }

    pub fn add<'b, 'c>(&self, s2: &SliceWithSign<'b>, dst: &mut SliceWithSign<'c>) {
        self.add_sub(s2, dst, 1);
    }

    pub fn sub<'b, 'c>(&self, s2: &SliceWithSign<'b>, dst: &mut SliceWithSign<'c>) {
        self.add_sub(s2, dst, -1);
    }

    pub fn add_assign<'c>(&mut self, s2: &SliceWithSign<'c>, work_buf: &mut [Digit]) {
        self.add_sub_assign(s2, 1, work_buf);
    }

    pub fn sub_assign<'c>(&mut self, s2: &SliceWithSign<'c>, work_buf: &mut [Digit]) {
        self.add_sub_assign(s2, -1, work_buf);
    }

    fn add_sub<'b, 'c>(&self, s2: &SliceWithSign<'b>, dst: &mut SliceWithSign<'c>, op: i8) {
        if (self.sign != s2.sign && op > 0) || (op < 0 && self.sign == s2.sign) {
            // subtract
            let cmp = Self::abs_cmp(self, s2);
            if cmp > 0 {
                dst.sign = self.sign;
                Self::abs_sub(self, s2, dst);
            } else if cmp < 0 {
                dst.sign = s2.sign*op;
                Self::abs_sub(s2, self, dst);
            } else {
                dst.fill(0);
            };
        } else {
            dst.sign = self.sign;
            Self::abs_add(self, s2, dst);
        }
    }

    fn add_sub_assign<'b>(&mut self, s2: &SliceWithSign<'b>, op: i8, work_buf: &mut [Digit]) {
        if (self.sign != s2.sign && op > 0) || (op < 0 && self.sign == s2.sign) {
            // subtract
            let cmp = Self::abs_cmp(self, s2);
            if cmp > 0 {
                Self::abs_sub_assign(self, s2);
            } else if cmp < 0 {
                self.sign = s2.sign*op;
                work_buf.copy_from_slice(s2.deref());
                Self::abs_sub_assign(work_buf, self);
                let dst = self.deref_mut();
                let max_len = dst.len().min(work_buf.len());
                dst[..max_len].copy_from_slice(&work_buf[..max_len]);
                dst[max_len..].fill(0);
            } else {
                self.fill(0);
            };
        } else {
            Self::abs_add_assign(self, s2);
        }
    }

    pub fn mul_assign<'c>(&mut self, s2: &SliceWithSign<'c>, work_buf: &mut [Digit]) {
        work_buf.fill(0);
        for (i, d1mi) in self.deref().iter().enumerate() {
            let d1mi = *d1mi as DoubleDigit;
            if d1mi == 0 {
                continue;
            }

            let mut k = 0;
            for (m2j, m3ij) in s2.deref().iter().zip(work_buf[i..].iter_mut()) {
                let m = d1mi * (*m2j as DoubleDigit) + *m3ij as DoubleDigit + k;

                *m3ij = m as Digit;
                k = m >> (DIGIT_BIT_SIZE);
            }
            work_buf[i + s2.len()] += k as Digit;
        }
        self.deref_mut().copy_from_slice(work_buf);
        self.sign *= s2.sign;
    }

    pub fn shift_left(&mut self, shift: usize) {
        shift_slice_left(self, shift);
    }

    pub fn shift_right(&mut self, shift: usize) {
        shift_slice_right(self, shift);
    }

    // set bits bits to 0 from the left (effectively: self mod 2^bits)
    pub fn mask_bits_left(&mut self, mut bits: usize) {
        let mut iter = self.deref_mut().iter_mut().rev();
        loop {
            if bits < DIGIT_BIT_SIZE {
                break;
            }
            if let Some(v) = iter.next() {
                *v = 0;
                bits -= DIGIT_BIT_SIZE;
            }
        }
        if bits > 0 {
            let mask = DIGIT_MAX >> (bits % DIGIT_BIT_SIZE);
            if let Some(v) = iter.next() {
                *v &= mask;
            }
        }
    }

    pub fn div_by_digit(&mut self, d: Digit) {
        debug_assert!(d != 0);
        let d = d as DoubleDigit;
        let mut rh = 0;
        let m = self.deref_mut();
        let mut iter = m.iter_mut().rev();
        let mut val;
        if let Some(v) = iter.next() {
            val = v;
        } else {
            return;
        }

        if (*val as DoubleDigit) < d {
            rh = *val as DoubleDigit;
            *val = 0;
            if let Some(v) = iter.next() {
                val = v;
            } else {
                return;
            }
        }

        loop {
            let qh = rh * DIGIT_BASE as DoubleDigit + *val as DoubleDigit;

            rh = qh % d;

            *val = (qh / d) as Digit;

            if let Some(v) = iter.next() {
                val = v;
            } else {
                break;
            }
        }
    }

    pub fn copy_from<'c>(&mut self, s2: &SliceWithSign<'c>) {
        match &mut self.m {
            SliceWithSignType::Mut(m) => {
                match &s2.m {
                    SliceWithSignType::Mut(s) => m[..s.len()].copy_from_slice(s),
                    SliceWithSignType::Immut(s) => m[..s.len()].copy_from_slice(s),
                };
            },
            _ => panic!(),
        }
    }

    fn abs_add(s1: &[Digit], s2: &[Digit], dst: &mut [Digit]) {
        let mut c = 0;
        let mut iter1 = s1.iter();
        let mut iter2 = s2.iter();
        let mut iter3 = dst.iter_mut();
        let l = s1.len().min(s2.len());
        for _ in 0..l {
            let a = if let Some(v) = iter1.next() { v } else { break };
            let b = if let Some(v) = iter2.next() { v } else { break };
            let mut s = c + *a as DoubleDigit + *b as DoubleDigit;
            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }
            *iter3.next().unwrap() = s as Digit;
        }
        if let Some(v) = iter1.next() {
            let mut s = c + *v as DoubleDigit;
            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }
            *iter3.next().unwrap() = s as Digit;
        }
        if let Some(v) = iter2.next() {
            let mut s = c + *v as DoubleDigit;
            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }
            *iter3.next().unwrap() = s as Digit;
        }
        if c > 0 {
            *iter3.next().unwrap() = c as Digit;
        }
    }

    fn abs_add_assign(s1: &mut [Digit], s2: &[Digit]) {
        let mut c = 0;
        let mut iter1 = s1.iter_mut();
        let iter2 = s2.iter();
        for (b, a) in izip!(iter2, iter1.by_ref()) {
            let mut s = c + *a as DoubleDigit + *b as DoubleDigit;
            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }
            *a = s as Digit;
        }
        if let Some(v) = iter1.next() {
            *v += c as Digit;
        }
    }

    fn abs_sub_assign(s1: &mut [Digit], s2: &[Digit]) {
        let mut c = 0;
        let mut iter1 = s1.iter_mut();
        let iter2 = s2.iter();
        for (b, a) in izip!(iter2, iter1.by_ref()) {
            let v1 = *a as DoubleDigit;
            let v2 = *b as DoubleDigit;
            if v1 < v2 + c {
                *a = (v1 + DIGIT_BASE - v2 - c) as Digit;
                c = 1;
            } else {
                *a = (v1 - v2 - c) as Digit;
                c = 0;
            }
        }
        if let Some(v) = iter1.next() {
            *v -= c as Digit;
        }
    }

    fn abs_sub(s1: &[Digit], s2: &[Digit], dst: &mut [Digit]) {
        let mut c = 0;
        let mut iter1 = s1.iter();
        let iter2 = s2.iter();
        let mut iter3 = dst.iter_mut();
        for (b, a, d) in izip!(iter2, iter1.by_ref(), iter3.by_ref()) {
            let v1 = *a as DoubleDigit;
            let v2 = *b as DoubleDigit;
            if v1 < v2 + c {
                *d = (v1 + DIGIT_BASE - v2 - c) as Digit;
                c = 1;
            } else {
                *d = (v1 - v2 - c) as Digit;
                c = 0;
            }
        }
        if let Some(v) = iter1.next() {
            *iter3.next().unwrap() = *v - c as Digit;
        }
    }

    // decrement absolute value by 1
    pub fn decrement_abs(&mut self) {
        for v in self.iter_mut() {
            if *v == 0 {
                *v = DIGIT_MAX;
            } else {
                *v -= 1;
                return;
            }
        }
        panic!("numeric overflow");
    }

    fn abs_cmp(s1: &[Digit], s2: &[Digit]) -> DigitSigned {
        let len = s1.len().min(s2.len());
        for v in &s1[len..] {
            if *v != 0 {
                return 1;
            }
        }
        for v in &s2[len..] {
            if *v != 0 {
                return -1;
            }
        }
        for (a, b) in core::iter::zip(s1[..len].iter().rev(), s2[..len].iter().rev()) {
            let diff = *a as DigitSigned - *b as DigitSigned;
            if diff != 0 {
                return diff;
            }
        }
        0
    }

    #[inline]
    pub fn set_sign(&mut self, sign: i8) {
        self.sign = sign;
    }

    #[inline]
    pub fn sign(&self) -> i8 {
        self.sign
    }
}

impl<'a> Deref for SliceWithSign<'a> {
    type Target = [Digit];

    #[inline]
    fn deref(&self) -> &[Digit] {
        match &self.m {
            SliceWithSignType::Mut(m) => m,
            SliceWithSignType::Immut(m) => m,
        }
    }
}

impl<'a> DerefMut for SliceWithSign<'a> {

    #[inline]
    fn deref_mut(&mut self) -> &mut [Digit] {
        match &mut self.m {
            SliceWithSignType::Mut(m) => m,
            _ => panic!(),
        }
    }
}
