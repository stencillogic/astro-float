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


// Shift m left by n digits.
pub fn shift_slice_left(m: &mut [Digit], n: usize) {
    let idx = n / DIGIT_BIT_SIZE;
    let shift = n % DIGIT_BIT_SIZE;
    if idx >= m.len() {
        m.fill(0);
    } else if shift > 0 {
        let l = m.len() - 1;
        let end = m.as_mut_ptr();
        unsafe {    // use of slices is almost 50% slower
            let mut dst = end.add(l);
            let mut src = end.add(l - idx);
            loop {
                if src > end {
                    let mut d = *src << shift;
                    src = src.sub(1);
                    d |= *src >> (DIGIT_BIT_SIZE - shift);
                    *dst = d;
                    dst = dst.sub(1);
                } else {
                    break;
                }
            }
            *dst = *src << shift;
        }
        m[0..idx].fill(0);
    } else if idx > 0 {
        let dst = m[idx..].as_mut_ptr();
        let src = m.as_ptr();
        unsafe {
            core::intrinsics::copy(src, dst, m.len()-idx);
        };
        m[..idx].fill(0);
    }
}

// Shift m left by n digits and put result in m2.
pub fn shift_slice_left_copy(m: &[Digit], m2: &mut [Digit], n: usize) {
    let idx = n / DIGIT_BIT_SIZE;
    let shift = n % DIGIT_BIT_SIZE;
    if idx >= m2.len() {
        m2.fill(0);
    } else if shift > 0 {
        m2[..idx].fill(0);
        let mut dst = m2[idx..].iter_mut();
        let src = m.iter();
        let mut prev = 0;
        for (a, b) in src.zip(dst.by_ref()) {
            *b = (prev >> (DIGIT_BIT_SIZE - shift)) | (*a << shift);
            prev = *a;
        }
        if let Some(b) = dst.next() {
            *b = prev >> (DIGIT_BIT_SIZE - shift);
        }
        for b in dst {
            *b = 0;
        }
    } else {
        m2[..idx].fill(0);
        let mut dst = m2[idx..].iter_mut();
        for (a, b) in m.iter().zip(dst.by_ref()) {
            *b = *a;
        }
        for b in dst {
            *b = 0;
        }
    }
}


// Shift m right by n digits.
pub fn shift_slice_right(m: &mut [Digit], n: usize) {
    let idx = n / DIGIT_BIT_SIZE;
    let shift = n % DIGIT_BIT_SIZE;
    if idx >= m.len() {
        m.fill(0);
    } else if shift > 0 {
        let l = m.len();
        let mut dst = m.as_mut_ptr();
        unsafe {    // use of slices is almost 50% slower
            let end = dst.add(l - 1);
            let mut src = dst.add(idx);
            loop {
                if src < end {
                    let mut d = *src >> shift;
                    src = src.add(1);
                    d |= *src << (DIGIT_BIT_SIZE - shift);
                    *dst = d;
                    dst = dst.add(1);
                } else {
                    break;
                }
            }
            *dst = *src >> shift;
        }
        m[l - idx..].fill(0);
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


// Internal repr of SliceWithSign.
enum SliceWithSignType<'a> {
    Mut(&'a mut [Digit]),
    Immut(&'a [Digit])
}

// Slice of digits with sign is a lightweight integer number representation.
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

    #[inline]
    pub fn add<'b, 'c>(&self, s2: &SliceWithSign<'b>, dst: &mut SliceWithSign<'c>) {
        self.add_sub(s2, dst, 1);
    }

    #[inline]
    pub fn sub<'b, 'c>(&self, s2: &SliceWithSign<'b>, dst: &mut SliceWithSign<'c>) {
        self.add_sub(s2, dst, -1);
    }

    #[inline]
    pub fn add_assign<'c>(&mut self, s2: &SliceWithSign<'c>) {
        self.add_sub_assign(s2, 1);
    }

    #[inline]
    pub fn sub_assign<'c>(&mut self, s2: &SliceWithSign<'c>) {
        self.add_sub_assign(s2, -1);
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

    fn add_sub_assign<'b>(&mut self, s2: &SliceWithSign<'b>, op: i8) {
        if (self.sign != s2.sign && op > 0) || (op < 0 && self.sign == s2.sign) {
            // subtract
            let cmp = Self::abs_cmp(self, s2);
            if cmp > 0 {
                Self::abs_sub_assign_1(self, s2);
            } else if cmp < 0 {
                Self::abs_sub_assign_2(self, s2);
                self.sign = s2.sign*op;
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

    #[inline]
    pub fn shift_left(&mut self, shift: usize) {
        shift_slice_left(self, shift);
    }

    #[inline]
    pub fn shift_right(&mut self, shift: usize) {
        shift_slice_right(self, shift);
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

        let (iter1, mut iter2) = if s1.len() < s2.len() {
            (s1.iter(), s2.iter())
        } else {
            (s2.iter(), s1.iter())
        };

        let mut iter3 = dst.iter_mut();

        for (a, b, x) in izip!(iter1, iter2.by_ref(), iter3.by_ref()) {
            c = add_carry(*a, *b, c, x);
        }

        for (b, x) in iter2.zip(iter3.by_ref()) {
            c = add_carry(0, *b, c, x);
        }

        if c > 0 {
            *iter3.next().unwrap() = c as Digit;
        }

        for v in iter3 {
            *v = 0;
        }
    }

    fn abs_add_assign(s1: &mut [Digit], s2: &[Digit]) {

        let mut c = 0;
        let mut iter1 = s1.iter_mut();
        let iter2 = s2.iter();

        for (b, a) in izip!(iter2, iter1.by_ref()) {
            c = add_carry(*a, *b, c, a);
        }

        for a in iter1 {
            c = add_carry(*a, 0, c, a);
        }
    }

    // prereq: val of s1 >= val of s2
    fn abs_sub_assign_1(s1: &mut [Digit], s2: &[Digit]) {

        let mut c = 0;
        let mut iter1 = s1.iter_mut();
        let iter2 = s2.iter();

        for (b, a) in izip!(iter2, iter1.by_ref()) {
            c = sub_borrow(*a, *b, c, a);
        }

        for a in iter1 {
            c = sub_borrow(*a, 0, c, a);
        }

        debug_assert!(c == 0);
    }

    // prereq: val of s2 > val of s1
    fn abs_sub_assign_2(s1: &mut [Digit], s2: &[Digit]) {

        let mut c = 0;

        for (a, b) in s2.iter().zip(s1.iter_mut()) {
            c = sub_borrow(*a, *b, c, b);
        }

        debug_assert!(c == 0);
    }

    fn abs_sub(s1: &[Digit], s2: &[Digit], dst: &mut [Digit]) {

        let mut c = 0;

        let mut iter1 = s1.iter();
        let iter2 = s2.iter();
        let mut iter3 = dst.iter_mut();

        for (b, a, d) in izip!(iter2, iter1.by_ref(), iter3.by_ref()) {
            c = sub_borrow(*a, *b, c, d);
        }

        if c > 0 {
            for (a, d) in iter1.zip(iter3.by_ref()) {
                c = sub_borrow(*a, 0, c, d);
            }
        } else {
            for (a, d) in iter1.zip(iter3.by_ref()) {
                *d = *a;
            }
        }

        for v in iter3 {
            *v = 0;
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

    pub fn is_zero(&self) -> bool {
        for v in self.iter() {
            if *v != 0 {
                return false;
            }
        }
        true
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

#[inline(always)]
pub fn add_carry(a: Digit, b: Digit, c: Digit, r: &mut Digit) -> Digit {

    #[cfg(target_arch = "x86_64")] 
    {
        unsafe { core::arch::x86_64::_addcarry_u32(c as u8, a, b, r) as Digit } 
    }
    
    #[cfg(target_arch = "x86")] 
    {
        unsafe { core::arch::x86::_addcarry_u32(c as u8, a, b, r) as Digit } 
    }
    
    #[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
    {
        let mut s = c as DoubleDigit + a as DoubleDigit + b as DoubleDigit;
        if s >= DIGIT_BASE {
            s -= DIGIT_BASE;
            *r = s as Digit;
            1
        } else {
            *r = s as Digit;
            0
        }
    }
}

#[inline(always)]
pub fn sub_borrow(a: Digit, b: Digit, c: Digit, r: &mut Digit) -> Digit {

    #[cfg(target_arch = "x86_64")] 
    {
        unsafe { core::arch::x86_64::_subborrow_u32(c as u8, a, b, r) as Digit }
    }

    #[cfg(target_arch = "x86")] 
    {
        unsafe { core::arch::x86::_subborrow_u32(c as u8, a, b, r) as Digit }
    }
    
    #[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
    {
        let v1 = a as DoubleDigit;
        let v2 = b as DoubleDigit + c as DoubleDigit;
    
        if v1 < v2 {
            *r = (v1 + DIGIT_BASE - v2) as Digit;
            1
        } else {
            *r = (v1 - v2) as Digit;
            0
        }
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_abs_sub_assign2() {
        let mut s1 = [1, 2, 5, 4, 0];
        let s2 =     [1, 2, 3, 4, 1];
        let s3 = [1, 2, 5, 4, 0];

        let mut s1 = SliceWithSign::new_mut(&mut s1, 1);
        let s2 = SliceWithSign::new(&s2, 1);
        let s3 = SliceWithSign::new(&s3, 1);

        SliceWithSign::abs_sub_assign_2(&mut s1, &s2);
        SliceWithSign::abs_add_assign(&mut s1, &s3);
        assert!(s1[..] == s2[..]);
    }
}