//! Toom-3 multiplication.

use crate::defs::DIGIT_BASE;
use crate::defs::DIGIT_BIT_SIZE;
use crate::defs::DoubleDigit;
use crate::defs::DigitSigned;
use crate::defs::Error;
use crate::defs::Digit;
use crate::mantissa::Mantissa;
use crate::mantissa::buf::DigitBuf;
use core::ops::DerefMut;
use core::ops::Deref;
use itertools::izip;


enum SliceWithSignType<'a> {
    Mut(&'a mut [Digit]),
    Immut(&'a [Digit])
}

// Auxiliary structure: slice of digits with sign.
struct SliceWithSign<'a> {
    m: SliceWithSignType<'a>,
    sign: i8,
}

impl<'a> SliceWithSign<'a> {
    fn new_mut(m: &'a mut [Digit], sign: i8) -> Self {
        SliceWithSign {
            m: SliceWithSignType::Mut(m),
            sign,
        }
    }

    fn new(m: &'a[Digit], sign: i8) -> Self {
        SliceWithSign {
            m: SliceWithSignType::Immut(m),
            sign,
        }
    }

    fn add<'b, 'c>(&self, s2: &SliceWithSign<'b>, dst: &mut SliceWithSign<'c>) {
        self.add_sub(s2, dst, 1);
    }

    fn sub<'b, 'c>(&self, s2: &SliceWithSign<'b>, dst: &mut SliceWithSign<'c>) {
        self.add_sub(s2, dst, -1);
    }

    fn add_assign<'c>(&mut self, s2: &SliceWithSign<'c>, work_buf: &mut [Digit]) {
        self.add_sub_assign(s2, -1, work_buf);
    }

    fn sub_assign<'c>(&mut self, s2: &SliceWithSign<'c>, work_buf: &mut [Digit]) {
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
            Self::abs_add(self, s2, dst);
        }
    }

    fn add_sub_assign<'b, 'c>(&mut self, s2: &SliceWithSign<'b>, op: i8, work_buf: &mut [Digit]) {
        if (self.sign != s2.sign && op > 0) || (op < 0 && self.sign == s2.sign) {
            // subtract
            let cmp = Self::abs_cmp(self, s2);
            if cmp > 0 {
                Self::abs_sub_assign(self, s2);
            } else if cmp < 0 {
                self.sign = s2.sign*op;
                work_buf.copy_from_slice(s2.deref());
                Self::abs_sub_assign(work_buf, self);
                self.deref_mut().copy_from_slice(work_buf);
            } else {
                self.fill(0);
            };
        } else {
            Self::abs_add_assign(self, s2);
        }
    }

    fn mul_assign<'c, 'd>(&mut self, s2: &SliceWithSign<'c>, work_buf: &mut [Digit]) {
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
            work_buf[i + work_buf.len()] += k as Digit;
        }
        self.deref_mut().copy_from_slice(work_buf);
        self.sign *= s2.sign;
    }

    fn shift_left(&mut self, shift: usize) {
        debug_assert!(shift < DIGIT_BIT_SIZE);
        let mut prev = 0;
        let rshift = DIGIT_BIT_SIZE - shift;
        for v in self.deref_mut().iter_mut() {
            let t = *v;
            *v = (t << shift) | (prev >> rshift);
            prev = t;
        }
    }

    fn shift_right(&mut self, shift: usize) {
        debug_assert!(shift < DIGIT_BIT_SIZE);
        let mut prev = 0;
        let lshift = DIGIT_BIT_SIZE - shift;
        for v in self.deref_mut().iter_mut().rev() {
            let t = *v;
            *v = (t >> shift) | (prev << lshift);
            prev = t;
        }
    }

    fn div_by_digit(&mut self, d: Digit) {
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
                *val = (rh * DIGIT_BASE as DoubleDigit / d) as Digit;
                break;
            }
        }
    }

    fn add_with_shift<'c>(&mut self, s2: &SliceWithSign<'c>, shift: usize) {
        debug_assert!(self.sign > 0);
        debug_assert!(s2.sign > 0);
        let mut c = 0;
        let mut prev = 0;
        let rshift = DIGIT_BIT_SIZE - shift;
        for (a, b) in izip!(self.deref_mut().iter_mut(), s2.deref().iter()) {
            let mut s = c + *a as DoubleDigit + (((*b as DoubleDigit) << shift) | (prev >> rshift));
            prev = *b as DoubleDigit;
            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }
            *a = s as Digit;
        }
        debug_assert!(c == 0);
    }

    fn copy_from<'c>(&mut self, s2: &SliceWithSign<'c>) {
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
        for (a, b, d) in izip!(s1.iter(), s2.iter(), dst.iter_mut()) {
            let mut s = c + *a as DoubleDigit + *b as DoubleDigit;
            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }
            *d = s as Digit;
        }
        debug_assert!(c == 0);
    }

    fn abs_add_assign(s1: &mut [Digit], s2: &[Digit]) {
        let mut c = 0;
        for (a, b) in izip!(s1.iter_mut(), s2.iter()) {
            let mut s = c + *a as DoubleDigit + *b as DoubleDigit;
            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }
            *a = s as Digit;
        }
        debug_assert!(c == 0);
    }

    fn abs_sub_assign(s1: &mut [Digit], s2: &[Digit]) {
        let mut c = 0;
        for (a, b) in izip!(s1.iter_mut(), s2) {
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
        debug_assert!(c == 0);
    }

    fn abs_sub(s1: &[Digit], s2: &[Digit], dst: &mut [Digit]) {
        let mut c = 0;
        for (a, b, d) in izip!(s1, s2, dst.iter_mut()) {
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
        debug_assert!(c == 0);
    }

    fn abs_cmp(s1: &[Digit], s2: &[Digit]) -> DigitSigned {
        let len = s1.len().min(s2.len());
        for (a, b) in core::iter::zip(s1.iter().rev(), s2.iter().rev()) {
            let diff = *a as DigitSigned - *b as DigitSigned;
            if diff != 0 {
                return diff;
            }
        }
        for v in &s1[..s1.len() - len] {
            if *v != 0 {
                return 1;
            }
        }
        for v in &s2[..s2.len() - len] {
            if *v != 0 {
                return -1;
            }
        }
        0
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

impl Mantissa {

    fn toom3_get_splits(m: &[Digit], l: usize) -> (SliceWithSign, SliceWithSign, SliceWithSign) {
        let b11 = l.min(m.len());
        let b12 = l.min(m.len() - b11) + b11;
        let m0 = &m[..b11];
        let m1 = &m[b11..b12];
        let m2 = &m[b12..];
        (SliceWithSign::new(m0, 1), SliceWithSign::new(m1, 1), SliceWithSign::new(m2, 1))
    }

    // Toom-3 multiplication.
    fn toom3(d1: &mut [Digit], d2: &[Digit]) -> Result<(), Error> {

        let l = d1.len().max(d2.len()) / 3 + 1;
        let (m0, m1, m2) = Self::toom3_get_splits(d1, l);
        let (n0, n1, n2) = Self::toom3_get_splits(d2, l);

        let mut buf = DigitBuf::new(22*(l+1)*DIGIT_BIT_SIZE)?;
        buf.fill(0);
        let (buf1, rest) = buf.split_at_mut(l+1);
        let (buf2, rest) = rest.split_at_mut(l+1);
        let (buf3, rest) = rest.split_at_mut((l+1)*2);
        let (buf4, rest) = rest.split_at_mut((l+1)*2);
        let (buf5, rest) = rest.split_at_mut((l+1)*2);
        let (buf6, rest) = rest.split_at_mut((l+1)*2);
        let (buf7, rest) = rest.split_at_mut((l+1)*2);
        let (buf8, rest) = rest.split_at_mut(l+1);
        let (buf9, rest) = rest.split_at_mut(l+1);
        let (buf10, rest) = rest.split_at_mut(l+1);
        let (buf11, rest) = rest.split_at_mut((l+1)*2);
        let (buf12, rest) = rest.split_at_mut((l+1)*2);
        let (buf13, rest) = rest.split_at_mut((l+1)*2);
        let buf14 = rest;   // 2*(l+1)

        let mut x1 = SliceWithSign::new_mut(buf1, 1);
        let mut x2 = SliceWithSign::new_mut(buf2, 1);
        let mut p0 = SliceWithSign::new_mut(buf3, 1);
        let mut p1 = SliceWithSign::new_mut(buf4, 1);
        let mut p2 = SliceWithSign::new_mut(buf5, 1);
        let mut p3 = SliceWithSign::new_mut(buf6, 1);
        let mut p4 = SliceWithSign::new_mut(buf7, 1);
        let mut q1 = SliceWithSign::new_mut(buf8, 1);
        let mut q2 = SliceWithSign::new_mut(buf9, 1);
        let mut q3 = SliceWithSign::new_mut(buf10, 1);
        let mut w1 = SliceWithSign::new_mut(buf11, 1);
        let mut w2 = SliceWithSign::new_mut(buf12, 1);
        let mut w3 = SliceWithSign::new_mut(buf13, 1);

        m0.add(&m2, &mut x1);
        x1.add(&m1, &mut p1);
        x1.sub(&m1, &mut p2);
        p2.add(&m2, &mut x2);
        x2.shift_left(1);
        x2.sub(&m0, &mut p3);
        p0.copy_from(&m0);
        p4.copy_from(&m2);

        n0.add(&n2, &mut x1);
        x1.add(&n1, &mut q1);
        x1.sub(&n1, &mut q2);
        q2.add(&n2, &mut x2);
        x2.shift_left(1);
        x2.sub(&n0, &mut q3);
        let q0 = n0;
        let q4 = n2;

        if l < 256 {
            p0.mul_assign(&q0, buf14);
            p1.mul_assign(&q1, buf14);
            p2.mul_assign(&q2, buf14);
            p3.mul_assign(&q3, buf14);
            p4.mul_assign(&q4, buf14);
        } else {
            Self::toom3(&mut p0, &q0)?;
            Self::toom3(&mut p1, &q1)?;
            Self::toom3(&mut p2, &q2)?;
            Self::toom3(&mut p3, &q3)?;
            Self::toom3(&mut p4, &q4)?;
        }

        p3.sub(&p1, &mut w3);
        w3.div_by_digit(3);
        p1.sub(&p2, &mut w1);
        w1.shift_right(1);
        p2.sub(&p0, &mut w2);
        w3.sub_assign(&w2, buf14);
        w3.add_with_shift(&p4, 2);
        w3.shift_right(1);
        w2.add_assign(&w1, buf14);
        w2.sub_assign(&p4, buf14);
        w1.sub_assign(&w3, buf14);

        for (i, w) in [p0, w1, w2, w3, p4].iter().enumerate().rev() {
            let mut a = SliceWithSign::new_mut(&mut d1[i*l..], 1);
            a.add_assign(w, buf14);
        }
        Ok(())
    }
}