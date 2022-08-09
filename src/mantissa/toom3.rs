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
        self.add_sub_assign(s2, 1, work_buf);
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
                let mut dst = self.deref_mut();
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

    fn mul_assign<'c, 'd>(&mut self, s2: &SliceWithSign<'c>, work_buf: &mut [Digit]) {
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

    fn shift_left(&mut self, shift: usize) {
        debug_assert!(shift < DIGIT_BIT_SIZE);
        let mut prev = 0;
        let rshift = DIGIT_BIT_SIZE - shift;
        for v in self.deref_mut().iter_mut() {
            let t = *v;
            *v = (t << shift) | (prev >> rshift);
            prev = t;
        }
        debug_assert!((prev >> rshift) == 0);
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
                break;
            }
        }
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
        let b13 = l.min(m.len() - b12) + b12;
        let m0 = &m[..b11];
        let m1 = &m[b11..b12];
        let m2 = &m[b12..b13];
        (SliceWithSign::new(m0, 1), SliceWithSign::new(m1, 1), SliceWithSign::new(m2, 1))
    }

    fn toom3_prepare_params<'a>(params: (SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>), l: usize, buf1: &'a mut [Digit], buf2: &'a [Digit]) -> (SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>) {
        let mut x1 = SliceWithSign::new_mut(buf1, 1);
        let x2 = SliceWithSign::new(buf2, 1);
        let x3 = SliceWithSign::new(buf2, 1);
        if params.0.deref().len() < l {
            x1.copy_from(&params.0);
            (x1, x2, x3)
        } else if params.1.deref().len() < l {
            x1.copy_from(&params.1);
            (params.0, x1, x2)
        } else if params.2.deref().len() < l {
            x1.copy_from(&params.2);
            (params.0, params.1, x1)
        } else {
            params
        }
    }

    // Toom-3 multiplication.
    // d1 must contain input number + have reserve of d2.len() positions in addition for the output.
    // The result is placed in d1, and the sign is returned.
    fn toom3(d1: &mut [Digit], d2: &[Digit]) -> Result<i8, Error> {

        let l = (d1.len() - d2.len()).max(d2.len());
        let l = if l%3 == 0 { l / 3 } else { l / 3 + 1 };
        let (m0, m1, m2) = Self::toom3_get_splits(d1, l);
        let (n0, n1, n2) = Self::toom3_get_splits(d2, l);

        let mut buf = DigitBuf::new(25*(l+1))?;
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
        let (buf14, rest) = rest.split_at_mut(l+1);
        let (buf15, rest) = rest.split_at_mut(l+1);
        let buf16 = rest;   // 2*(l+1)
        let buf15 = &(*buf15);

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

        let (m0, m1, m2) = Self::toom3_prepare_params((m0,m1,m2), l, buf14, buf15);

        m0.add(&m2, &mut x1);
        x1.add(&m1, &mut p1);
        x1.sub(&m1, &mut p2);
        p2.add(&m2, &mut x2);
        x2.shift_left(1);
        x2.sub(&m0, &mut p3);
        p0.copy_from(&m0);
        p4.copy_from(&m2);

        buf14.fill(0);
        let (n0, n1, n2) = Self::toom3_prepare_params((n0,n1,n2), l, buf14, buf15);

        x1.deref_mut().fill(0);
        x2.deref_mut().fill(0);
        n0.add(&n2, &mut x1);
        x1.add(&n1, &mut q1);
        x1.sub(&n1, &mut q2);
        q2.add(&n2, &mut x2);
        x2.shift_left(1);
        x2.sub(&n0, &mut q3);
        let q0 = n0;
        let q4 = n2;

        if l <= 256 {
            p0.mul_assign(&q0, buf16);
            p1.mul_assign(&q1, buf16);
            p2.mul_assign(&q2, buf16);
            p3.mul_assign(&q3, buf16);
            p4.mul_assign(&q4, buf16);
        } else {
            p0.sign *= Self::toom3(&mut p0, &q0)? * q0.sign;
            p1.sign *= Self::toom3(&mut p1, &q1)? * q1.sign;
            p2.sign *= Self::toom3(&mut p2, &q2)? * q2.sign;
            p3.sign *= Self::toom3(&mut p3, &q3)? * q3.sign;
            p4.sign *= Self::toom3(&mut p4, &q4)? * q4.sign;
        }

        buf16.fill(0);
        let mut x3 = SliceWithSign::new_mut(buf16, 1);
        p3.sub(&p1, &mut w3);
        w3.div_by_digit(3);
        p1.sub(&p2, &mut w1);
        w1.shift_right(1);
        p2.sub(&p0, &mut w2);
        buf4.fill(0);   // p1 not used further, let's reuse its buffer
        w3.sub_assign(&w2, buf4);
        w3.sign = -w3.sign;
        x3.copy_from(&p4);
        x3.shift_left(2);
        w3.add_assign(&x3, buf4);
        w3.shift_right(1);
        w2.add_assign(&w1, buf4);
        w2.sub_assign(&p4, buf4);
        w1.sub_assign(&w3, buf4);

        d1.fill(0);
        let d1len = d1.len();
        let mut sign = 1;
        for (i, w) in [p0, w1, w2, w3, p4].iter().enumerate() {
            let start = i*l;
            if start < d1len {
                let mut a = SliceWithSign::new_mut(&mut d1[start..], sign);
                let len = d1len - start;
                if w.len() > len {
                    a.add_assign(&SliceWithSign::new(&w[..len], w.sign), &mut buf16[..len]);
                } else {
                    a.add_assign(w, buf16);
                }
                sign = a.sign;
            }
        }
        Ok(sign)
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use rand::random;

    #[test]
    fn test_toom3() {

        let mut s1 = [32325439, 3157084656, 1940846527, 636874141, 731432345, 215781689, 11841131, 292926102, 3110062891, 2049545896, 3056399800, 217536740, 3115564791, 855825154, 2856674810, 2119217692, 337271047, 1387040184, 2287680423, 4085782669, 3048273246, 1571754795, 2014041111, 1574156240, 494708558, 4028365089, 2509206061, 4101089368, 1815707509, 1103712756, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let mut s2 = [4288599985, 1993425043, 3713765162, 378315979, 4186570953, 3695713351, 685881772, 2855025353, 2777377980, 693251457, 1414392347, 3232139466, 3787513323, 4250809159, 1398202442, 3636599798, 1435043072, 1031166858, 2806334256, 3046242060, 1968612920, 2608479000, 559581948, 815370191, 2333345657, 2064703478, 647872440, 1028106786, 3275523964, 4266614507];
        //------ ref [1594401679, 4025435177, 3872032686, 1082006611, 1191821903, 393876621, 1124100098, 681590019, 1238588406, 931188003, 2915971869, 3529553155, 235283209, 3139497253, 3261962557, 3658555223, 1161847181, 30897951, 277106709, 3393338275, 2381358366, 2324910733, 1996697543, 255151738, 661644278, 2683937772, 2805523683, 3222377358, 2253796897, 2111904295, 2204728747, 3049094907, 682618952, 1166529500, 358842457, 1258085382, 927290978, 1225087809, 3780273850, 1512785416, 4189307888, 2089143521, 123828443, 2211482432, 1505682670, 1414599565, 2714020077, 2046963890, 3694380217, 2148355927, 1293397105, 2253153404, 1636916399, 4291286091, 2784854512, 926120772, 3732057919, 1320724800, 1340101823, 1096426709]
        Mantissa::toom3(&mut s1, &s2).unwrap();

        // d1*d2
        let s1 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let s2 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let mut ref_s = [0; 36];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 36];
        ret_s[0..s1.len()].copy_from_slice(&s1);
        Mantissa::toom3(&mut ret_s, &s2).unwrap();

        assert!(ret_s == ref_s);


        // 999..99 * 999..99
        let s1 = [Digit::MAX; 8];
        let s2 = [Digit::MAX; 7];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        ret_s[0..s1.len()].copy_from_slice(&s1);
        Mantissa::toom3(&mut ret_s, &s2).unwrap();

        assert!(ret_s == ref_s);

        // d1*d2
        let s1 = [1, 2, 3, 4, 5, 6];
        let s2 = [0, 1, 2, 3, 4, 5, 6];
        let mut ref_s = [0; 13];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 13];
        ret_s[0..s1.len()].copy_from_slice(&s1);
        Mantissa::toom3(&mut ret_s, &s2).unwrap();

        assert!(ret_s == ref_s);

        // 0*0
        let s1 = [0, 0, 0, 0, 0, 0, 0, 0];
        let s2 = [0, 0, 0, 0, 0, 0, 0];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        ret_s[0..s1.len()].copy_from_slice(&s1);
        Mantissa::toom3(&mut ret_s, &s2).unwrap();

        assert!(ret_s == ref_s);

        // 1*1
        let s1 = [1, 0, 0, 0, 0, 0, 0, 0];
        let s2 = [1, 0, 0, 0, 0, 0, 0];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        ret_s[0..s1.len()].copy_from_slice(&s1);
        Mantissa::toom3(&mut ret_s, &s2).unwrap();

        assert!(ret_s == ref_s);

        // random
        for _ in 0..1000 {
            let mut s1 = random_slice(5, 100);
            let s2 = random_slice(5, 100);
            let mut ref_s = Vec::new();
            ref_s.resize(s1.len() + s2.len(), 0);
            mul(&s1, &s2, ref_s.as_mut_slice());

            s1.resize(s1.len() + s2.len(), 0);
            Mantissa::toom3(&mut s1, &s2).unwrap();
            assert!(s1 == ref_s);
        }

        // recursive
        for _ in 0..100 {
            let mut s1 = random_slice(1000, 2000);
            let s2 = random_slice(1000, 2000);
            let mut ref_s = Vec::new();
            ref_s.resize(s1.len() + s2.len(), 0);
            mul(&s1, &s2, ref_s.as_mut_slice());
    
            s1.resize(s1.len() + s2.len(), 0);
            Mantissa::toom3(&mut s1, &s2).unwrap();
            assert!(s1 == ref_s);
        }
    }

    fn random_slice(min_len: usize, max_len: usize) -> Vec<Digit> {
        let mut s1 = Vec::new();
        let l = if max_len > min_len {
            random::<usize>() % (max_len - min_len) + min_len
        } else {
            min_len
        };
        for _ in 0..l {
            s1.push(random());
        }
        s1
    }

    fn mul(s1: &[Digit], s2: &[Digit], ret: &mut [Digit]) {
        for (i, d1mi) in s1.iter().enumerate() {
            let d1mi = *d1mi as DoubleDigit;
            if d1mi == 0 {
                continue;
            }

            let mut k = 0;
            for (m2j, m3ij) in s2.deref().iter().zip(ret[i..].iter_mut()) {
                let m = d1mi * (*m2j as DoubleDigit) + *m3ij as DoubleDigit + k;

                *m3ij = m as Digit;
                k = m >> (DIGIT_BIT_SIZE);
            }
            ret[i + s2.len()] += k as Digit;
        }
    }
}