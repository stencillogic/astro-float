//! Toom-3 multiplication.

use crate::defs::DIGIT_BIT_SIZE;
use crate::defs::Error;
use crate::defs::Digit;
use crate::mantissa::Mantissa;
use crate::mantissa::buf::DigitBuf;

enum SliceWithSignType<'a> {
    Mut(&'a mut [Digit]),
    Immut(&'a [Digit])
}

// Slice of digits with sign.
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

    }

    fn sub<'b, 'c>(&self, s2: &SliceWithSign<'b>, dst: &mut SliceWithSign<'c>) {

    }

    fn add_assign<'c>(&mut self, s2: &SliceWithSign<'c>) {
        
    }

    fn sub_assign<'c>(&mut self, s2: &SliceWithSign<'c>) {
        
    }

    fn mul_assign<'c>(&mut self, s2: &SliceWithSign<'c>) {

    }

    fn shift_left(&mut self, shift: usize) {

    }

    fn shift_right(&mut self, shift: usize) {

    }

    fn div_by_digit(&mut self, d: Digit) {

    }

    fn add_with_shift<'c>(&mut self, s2: &SliceWithSign<'c>, shift: usize) {

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

        let mut buf = DigitBuf::new(21*(l+1)*DIGIT_BIT_SIZE)?;
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
        let buf13 = rest;   // 2*(l+1)

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

        p0.mul_assign(&q0);
        p1.mul_assign(&q1);
        p2.mul_assign(&q2);
        p3.mul_assign(&q3);
        p4.mul_assign(&q4);

        p3.sub(&p1, &mut w3);
        w3.div_by_digit(3);
        p1.sub(&p2, &mut w1);
        w1.shift_right(1);
        p2.sub(&p0, &mut w2);
        w3.sub_assign(&w2);
        w3.add_with_shift(&p4, 2);
        w3.shift_right(1);
        w2.add_assign(&w1);
        w2.sub_assign(&p4);
        w1.sub_assign(&w3);

        for (i, w) in [p0, w1, w2, w3, p4].iter().enumerate().rev() {
            let mut a = SliceWithSign::new_mut(&mut d1[i*l..], 1);
            a.add_assign(w);
        }
        Ok(())
    }
}