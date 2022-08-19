//! Toom-3 multiplication.

use crate::defs::Error;
use crate::defs::Digit;
use crate::mantissa::Mantissa;
use crate::mantissa::buf::DigitBuf;
use crate::mantissa::util::SliceWithSign;
use core::ops::DerefMut;
use core::ops::Deref;


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
    pub(super) fn toom3(d1: &mut [Digit], d2: &[Digit]) -> Result<i8, Error> {

        let l = (d1.len() - d2.len()).max(d2.len());
        let l = if l%3 == 0 { l / 3 } else { l / 3 + 1 };
        let params0 = Self::toom3_get_splits(d1, l);
        let params1 = Self::toom3_get_splits(d2, l);

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

        let (m0, m1, m2) = Self::toom3_prepare_params(params0, l, buf14, buf15);

        m0.add(&m2, &mut x1);
        x1.add(&m1, &mut p1);
        x1.sub(&m1, &mut p2);
        p2.add(&m2, &mut x2);
        x2.shift_left(1);
        x2.sub(&m0, &mut p3);
        p0.copy_from(&m0);
        p4.copy_from(&m2);

        buf14.fill(0);
        let (n0, n1, n2) = Self::toom3_prepare_params(params1, l, buf14, buf15);

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

        if l <= 70 {
            p0.mul_assign(&q0, buf16);
            p1.mul_assign(&q1, buf16);
            p2.mul_assign(&q2, buf16);
            p3.mul_assign(&q3, buf16);
            p4.mul_assign(&q4, buf16);
        } else {
            let s0 = Self::toom3(&mut p0, &q0)? * q0.sign() * p0.sign();
            let s1 = Self::toom3(&mut p1, &q1)? * q1.sign() * p1.sign();
            let s2 = Self::toom3(&mut p2, &q2)? * q2.sign() * p2.sign();
            let s3 = Self::toom3(&mut p3, &q3)? * q3.sign() * p3.sign();
            let s4 = Self::toom3(&mut p4, &q4)? * q4.sign() * p4.sign();
            p0.set_sign(s0);
            p1.set_sign(s1);
            p2.set_sign(s2);
            p3.set_sign(s3);
            p4.set_sign(s4);
        }

        buf16.fill(0);
        let mut x3 = SliceWithSign::new_mut(buf16, 1);
        p3.sub(&p1, &mut w3);
        w3.div_by_digit(3);
        p1.sub(&p2, &mut w1);
        w1.shift_right(1);
        p2.sub(&p0, &mut w2);
        w3.sub_assign(&w2);
        w3.set_sign(-w3.sign());
        x3.copy_from(&p4);
        x3.shift_left(2);
        w3.add_assign(&x3);
        w3.shift_right(1);
        w2.add_assign(&w1);
        w2.sub_assign(&p4);
        w1.sub_assign(&w3);

        d1.fill(0);
        let d1len = d1.len();
        let mut sign = 1;
        for (i, w) in [p0, w1, w2, w3, p4].iter().enumerate() {
            let start = i*l;
            if start < d1len {
                let mut a = SliceWithSign::new_mut(&mut d1[start..], sign);
                let len = d1len - start;
                if w.len() > len {
                    a.add_assign(&SliceWithSign::new(&w[..len], w.sign()));
                } else {
                    a.add_assign(w);
                }
                sign = a.sign();
            }
        }
        Ok(sign)
    }

    // Estimate the cost of multiplication with toom-3. 
    // Return true if toom-3 is better than plain multiplication.
    // l1 is supposed to be smaller or equal to l2.
    pub(super) fn toom3_cost_estimate(l1: usize, l2: usize) -> bool {
        if l1 < 70 && l2 < 70 {
            return false;
        }
        for (thrsh1, thrsh2) in [
            (120, 210),
            (200, 630),
            (340, 1890),
            (580, 5670),
            (900, 17010),
            (1500, 51030)]
        {
            if l2 < thrsh2 {
                return l1 >= thrsh1;
            }
        }
        let mut thrsh2 = 51030;
        let mut thrsh1 = 1500;
        while thrsh2 < usize::MAX / 3 {
            thrsh2 *= 3;
            thrsh1 *= 16;
            thrsh1 /= 10;
            if l2 < thrsh2 {
                return l1 >= thrsh1;
            }
        }
        false
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use rand::random;
    use crate::defs::DoubleDigit;
    use crate::defs::DIGIT_BIT_SIZE;

    #[ignore]
    #[test]
    fn toom3_perf() {

        for _ in 0..5 {
            let sz = 3840;
            let f = random_slice(459270, 459270);
            let mut n = vec![];
            let l = 2;
            for _ in 0..l {
                let mut v = random_slice(sz, sz);
                v.resize(v.len() + f.len(), 0);
                n.push(v);
            }
            
            let start_time = std::time::Instant::now();
            for mut ni in n.drain(..) {
                Mantissa::toom3(&mut ni, &f).unwrap();
            }
            let time = start_time.elapsed();
            println!("toom {}", time.as_millis());

            let mut ret = vec![];
            ret.resize(sz + f.len(), 0);
            for _ in 0..l {
                n.push(random_slice(sz, sz));
            }

            let start_time = std::time::Instant::now();
            for ni in n.drain(..) {
                mul(&ni, &f, &mut ret);
            }
            let time = start_time.elapsed();
            println!("mul  {}", time.as_millis());
        }
    }

    #[test]
    fn test_toom3() {

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