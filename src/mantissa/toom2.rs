//! Karatsuba multiplication.

use crate::defs::Error;
use crate::defs::Digit;
use crate::defs::DoubleDigit;
use crate::defs::DIGIT_BASE;
use crate::mantissa::Mantissa;
use crate::mantissa::buf::DigitBuf;
use itertools::izip;


impl Mantissa {

    fn add_slices(s1: &[Digit], s2: &[Digit], s3: &mut [Digit]) {

        let mut c = 0;

        let (mut iter1, mut iter2) = if s1.len() > s2.len() {
            (s1.iter(), s2.iter())
        } else {
            (s2.iter(), s1.iter())
        };
        let mut iter3 = s3.iter_mut();

        for (a, b, x) in izip!(iter2.by_ref(), iter1.by_ref(), iter3.by_ref()) {

            let mut s = c + *a as DoubleDigit + *b as DoubleDigit;

            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }

            *x = s as Digit;
        }

        for (a, x) in iter1.zip(iter3.by_ref()) {
    
            let mut s = c + *a as DoubleDigit;

            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }

            *x = s as Digit;
        }

        *iter3.next().unwrap() =  c as Digit;
    }

    fn paired_sub(s1: &[Digit], s2: &[Digit], s3: &mut [Digit]) {

        let mut c = 0;
        let mut iter3 = s3.iter_mut();

        let (mut iter1, mut iter2) = if s1.len() > s2.len() {
            (s1.iter(), s2.iter())
        } else {
            (s2.iter(), s1.iter())
        };

        for (a, b, x) in izip!(iter2.by_ref(), iter1.by_ref(), iter3.by_ref()) {

            let v = *x as DoubleDigit;
            let s = *a as DoubleDigit + *b as DoubleDigit + c;

            if v >= s {
                *x = (v - s) as Digit;
                c = 0;
            } else if v + DIGIT_BASE >= s {
                *x = (v + DIGIT_BASE - s) as Digit;
                c = 1;
            } else {
                *x = (v + DIGIT_BASE*2 - s) as Digit;
                c = 2;
            }
        }

        for (a, x) in iter1.zip(iter3.by_ref()) {

            let v = *x as DoubleDigit;
            let s = c + *a as DoubleDigit;

            if v >= s {
                *x = (v - s) as Digit;
                c = 0;
            } else {
                *x = (v + DIGIT_BASE - s) as Digit;
                c = 1;
            }
        }

        *iter3.next().unwrap() -= c as Digit;
    }

    fn add_assign_slices(s1: &mut [Digit], s2: &[Digit]) {

        let mut c = 0;

        let mut s3iter = s1.iter_mut();
        for (a, b) in s2.iter().zip(s3iter.by_ref()) {

            let mut s = c + *a as DoubleDigit + *b as DoubleDigit;

            if s >= DIGIT_BASE {
                s -= DIGIT_BASE;
                c = 1;
            } else {
                c = 0;
            }

            *b = s as Digit;
        }

        *s3iter.next().unwrap() += c as Digit;
    }

    pub(super) fn toom2(m1: &[Digit], m2: &[Digit], m3: &mut [Digit]) -> Result<(), Error> {

        let n = (m1.len().min(m2.len()) + 1) >> 1;
        let n2 = n << 1;

        let (m11, m12) = m1.split_at(n);
        let (m21, m22) = m2.split_at(n);
        let (m31, m32) = m3.split_at_mut(n2);

        let x1l = m11.len().max(m12.len()) + 1;
        let x2l = m21.len().max(m22.len()) + 1;
        let buf_sz = (x1l + x2l)*2;

        let mut buf_holder1;
        let mut buf_holder2;
        let buf = if buf_sz <= 256 {
            buf_holder2 = [0; 256];
            &mut buf_holder2[..buf_sz]
        } else {
            buf_holder1 = DigitBuf::new(buf_sz)?;
            &mut buf_holder1
        };
        
        let (x1, rest) = buf.split_at_mut(x1l);
        let (x2, rest) = rest.split_at_mut(x2l);
        let z2buf = rest;

        Self::add_slices(m11, m12, x1);
        Self::add_slices(m21, m22, x2);

        Self::mul_basic(x1, x2, z2buf);
        Self::mul_basic(m11, m21, m31);
        Self::mul_basic(m12, m22, m32);

        Self::paired_sub(m31, m32, z2buf);
        Self::add_assign_slices(&mut m3[n..], z2buf);

        Ok(())
    }
}


#[cfg(test)]
mod tests {

    use super::*;
    use rand::random;
    use crate::defs::{DoubleDigit, DIGIT_BIT_SIZE};

    
    #[test]
    fn test_toom2() {

        // d1*d2
        let s1 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let s2 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1];
        let mut ref_s = [0; 36];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 36];
        Mantissa::toom2(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 999..99 * 999..99
        let s1 = [Digit::MAX; 8];
        let s2 = [Digit::MAX; 7];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        Mantissa::toom2(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // d1*d2
        let s1 = [1, 2, 3, 4, 5, 6];
        let s2 = [0, 1, 2, 3, 4, 5, 6];
        let mut ref_s = [0; 13];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 13];
        Mantissa::toom2(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 0*0
        let s1 = [0, 0, 0, 0, 0, 0, 0, 0];
        let s2 = [0, 0, 0, 0, 0, 0, 0];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        Mantissa::toom2(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 1*1
        let s1 = [1, 0, 0, 0, 0, 0, 0, 0];
        let s2 = [1, 0, 0, 0, 0, 0, 0];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        Mantissa::toom2(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // random
        for _ in 0..10000 {
            let s1 = random_slice(80, 300);
            let s2 = random_slice(80, 300);
            let mut ref_s = Vec::new();
            ref_s.resize(s1.len() + s2.len(), 0);
            mul(&s1, &s2, &mut ref_s);

            let mut ret_s = Vec::new();
            ret_s.resize(s1.len() + s2.len(), 0);
            Mantissa::toom2(&s1, &s2, &mut ret_s).unwrap();

            //println!("s1 {:?}", s1);
            //println!("s2 {:?}", s2);

            assert!(ret_s == ref_s);
        }
    }


    #[ignore]
    #[test]
    fn toom2_perf() {

        for _ in 0..5 {
            let sz = 32;
            let f = random_slice(sz, sz);
            let mut n = vec![];
            let mut ret = vec![];
            ret.resize(sz + f.len(), 0);
            let l = 100000;
            for _ in 0..l {
                let v = random_slice(sz, sz);
                n.push(v);
            }
            
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                Mantissa::toom2(ni, &f, &mut ret).unwrap();
            }
            let time = start_time.elapsed();
            println!("toom2 {}", time.as_millis());

            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                mul(ni, &f, &mut ret);
            }
            let time = start_time.elapsed();
            println!("mul  {}", time.as_millis());
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
        ret.fill(0);
        for (i, d1mi) in s1.iter().enumerate() {
            let d1mi = *d1mi as DoubleDigit;
            if d1mi == 0 {
                continue;
            }

            let mut k = 0;
            for (m2j, m3ij) in s2.iter().zip(ret[i..].iter_mut()) {
                let m = d1mi * (*m2j as DoubleDigit) + *m3ij as DoubleDigit + k;

                *m3ij = m as Digit;
                k = m >> (DIGIT_BIT_SIZE);
            }
            ret[i + s2.len()] += k as Digit;
        }
    }
}