//! Karatsuba multiplication.

use crate::common::buf::WordBuf;
use crate::common::util::add_carry;
use crate::defs::DoubleWord;
use crate::defs::Error;
use crate::defs::Word;
use crate::defs::WORD_BASE;
use crate::mantissa::Mantissa;
use itertools::izip;

impl Mantissa {
    fn add_slices(s1: &[Word], s2: &[Word], s3: &mut [Word]) {
        let mut c = 0;

        let (mut iter1, mut iter2) = if s1.len() > s2.len() {
            (s1.iter(), s2.iter())
        } else {
            (s2.iter(), s1.iter())
        };
        let mut iter3 = s3.iter_mut();

        for (a, b, x) in izip!(iter2.by_ref(), iter1.by_ref(), iter3.by_ref()) {
            c = add_carry(*a, *b, c, x);
        }

        for (a, x) in iter1.zip(iter3.by_ref()) {
            c = add_carry(*a, 0, c, x);
        }

        *iter3.next().unwrap() = c as Word; // s3 is supposed to be longer than s1 and s2 to process carry.
    }

    fn paired_sub(s1: &[Word], s2: &[Word], s3: &mut [Word]) {
        let mut c = 0;
        let mut iter3 = s3.iter_mut();

        let (mut iter1, iter2) = if s1.len() > s2.len() {
            (s1.iter(), s2.iter())
        } else {
            (s2.iter(), s1.iter())
        };

        for (a, b, x) in izip!(iter2, iter1.by_ref(), iter3.by_ref()) {
            let v = *x as DoubleWord;
            let s = *a as DoubleWord + *b as DoubleWord + c;

            if v >= s {
                *x = (v - s) as Word;
                c = 0;
            } else if v + WORD_BASE >= s {
                *x = (v + WORD_BASE - s) as Word;
                c = 1;
            } else {
                *x = (v + WORD_BASE * 2 - s) as Word;
                c = 2;
            }
        }

        for (a, x) in iter1.zip(iter3.by_ref()) {
            let v = *x as DoubleWord;
            let s = *a as DoubleWord + c;

            if v >= s {
                *x = (v - s) as Word;
                c = 0;
            } else if v + WORD_BASE >= s {
                *x = (v + WORD_BASE - s) as Word;
                c = 1;
            } else {
                *x = (v + WORD_BASE * 2 - s) as Word;
                c = 2;
            }
        }

        if c > 0 {
            for x in iter3 {
                let v = *x as DoubleWord;
                let s = c;

                if v >= s {
                    *x = (v - s) as Word;
                    c = 0;
                } else if v + WORD_BASE >= s {
                    *x = (v + WORD_BASE - s) as Word;
                    c = 1;
                } else {
                    *x = (v + WORD_BASE * 2 - s) as Word;
                    c = 2;
                }
            }
        }
    }

    fn add_assign_slices(s1: &mut [Word], s2: &[Word]) {
        let mut c = 0;

        let mut s3iter = s1.iter_mut();
        for (a, b) in s2.iter().zip(s3iter.by_ref()) {
            c = add_carry(*a, *b, c, b);
        }

        if c > 0 {
            for b in s3iter {
                c = add_carry(0, *b, c, b);
            }
        }
    }

    pub(super) fn toom2(m1: &[Word], m2: &[Word], m3: &mut [Word]) -> Result<(), Error> {
        let n = (m1.len().min(m2.len()) + 1) >> 1;
        let n2 = n << 1;

        let (m11, m12) = m1.split_at(n);
        let (m21, m22) = m2.split_at(n);
        let (m31, m32) = m3.split_at_mut(n2);

        let x1l = m11.len().max(m12.len()) + 1;
        let x2l = m21.len().max(m22.len()) + 1;
        let buf_sz = (x1l + x2l) * 2;

        let mut buf_holder1;
        let mut buf_holder2;
        let buf = if buf_sz <= 256 {
            buf_holder2 = [0; 256];
            &mut buf_holder2[..buf_sz]
        } else {
            buf_holder1 = WordBuf::new(buf_sz)?;
            &mut buf_holder1
        };

        let (x1, rest) = buf.split_at_mut(x1l);
        let (x2, rest) = rest.split_at_mut(x2l);
        let z2buf = rest;

        Self::add_slices(m11, m12, x1);
        Self::add_slices(m21, m22, x2);

        Self::mul_unbalanced(x1, x2, z2buf)?;
        Self::mul_unbalanced(m11, m21, m31)?;
        Self::mul_unbalanced(m12, m22, m32)?;

        Self::paired_sub(m31, m32, z2buf);
        Self::add_assign_slices(&mut m3[n..], z2buf);

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::{DoubleWord, WORD_BIT_SIZE};
    use rand::random;

    #[cfg(not(feature = "std"))]
    use alloc::vec::Vec;

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
        let s1 = [Word::MAX; 8];
        let s2 = [Word::MAX; 7];
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
        for _ in 0..1000 {
            let s1 = random_slice(80, 300);
            let s2 = random_slice(80, 300);

            //println!("s1 {:?}", s1);
            //println!("s2 {:?}", s2);

            let mut ref_s = Vec::new();
            ref_s.resize(s1.len() + s2.len(), 0);
            mul(&s1, &s2, &mut ref_s);

            let mut ret_s = Vec::new();
            ret_s.resize(s1.len() + s2.len(), 0);
            Mantissa::toom2(&s1, &s2, &mut ret_s).unwrap();

            assert!(ret_s == ref_s);
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn toom2_perf() {
        for _ in 0..5 {
            let sz = 34;
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

    fn random_slice(min_len: usize, max_len: usize) -> Vec<Word> {
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

    fn mul(s1: &[Word], s2: &[Word], ret: &mut [Word]) {
        ret.fill(0);
        for (i, d1mi) in s1.iter().enumerate() {
            let d1mi = *d1mi as DoubleWord;
            if d1mi == 0 {
                continue;
            }

            let mut k = 0;
            for (m2j, m3ij) in s2.iter().zip(ret[i..].iter_mut()) {
                let m = d1mi * (*m2j as DoubleWord) + *m3ij as DoubleWord + k;

                *m3ij = m as Word;
                k = m >> (WORD_BIT_SIZE);
            }
            ret[i + s2.len()] += k as Word;
        }
    }
}
