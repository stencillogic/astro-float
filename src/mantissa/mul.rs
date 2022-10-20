//! Multiplication algos.

use crate::defs::WORD_BIT_SIZE;
use crate::defs::Error;
use crate::defs::Word;
use crate::defs::DoubleWord;
use crate::mantissa::Mantissa;
use crate::common::buf::WordBuf;
use crate::common::int::SliceWithSign;


impl Mantissa {

    fn mul_basic(m1: &[Word], m2: &[Word], m3: &mut [Word]) {

        m3.fill(0);
        
        for (i, d1mi) in m1.iter().enumerate() {

            let d1mi = *d1mi as DoubleWord;
            if d1mi == 0 {
                continue;
            }

            let mut k = 0;
            for (m2j, m3ij) in m2.iter().zip(m3[i..].iter_mut()) {
                let m = d1mi * (*m2j as DoubleWord) + *m3ij as DoubleWord + k;
                *m3ij = m as Word;
                k = m >> (WORD_BIT_SIZE);
            }

            m3[i + m2.len()] += k as Word;
        }
    }

    fn mul_slices(m1: &[Word], m2: &[Word], m3: &mut [Word]) -> Result<(), Error> {

        debug_assert!(m1.len() <= m2.len());

        if m1.len() <= 32 || m2.len() <= 32 {

            Self::mul_basic(m1, m2, m3);

        } else if m1.len() <= 220 || m2.len() <= 220 {

            Self::toom2(m1, m2, m3)?;

        } else if m1.len() <= 5400 && m2.len() <= 5400 {
            
            Self::toom3(m1, m2, m3)?;

        } else {
            
            Mantissa::fft_mul(m1, m2, m3)?;

        }
        Ok(())
    }

    // general case multiplication
    pub(super) fn mul_unbalanced(m1: &[Word], m2: &[Word], m3: &mut [Word]) -> Result<(), Error> {
        
        let (sm, lg) = if m1.len() < m2.len() {
            (m1, m2)
        } else {
            (m2, m1)
        };

        if lg.len()/2 >= sm.len() && sm.len() > 70 {

            // balancing
            
            let mut buf = WordBuf::new(2*sm.len())?;
            let mut even = true;
            let mut lb = 0;
            let mut ub = 0;

            for _ in 0..2 {

                while lb < lg.len() {

                    ub = if lb + sm.len() <= lg.len() {
                        lb + sm.len()
                    } else {
                        lg.len()
                    };

                    Self::mul_slices(&lg[lb..ub], sm, &mut buf)?;

                    let src = SliceWithSign::new(&buf[..ub - lb + sm.len()], 1);
                    let mut dst = SliceWithSign::new_mut(&mut m3[lb..], 1);

                    if even {
                        dst.copy_from(&src);
                    } else {
                        dst.add_assign(&src);
                    }

                    lb += sm.len()*2;
                }

                if even {

                    if ub + sm.len() < m3.len() {
                        m3[ub + sm.len()..].fill(0);
                    }

                    even = false;
                    lb = sm.len();
                }
            }

            Ok(())

        } else {

            Self::mul_slices(sm, lg, m3)
        }
    }

    // short multiplication
    #[allow(dead_code)] // TODO: can it be faster than mul_unbalanced by more than 90% ?
    pub(super) fn mul_short(m1: &[Word], m2: &[Word], m3: &mut [Word]) -> Result<(), Error> {
        debug_assert!(m1.len() == m2.len());    // TODO: consider relaxing this
        let n = m1.len();
        Self::mul_short_step(m1, m2, m3, n)
    }

    
    // short multiplication
    fn mul_short_step(m1: &[Word], m2: &[Word], m3: &mut [Word], n: usize) -> Result<(), Error> {
        if n <= 10 {

            Self::mul_unbalanced(m1, m2, m3)?;

            let mut c1 = SliceWithSign::new_mut(m3, 1);
            c1.shift_right(n*WORD_BIT_SIZE);

        } else {
            let k = n * 775 / 1000;
            let l = n - k;

            let a1 = SliceWithSign::new(&m1[l..], 1);  // m1 div 2^l
            let a2 = SliceWithSign::new(&m1[..l], 1);  // m1 mod 2^l
            let a3 = SliceWithSign::new(&m1[k..], 1);  // m1 div 2^k

            let b1 = SliceWithSign::new(&m2[l..], 1);  // m2 div 2^l
            let b2 = SliceWithSign::new(&m2[..l], 1);  // m2 mod 2^l
            let b3 = SliceWithSign::new(&m2[k..], 1);  // m2 div 2^k

            Self::mul_unbalanced(&a1, &b1, m3)?;

            let mut c1 = SliceWithSign::new_mut(m3, 1);
            c1.shift_right((k-l)*WORD_BIT_SIZE);

            let mut tmp_buf = WordBuf::new(a2.len() + b3.len() + a3.len() + b2.len())?;
            let (buf1, buf2) = tmp_buf.split_at_mut(a2.len() + b3.len());

            Self::mul_short_step(&a2, &b3, buf1, l)?;
            let c2 = SliceWithSign::new(buf1, 1);

            Self::mul_short_step(&a3, &b2, buf2, l)?;
            let c3 = SliceWithSign::new(buf2, 1);

            c1.add_assign(&c2);
            c1.add_assign(&c3);
        }

        Ok(())
    }
}


#[cfg(test)]
mod tests {

    use crate::defs::WORD_MAX;
    use super::*;
    use rand::random;

    #[cfg(not(feature="std"))]
    use alloc::vec::Vec;

    #[test]
    fn test_mul_unbalanced() {
        let sz1 = random::<usize>()%10 + 1;
        let sz2 = random::<usize>()%10*sz1 + random::<usize>()%sz1 + sz1;
        let f = random_slice(1, sz1);
        let mut ret1 = WordBuf::new(sz1 + sz2).unwrap();
        let mut ret2 = WordBuf::new(sz1 + sz2).unwrap();
        for _ in 0..1000 {
            let v = random_slice(sz1, sz2);
            Mantissa::mul_unbalanced(&f, &v, &mut ret1).unwrap();
            Mantissa::mul_slices(&f, &v, &mut ret2).unwrap();
            assert!(ret1[..] == ret2[..]);
        }
    }

    #[ignore]
    #[test]
    fn test_mul_short() {
        let s1 = [1,2,3,4];
        let s2 = [1,2,3,4];
        let mut s3 = [0,0,0,0,0,0,0,0];

        Mantissa::mul_short(&s1, &s2, &mut s3).unwrap();

        assert!(s3 == [25,24,16,0,0,0,0,0]);

        let s1=[1496867450, 1417658947, 3271802710, 2677751033, 3237139020, 3064555062, 1548441171, 778455770, 2436515277, 483318499];
        let s2=[3225363533, 3760565749, 1879799765, 4055875449, 305072033, 1248705486, 102752588, 2971455321, 1010393078, 2764359410];

        let mut ret = WordBuf::new(20).unwrap();
        Mantissa::mul_short(&s1, &s2, &mut ret).unwrap();

        let mut s3 = WordBuf::new(20).unwrap();
        Mantissa::mul_unbalanced(&s1, &s2, &mut s3).unwrap();

        ret[0] &= WORD_MAX<<10; // 10 = ceil(log2(3*(p-1)))
        s3[10] &= WORD_MAX<<10;
        assert!(ret[..10] == s3[10..]);
    }

    #[ignore]
    #[test]
    #[cfg(feature="std")]
    fn test_mul_short_perf() {

        for _ in 0..5 {
            let sz1 = 1000;
            let sz2 = 1000;
            let f = random_slice(sz1, sz1);
            let mut ret = WordBuf::new(sz1 + sz2).unwrap();
            let mut n = vec![];
            let l = 1000;
            for _ in 0..l {
                let v = random_slice(sz2, sz2);
                n.push(v);
            }
            
            // basic
            let start_time = std::time::Instant::now();
            for ni in &n {
                Mantissa::mul_unbalanced(&f, ni, &mut ret).unwrap();
            }
            let time = start_time.elapsed();
            println!("mul_slices {}", time.as_millis());
            
            // short
            let start_time = std::time::Instant::now();
            for ni in &n {
                Mantissa::mul_short(&f, ni, &mut ret).unwrap();
            }
            let time = start_time.elapsed();
            println!("mul_short {}", time.as_millis());
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
}