//! Multiplication algos.

use crate::defs::DIGIT_BIT_SIZE;
use crate::defs::Error;
use crate::defs::Digit;
use crate::defs::DoubleDigit;
use crate::mantissa::Mantissa;
use crate::mantissa::buf::DigitBuf;
use crate::mantissa::util::SliceWithSign;


impl Mantissa {

    fn mul_basic(m1: &[Digit], m2: &[Digit], m3: &mut [Digit]) {
        // TODO: consider multiplying by the lowest and the highest word and 
        // assigning result to m3 first to avoid filling with zeroes.
        m3.fill(0);
        for (i, d1mi) in m1.iter().enumerate() {
            let d1mi = *d1mi as DoubleDigit;
            if d1mi == 0 {
                continue;
            }
            let mut k = 0;
            for (m2j, m3ij) in m2.iter().zip(m3[i..].iter_mut()) {
                let m = d1mi * (*m2j as DoubleDigit) + *m3ij as DoubleDigit + k;
                *m3ij = m as Digit;
                k = m >> (DIGIT_BIT_SIZE);
            }
            m3[i + m2.len()] += k as Digit;
        }
    }

    // general case multiplication: quardric or toom-3
    pub(super) fn mul_slices(m1: &[Digit], m2: &[Digit], m3: &mut [Digit]) -> Result<(), Error> {
        let (sm, lg) = if m1.len() < m2.len() {
            (m1, m2)
        } else {
            (m2, m1)
        };
        if Self::toom3_cost_estimate(sm.len(), lg.len()) {
            // toom-3
            m3[..sm.len()].copy_from_slice(sm);
            m3[sm.len()..].fill(0);
            let sign = Self::toom3(m3, lg)?;
            debug_assert!(sign > 0);
        } else {
            // plain multiplication
            Self::mul_basic(m1, m2, m3)
        }
        Ok(())
    }

    // short multiplication
    #[allow(dead_code)] // TODO: can it be faster than just mul_slices ? 
    pub(super) fn mul_short(m1: &[Digit], m2: &[Digit], m3: &mut [Digit]) -> Result<(), Error> {
        debug_assert!(m1.len() == m2.len());    // TODO: consider relaxing this
        let n = m1.len();
        Self::mul_short_step(m1, m2, m3, n)
    }

    
    // short multiplication
    fn mul_short_step(m1: &[Digit], m2: &[Digit], m3: &mut [Digit], n: usize) -> Result<(), Error> {
        if n <= 1000 {
            Self::mul_slices(m1, m2, m3)?;
            let mut c1 = SliceWithSign::new_mut(m3, 1);
            c1.shift_right(n*DIGIT_BIT_SIZE);
        } else {
            let k = n*775/1000;
            let l = n - k;

            let a1 = SliceWithSign::new(&m1[l..], 1);  // m1 div 2^l
            let a2 = SliceWithSign::new(&m1[..l], 1);  // m1 mod 2^l
            let a3 = SliceWithSign::new(&m1[k..], 1);  // m1 div 2^k

            let b1 = SliceWithSign::new(&m2[l..], 1);  // m2 div 2^l
            let b2 = SliceWithSign::new(&m2[..l], 1);  // m2 mod 2^l
            let b3 = SliceWithSign::new(&m2[k..], 1);  // m2 div 2^k

            Self::mul_slices(&a1, &b1, m3)?;
            let mut c1 = SliceWithSign::new_mut(m3, 1);
            c1.shift_right((k-l)*DIGIT_BIT_SIZE);

            let mut tmp_buf = DigitBuf::new(a2.len() + b3.len() + a3.len() + b2.len())?;
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

    use crate::defs::DIGIT_MAX;
    use super::*;
    use rand::random;
    
    #[test]
    fn test_mul_short() {
        let s1 = [1,2,3,4];
        let s2 = [1,2,3,4];
        let mut s3 = [0,0,0,0,0,0,0,0];

        Mantissa::mul_short(&s1, &s2, &mut s3).unwrap();

        assert!(s3 == [25,24,16,0,0,0,0,0]);

        let s1=[1496867450, 1417658947, 3271802710, 2677751033, 3237139020, 3064555062, 1548441171, 778455770, 2436515277, 483318499];
        let s2=[3225363533, 3760565749, 1879799765, 4055875449, 305072033, 1248705486, 102752588, 2971455321, 1010393078, 2764359410];

        let mut ret = DigitBuf::new(20).unwrap();
        Mantissa::mul_short(&s1, &s2, &mut ret).unwrap();

        let mut s3 = DigitBuf::new(20).unwrap();
        Mantissa::mul_slices(&s1, &s2, &mut s3).unwrap();

        ret[0] &= DIGIT_MAX<<10; // 10 = ceil(log2(3*(p-1)))
        s3[10] &= DIGIT_MAX<<10;
        assert!(ret[..10] == s3[10..]);
    }


    #[ignore]
    #[test]
    fn test_mul_short_perf() {

        for _ in 0..5 {
            let sz1 = 10000;
            let sz2 = 10000;
            let f = random_slice(sz1, sz1);
            let mut ret = DigitBuf::new(sz1 + sz2).unwrap();
            let mut n = vec![];
            let l = 10;
            for _ in 0..l {
                let v = random_slice(sz2, sz2);
                n.push(v);
            }
            
            // basic
            let start_time = std::time::Instant::now();
            for ni in &n {
                Mantissa::mul_slices(&f, ni, &mut ret).unwrap();
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
}