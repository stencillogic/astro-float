//! Toom-3 multiplication.

use crate::defs::Error;
use crate::defs::Digit;
use crate::mantissa::Mantissa;
use crate::mantissa::buf::DigitBuf;
use crate::mantissa::util::SliceWithSign;


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

    fn toom3_factors<'a, 'b>(params: (SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>), 
                    x1: &mut SliceWithSign<'b>, x2: &mut SliceWithSign<'b>,
                    buf1: &'a mut [Digit], buf2: &'a mut [Digit], buf3: &'a mut [Digit]) 
                    -> (SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>) {

        let (m0, m1, m2) = params;
        let mut p1 = SliceWithSign::new_mut(buf1, 1);
        let mut p2 = SliceWithSign::new_mut(buf2, 1);
        let mut p3 = SliceWithSign::new_mut(buf3, 1);

        m0.add(&m2, x1);
        x1.add(&m1, &mut p1);
        x1.sub(&m1, &mut p2);

        p2.add(&m2, x2);
        x2.shift_left(1);
        x2.sub(&m0, &mut p3);

        (m0, p1, p2, p3, m2)
    }

    // Toom-3 multiplication.
    // d1 must contain input number + have reserve of d2.len() positions in addition for the output.
    // The result is placed in d1, and the sign is returned.
    pub(super) fn toom3(d1: &[Digit], d2: &[Digit], d3: &mut [Digit]) -> Result<(), Error> {

        let l = (d1.len().max(d2.len()) + 2) / 3;

        let mut buf = DigitBuf::new(26*(l+1))?;

        let (x1buf, rest) = buf.split_at_mut(l+1);
        let (x2buf, rest) = rest.split_at_mut(l+1);
        let (x3buf, rest) = rest.split_at_mut(2*(l+1));

        let (p1buf, rest) = rest.split_at_mut(l+1);
        let (p2buf, rest) = rest.split_at_mut(l+1);
        let (p3buf, rest) = rest.split_at_mut(l+1);

        let (q1buf, rest) = rest.split_at_mut(l+1);
        let (q2buf, rest) = rest.split_at_mut(l+1);
        let (q3buf, rest) = rest.split_at_mut(l+1);

        let (w1buf, rest) = rest.split_at_mut((l+1)*2);
        let (w2buf, rest) = rest.split_at_mut((l+1)*2);
        let (w3buf, rest) = rest.split_at_mut((l+1)*2);

        let (s0buf, rest) = rest.split_at_mut((l+1)*2);
        let (s1buf, rest) = rest.split_at_mut((l+1)*2);
        let (s2buf, rest) = rest.split_at_mut((l+1)*2);
        let (s3buf, rest) = rest.split_at_mut((l+1)*2);
        let s4buf = rest; // (l+1)*2

        let mut x1 = SliceWithSign::new_mut(x1buf, 1);
        let mut x2 = SliceWithSign::new_mut(x2buf, 1);
        let mut x3 = SliceWithSign::new_mut(x3buf, 1);

        let mut w1 = SliceWithSign::new_mut(w1buf, 1);
        let mut w2 = SliceWithSign::new_mut(w2buf, 1);
        let mut w3 = SliceWithSign::new_mut(w3buf, 1);

        let mut s0 = SliceWithSign::new_mut(s0buf, 1);
        let mut s1 = SliceWithSign::new_mut(s1buf, 1);
        let mut s2 = SliceWithSign::new_mut(s2buf, 1);
        let mut s3 = SliceWithSign::new_mut(s3buf, 1);
        let mut s4 = SliceWithSign::new_mut(s4buf, 1);

        let params0 = Self::toom3_get_splits(d1, l);
        let params1 = Self::toom3_get_splits(d2, l);

        let (p0, p1, p2, p3, p4) = Self::toom3_factors(params0, &mut x1, &mut x2, p1buf, p2buf, p3buf);

        let (q0, q1, q2, q3, q4) = Self::toom3_factors(params1, &mut x1, &mut x2, q1buf, q2buf, q3buf);

        debug_assert!(p1.len() + q1.len() == s1.len());
        debug_assert!(p2.len() + q2.len() == s2.len());
        debug_assert!(p3.len() + q3.len() == s3.len());

        let t = p0.len() + q0.len();
        if t < s0.len() {
            s0[t..].fill(0);
        }

        let t = p4.len() + q4.len();
        if t < s4.len() {
            s4[t..].fill(0);
        }

        Self::mul_unbalanced(&p0, &q0, &mut s0)?;
        Self::mul_unbalanced(&p1, &q1, &mut s1)?;
        Self::mul_unbalanced(&p2, &q2, &mut s2)?;
        Self::mul_unbalanced(&p3, &q3, &mut s3)?;
        Self::mul_unbalanced(&p4, &q4, &mut s4)?;

        s0.set_sign(p0.sign() * q0.sign());
        s1.set_sign(p1.sign() * q1.sign());
        s2.set_sign(p2.sign() * q2.sign());
        s3.set_sign(p3.sign() * q3.sign());
        s4.set_sign(p4.sign() * q4.sign());

        s3.sub(&s1, &mut w3);
        w3.div_by_digit(3);
        s1.sub(&s2, &mut w1);
        w1.shift_right(1);
        s2.sub(&s0, &mut w2);
        w3.sub_assign(&w2);
        w3.set_sign(-w3.sign());
        x3.copy_from(&s4);
        x3.shift_left(2);
        w3.add_assign(&x3);
        w3.shift_right(1);
        w2.add_assign(&w1);
        w2.sub_assign(&s4);
        w1.sub_assign(&w3);

        let w1s = w1.sign();
        let w2s = w1.sign();

        let mut parts = [(4, s4), (0, s0), (1, w1), (2, w2), (3, w3)];

        if w1s < 0 {
            parts.swap(2, 4);
        }
        if w2s < 0 {
            parts.swap(3, 4);
        }

        d3.fill(0);
        for (i, w) in &parts {
            let start = i*l;
            if start < d3.len() {
                let mut a = SliceWithSign::new_mut(&mut d3[start..], 1);
                a.add_assign(w);
            }
        }

        Ok(())
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

            let sz = 256;
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
            for ni in &n {
                Mantissa::toom3(ni, &f, &mut ret).unwrap();
            }
            let time = start_time.elapsed();
            println!("toom3 {}", time.as_millis());

            let start_time = std::time::Instant::now();
            for ni in &n {
                Mantissa::mul_unbalanced(ni, &f, &mut ret).unwrap();
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
        Mantissa::toom3(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);


        // 999..99 * 999..99
        let s1 = [Digit::MAX; 8];
        let s2 = [Digit::MAX; 7];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        Mantissa::toom3(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // d1*d2
        let s1 = [1, 2, 3, 4, 5, 6];
        let s2 = [0, 1, 2, 3, 4, 5, 6];
        let mut ref_s = [0; 13];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 13];
        Mantissa::toom3(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 0*0
        let s1 = [0, 0, 0, 0, 0, 0, 0, 0];
        let s2 = [0, 0, 0, 0, 0, 0, 0];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        Mantissa::toom3(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 1*1
        let s1 = [1, 0, 0, 0, 0, 0, 0, 0];
        let s2 = [1, 0, 0, 0, 0, 0, 0];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        Mantissa::toom3(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // random
        for _ in 0..1000 {
            let s1 = random_slice(5, 20);
            let s2 = random_slice(5, 20);

            //println!("let s1 = {:?};", s1);
            //println!("let s2 = {:?};", s2);

            let mut ref_s = Vec::new();
            ref_s.resize(s1.len() + s2.len(), 0);
            mul(&s1, &s2, ref_s.as_mut_slice());

            let mut ret_s = Vec::new();
            ret_s.resize(s1.len() + s2.len(), 0);
            Mantissa::toom3(&s1, &s2, &mut ret_s).unwrap();

            assert!(ret_s == ref_s);
        }

        // recursive
        for _ in 0..100 {
            let s1 = random_slice(500, 1000);
            let s2 = random_slice(500, 1000);

            //println!("let s1 = {:?};", s1);
            //println!("let s2 = {:?};", s2);

            let mut ref_s = Vec::new();
            ref_s.resize(s1.len() + s2.len(), 0);
            mul(&s1, &s2, ref_s.as_mut_slice());
    
            let mut ret_s = Vec::new();
            ret_s.resize(s1.len() + s2.len(), 0);
            Mantissa::toom3(&s1, &s2, &mut ret_s).unwrap();
            assert!(ret_s == ref_s);
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