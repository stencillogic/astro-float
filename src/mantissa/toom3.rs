//! Toom-3 multiplication.

use crate::defs::Error;
use crate::defs::Word;
use crate::mantissa::Mantissa;
use crate::mantissa::buf::WordBuf;
use crate::mantissa::util::SliceWithSign;
use crate::mantissa::util::shift_slice_left_copy;


impl Mantissa {

    fn toom3_get_splits(m: &[Word], l: usize) -> (SliceWithSign, SliceWithSign, SliceWithSign) {

        let b11 = l.min(m.len());
        let b12 = l.min(m.len() - b11) + b11;
        let b13 = l.min(m.len() - b12) + b12;

        let m0 = &m[..b11];
        let m1 = &m[b11..b12];
        let m2 = &m[b12..b13];

        (SliceWithSign::new(m0, 1), SliceWithSign::new(m1, 1), SliceWithSign::new(m2, 1))
    }

    fn toom3_factors<'a, 'b>(params: (SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>), 
                    x1: &mut SliceWithSign<'b>,
                    buf1: &'a mut [Word], buf2: &'a mut [Word], buf3: &'a mut [Word]) 
                    -> (SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>, SliceWithSign<'a>) {

        let (m0, m1, m2) = params;

        let mut p1 = SliceWithSign::new_mut(buf1, 1);
        let mut p2 = SliceWithSign::new_mut(buf2, 1);
        let mut p3 = SliceWithSign::new_mut(buf3, 1);

        m0.add(&m2, x1);
        x1.add(&m1, &mut p1);
        x1.sub(&m1, &mut p2);

        p2.add(&m2, &mut p3);
        p3.shift_left(1);
        p3.sub_assign(&m0);

        (m0, p1, p2, p3, m2)
    }

    // Toom-3 multiplication.
    // d1 must contain input number + have reserve of d2.len() positions in addition for the output.
    // The result is placed in d1, and the sign is returned.
    pub(super) fn toom3(d1: &[Word], d2: &[Word], d3: &mut [Word]) -> Result<(), Error> {

        let l = (d1.len().max(d2.len()) + 2) / 3;

        let mut buf = WordBuf::new(25*(l+1))?;

        let (x1buf, rest) = buf.split_at_mut(l+1);
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
        let mut x3 = SliceWithSign::new_mut(x3buf, 1);

        let mut w1 = SliceWithSign::new_mut(w1buf, 1);
        let mut w2 = SliceWithSign::new_mut(w2buf, 1);
        let mut w3 = SliceWithSign::new_mut(w3buf, 1);

        let params0 = Self::toom3_get_splits(d1, l);
        let params1 = Self::toom3_get_splits(d2, l);

        let mut s0 = SliceWithSign::new_mut(&mut s0buf[..params0.0.len()+params1.0.len()], 1);
        let mut s1 = SliceWithSign::new_mut(s1buf, 1);
        let mut s2 = SliceWithSign::new_mut(s2buf, 1);
        let mut s3 = SliceWithSign::new_mut(s3buf, 1);
        let mut s4 = SliceWithSign::new_mut(&mut s4buf[..params0.2.len()+params1.2.len()], 1);

        let (p0, p1, p2, p3, p4) = Self::toom3_factors(params0, &mut x1, p1buf, p2buf, p3buf);

        let (q0, q1, q2, q3, q4) = Self::toom3_factors(params1, &mut x1, q1buf, q2buf, q3buf);

        debug_assert!(p1.len() + q1.len() == s1.len());
        debug_assert!(p2.len() + q2.len() == s2.len());
        debug_assert!(p3.len() + q3.len() == s3.len());

        Self::mul_unbalanced(&p0, &q0, &mut s0)?;
        Self::mul_unbalanced(&p1, &q1, &mut s1)?;
        Self::mul_unbalanced(&p2, &q2, &mut s2)?;
        Self::mul_unbalanced(&p3, &q3, &mut s3)?;
        Self::mul_unbalanced(&p4, &q4, &mut s4)?;

        s1.set_sign(p1.sign() * q1.sign());
        s2.set_sign(p2.sign() * q2.sign());
        s3.set_sign(p3.sign() * q3.sign());

        s3.sub(&s1, &mut w3);
        w3.div_by_word(3);
        s1.sub(&s2, &mut w1);
        w1.shift_right(1);
        s2.sub(&s0, &mut w2);
        w3.sub_assign(&w2);
        w3.set_sign(-w3.sign());
        shift_slice_left_copy(&s4, &mut x3, 2);
        w3.add_assign(&x3);
        w3.shift_right(1);
        w2.add_assign(&w1);
        w2.sub_assign(&s4);
        w1.sub_assign(&w3);

        let l4 = 4*l;

        d3[..s0.len()].copy_from_slice(&s0);
        if l4 < d3.len() {
            d3[s0.len()..l4].fill(0);

            if d3.len() < l4 + s4.len() {
                let ll = d3.len();
                d3[l4..].copy_from_slice(&s4[..ll-l4]);
            } else {
                d3[l4..l4 + s4.len()].copy_from_slice(&s4);
                d3[l4 + s4.len()..].fill(0);
            }
        } else {
            d3[s0.len()..].fill(0);
        }

        let w1s = w1.sign();
        let w2s = w1.sign();

        let mut parts = [(l, w1), (l*2, w2), (l*3, w3)];

        if w1s < 0 {
            parts.swap(0, 2);
        }
        if w2s < 0 {
            parts.swap(1, 2);
        }

        for (start, w) in &parts {
            if *start < d3.len() {
                let mut a = SliceWithSign::new_mut(&mut d3[*start..], 1);
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
    use crate::defs::DoubleWord;
    use crate::defs::WORD_BIT_SIZE;

    #[ignore]
    #[test]
    fn toom3_perf() {

        for _ in 0..5 {

            let sz = 220;
            let f = random_slice(sz, sz);
            let mut n = vec![];
            let mut ret = vec![];
            ret.resize(sz + f.len(), 0);
            let l = 10000;

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
        let s1 = [Word::MAX; 8];
        let s2 = [Word::MAX; 7];
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