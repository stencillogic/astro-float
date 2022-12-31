//! Division algos.

use crate::common::buf::WordBuf;
use crate::common::int::SliceWithSign;
use crate::common::util::add_carry;
use crate::common::util::log2_ceil;
use crate::defs::DoubleWord;
use crate::defs::Error;
use crate::defs::Word;
use crate::defs::WORD_BASE;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_SIGNIFICANT_BIT;
use crate::mantissa::Mantissa;

impl Mantissa {
    // Basic integer division.
    fn div_basic(m1: &[Word], m2: &[Word]) -> Result<(WordBuf, WordBuf), Error> {
        debug_assert!(m1.len() >= m2.len());
        debug_assert!(!m2.is_empty());

        let l1 = m1.len();
        let l2 = m2.len();
        let mut c: DoubleWord;
        let mut j: usize;
        let mut qh: DoubleWord;
        let mut k: DoubleWord;
        let mut rh: DoubleWord;
        let mut buf = WordBuf::new(l1 + l2 + 2)?;
        let (buf1, buf2) = (&mut buf).split_at_mut(l1 + 1);
        let n = l2 - 1;
        let m = l1 - 1;
        let mut m3 = WordBuf::new(m - n + 1)?;
        let mut rem = WordBuf::new(l2)?;

        if n == 0 {
            // division by single word
            let d = m2[0] as DoubleWord;
            rh = 0;
            let mut j = l1 - l2 + 1;
            let mut iter = m1.iter().rev();
            let mut val = *iter.next().unwrap_or(&0) as DoubleWord;
            let mut m3iter = m3.iter_mut().rev();
            if val < d {
                rh = val;
                val = *iter.next().unwrap_or(&0) as DoubleWord;
                *m3iter.next().unwrap() = 0; // m3 is at least 1 word long.
                rem[0] = rh as Word;
                j -= 1;
            }

            if j > 0 {
                loop {
                    qh = rh * WORD_BASE as DoubleWord + val;
                    rh = qh % d;

                    if let Some(v) = m3iter.next() {
                        *v = (qh / d) as Word;
                        rem[0] = rh as Word;
                    } else {
                        break;
                    }
                    val = *iter.next().unwrap_or(&0) as DoubleWord;
                }
            } else {
                for v in m3iter {
                    *v = 0;
                }
            }
        } else {
            // normalize: buf1 = d1 * d, buf2 = d2 * d
            let d = WORD_BASE / (m2[n] as DoubleWord + 1); // factor d: d * m2[most significant] is close to WORD_MAX

            if d == 1 {
                buf1[..l1].clone_from_slice(m1);
                buf2[..l2].clone_from_slice(m2);
                buf1[l1] = 0;
                buf2[l2] = 0;
            } else {
                Self::mul_by_word(m1, d, buf1);
                Self::mul_by_word(m2, d, buf2);
            }

            let v1 = buf2[n] as DoubleWord;
            let v2 = buf2[n - 1] as DoubleWord;

            j = m - n;
            let mut m3iter = m3.iter_mut().rev();
            let mut in_loop = false;
            let mut buf12;
            let mut buf11;
            let mut buf10;
            loop {
                buf12 = buf1[j + n + 1] as DoubleWord;
                buf11 = buf1[j + n] as DoubleWord;
                buf10 = buf1[j + n - 1] as DoubleWord;

                qh = buf12 * WORD_BASE + buf11;
                rh = qh % v1;
                qh /= v1;

                if qh >= WORD_BASE || (qh * v2 > WORD_BASE * rh + buf10) {
                    qh -= 1;
                    rh += v1;
                    if rh < WORD_BASE && (qh >= WORD_BASE || (qh * v2 > WORD_BASE * rh + buf10)) {
                        qh -= 1;
                    }
                }

                // n1_j = n1_j - n2 * qh
                c = 0;
                k = 0;
                for (a, b) in buf2[..n + 2].iter().zip(buf1[j..j + n + 2].iter_mut()) {
                    k = *a as DoubleWord * qh + k / WORD_BASE;
                    let val = k % WORD_BASE + c;
                    if (*b as DoubleWord) < val {
                        *b += (WORD_BASE - val) as Word;
                        c = 1;
                    } else {
                        *b -= val as Word;
                        c = 0;
                    }
                }

                if c > 0 {
                    // compensate
                    qh -= 1;
                    c = 0;
                    for (a, b) in buf2[..n + 2].iter().zip(buf1[j..j + n + 2].iter_mut()) {
                        c = add_carry(*a, *b, c as Word, b) as DoubleWord;
                    }
                    debug_assert!(c > 0);
                }

                if let Some(v) = m3iter.next() {
                    if in_loop || qh > 0 {
                        *v = qh as Word;
                    } else {
                        *v = 0;
                    }
                } else {
                    break;
                }

                if j == 0 {
                    break;
                }
                j -= 1;
                in_loop = true;
            }

            for v in m3iter {
                *v = 0;
            }

            if d > 1 {
                // restore remainder
                rh = 0;
                let mut j = l1 + 1;
                let mut iter = buf1[..l2].iter().rev();
                let mut val = *iter.next().unwrap_or(&0) as DoubleWord;
                let mut remiter = rem.iter_mut().rev();
                if val < d {
                    rh = val;
                    val = *iter.next().unwrap_or(&0) as DoubleWord;
                    *remiter.next().unwrap() = 0; // rem is at least 1 word long.
                    j -= 1;
                }

                if j > 0 {
                    loop {
                        qh = rh * WORD_BASE as DoubleWord + val;
                        rh = qh % d;

                        if let Some(v) = remiter.next() {
                            *v = (qh / d) as Word;
                        } else {
                            break;
                        }
                        val = *iter.next().unwrap_or(&0) as DoubleWord;
                    }
                } else {
                    for v in remiter {
                        *v = 0;
                    }
                }
            } else {
                rem.copy_from_slice(&buf1[..l2]);
            }
        }
        Ok((m3, rem))
    }

    // recursive division correction
    fn div_correction(a: &mut SliceWithSign, q: &mut SliceWithSign, step: SliceWithSign) {
        while a.sign() < 0 {
            q.decrement_abs();
            a.add_assign(&step);
        }
    }

    // Recursive integer division divides m1 by m2, returns quotinent and remainder.
    // prereq: m <= n, m2 is normalized
    fn div_recursive(m1: &[Word], m2: &[Word]) -> Result<(WordBuf, WordBuf), Error> {
        debug_assert!(m2[m2.len() - 1] & WORD_SIGNIFICANT_BIT != 0);

        if m1.len() < m2.len() {
            let mut q = WordBuf::new(1)?;
            q.fill(0);

            let mut r = WordBuf::new(m1.len())?;
            r.copy_from_slice(m1);

            return Ok((q, r));
        }

        let m = m1.len() - m2.len();

        debug_assert!(m <= m2.len());

        if m < 70 {
            Self::div_basic(m1, m2)
        } else {
            let k = m / 2;
            let k2 = k << 1;

            let mut rembuf = WordBuf::new(m1.len())?;
            let mut tmpbuf = WordBuf::new(m1.len())?;

            let a1 = SliceWithSign::new(&m1[k2..], 1); // m1 div 2^(2*k)
            let a0 = SliceWithSign::new(&m1[..k2], 1); // m1 mod 2^(2*k)

            let b = SliceWithSign::new(m2, 1);
            let b1 = SliceWithSign::new(&m2[k..], 1); // m2 div 2^k
            let b0 = SliceWithSign::new(&m2[..k], 1); // m2 mod 2^k

            let (mut q1buf, r1) = Self::div_recursive(&a1, &b1)?;
            let mut q1 = SliceWithSign::new_mut(&mut q1buf, 1);

            // a3 = a0 + r1*2^(2*k) - q1*b0*2^k
            rembuf[..k2].copy_from_slice(&a0);
            rembuf[k2..k2 + r1.len()].copy_from_slice(&r1);
            rembuf[k2 + r1.len()..].fill(0);

            tmpbuf[..k].fill(0);

            Self::mul_unbalanced(&q1, &b0, &mut tmpbuf[k..])?;

            let qbk = SliceWithSign::new(&tmpbuf[..q1.len() + b0.len() + k], 1);
            let mut a3 = SliceWithSign::new_mut(&mut rembuf, 1);
            a3.sub_assign(&qbk);

            if a3.sign() < 0 {
                // correction
                tmpbuf[..k].fill(0);
                tmpbuf[k + m2.len()..].fill(0);
                tmpbuf[k..k + m2.len()].copy_from_slice(m2);
                let b = SliceWithSign::new(&tmpbuf, 1);
                Self::div_correction(&mut a3, &mut q1, b);
            }

            let mut ub = a3.len();
            for v in a3.iter().rev() {
                if *v == 0 {
                    ub -= 1;
                } else {
                    break;
                }
            }

            q1buf.try_extend((m + 1) * WORD_BIT_SIZE)?;
            let mut q1 = SliceWithSign::new_mut(&mut q1buf, 1);

            if ub > k {
                let a31 = SliceWithSign::new(&rembuf[k..ub], 1); // a3 div 2^(k)
                let (mut q0, r0) = Self::div_recursive(&a31, &b1)?;
                let mut q0 = SliceWithSign::new_mut(&mut q0, 1);

                // a4 = r0*2^k + (a3 mod 2^k) - q0*b0
                rembuf[k..k + r0.len()].copy_from_slice(&r0);
                rembuf[k + r0.len()..].fill(0);
                let mut a4 = SliceWithSign::new_mut(&mut rembuf, 1);

                Self::mul_unbalanced(&q0, &b0, &mut tmpbuf)?;

                let qb = SliceWithSign::new(&tmpbuf[..q0.len() + b0.len()], 1);
                a4.sub_assign(&qb);

                if a4.sign() < 0 {
                    // correction
                    Self::div_correction(&mut a4, &mut q0, b);
                }

                // quot = q1 * 2^k + q0;
                let q0l = q0.len();
                if q0l > k {
                    q1[..k].copy_from_slice(&q0[..k]);
                    let q0 = SliceWithSign::new(&q0[k..], 1);
                    q1.add_assign(&q0);
                } else {
                    q1[..q0l].copy_from_slice(&q0);
                }
            }

            Ok((q1buf, rembuf))
        }
    }

    #[inline]
    fn div_basic_prefer(n: usize, m: usize) -> bool {
        n < 160 || {
            let lm = log2_ceil(m);
            lm >= 13 && (n < 50 * (lm - 13) + 200)
        }
    }

    // general case division
    pub(super) fn div_unbalanced(m1: &[Word], m2: &[Word]) -> Result<(WordBuf, WordBuf), Error> {
        if m1.len() < m2.len() {
            let q = WordBuf::new(1)?;
            let mut r = WordBuf::new(m1.len())?;
            r.copy_from_slice(m1);

            return Ok((q, r));
        }

        let mut m = m1.len() - m2.len();
        let n = m2.len();

        if m <= n {
            Self::div_recursive(m1, m2)
        } else if Self::div_basic_prefer(n, m) {
            Self::div_basic(m1, m2)
        } else {
            let mut buf1 = WordBuf::new(m + 1)?;
            buf1[m] = 0;

            let mut buf3 = WordBuf::new(m1.len())?;
            buf3.copy_from_slice(m1);

            let mut ub = m1.len();
            while m > n {
                let mn = m - n;

                let (q, r) = Self::div_recursive(&buf3[mn..ub], m2)?;

                buf1[mn..m].copy_from_slice(&q[..n]);
                let mut q1 = SliceWithSign::new_mut(&mut buf1[m..], 1);
                let q2 = SliceWithSign::new(&q[n..], 1);
                q1.add_assign(&q2);

                let prev_ub = ub;
                ub = mn + r.len().min(n);
                buf3[mn..ub].copy_from_slice(&r[..ub - mn]);
                buf3[ub..prev_ub].fill(0);

                m -= n;
            }

            let (q, r) = Self::div_recursive(&buf3[..ub], m2)?;

            buf1[..m].copy_from_slice(&q[..m]);
            let mut q1 = SliceWithSign::new_mut(&mut buf1[m..], 1);
            let q2 = SliceWithSign::new(&q[m..], 1);
            q1.add_assign(&q2);

            Ok((buf1, r))
        }
    }

    // short division
    // prepreq: m1.len() = 2*m2.len()
    #[allow(dead_code)] // TODO: consider performance improvement
    fn div_short(m1: &[Word], m2: &[Word]) -> Result<WordBuf, Error> {
        debug_assert!(m1.len() == 2 * m2.len());
        debug_assert!(m2[m2.len() - 1] & WORD_SIGNIFICANT_BIT != 0);
        if m2.len() <= 20 {
            let (q1, _r1) = Self::div_basic(m1, m2)?;
            Ok(q1)
        } else {
            let m2l = (m2.len() + 1) / 2;
            let k = m2.len() - m2l;

            let a1 = SliceWithSign::new(&m1[2 * k..], 1); // m1 div 2^(2*k)
            let a0 = SliceWithSign::new(&m1[..2 * k], 1); // m1 mod 2^(2*k)

            let b1 = SliceWithSign::new(&m2[k..], 1); // m2 div 2^k
            let b0 = SliceWithSign::new(&m2[..k], 1); // m2 mod 2^k

            let (mut q1, mut r1) = Self::div_basic(&a1, &b1)?;

            // a2 = a0 + r1*2^(2*k) - q1*b0*2^k
            let mut tmp_buf = WordBuf::new(m1.len() + 1)?;

            // TODO: consider using mul_short when it gets faster than mul_unbalanced
            tmp_buf[..k].fill(0);
            tmp_buf[k + q1.len() + b0.len()..].fill(0);
            Self::mul_unbalanced(&q1, &b0, &mut tmp_buf[k..])?;

            let mut bqk = SliceWithSign::new_mut(&mut tmp_buf, -1);
            bqk.add_assign(&a0);

            r1.try_extend((r1.len() + k * 2) * WORD_BIT_SIZE)?;
            let r1 = SliceWithSign::new(&r1, 1);
            bqk.add_assign(&r1);

            if bqk.sign() < 0 {
                let mut q1 = SliceWithSign::new_mut(&mut q1, -1);
                let mut bk = WordBuf::new(m2.len() + k)?;
                bk[..k].fill(0);
                bk[k..].copy_from_slice(m2);
                let b = SliceWithSign::new(&bk, 1);
                Self::div_correction(&mut bqk, &mut q1, b);
            }

            let a21 = SliceWithSign::new(&tmp_buf[m2l..], 1); // a2 div 2^m2l
            let b21 = SliceWithSign::new(&m2[m2l..], 1); // m1 div 2^m2l
            let q0 = Self::div_short(&a21[..b21.len() * 2], &b21)?;
            let q0 = SliceWithSign::new(&q0, 1);

            let mut full_q_buf = WordBuf::new(m2.len() + 1)?;
            full_q_buf[..k].fill(0);
            full_q_buf[q1.len() + k..].fill(0);
            full_q_buf[k..q1.len() + k].copy_from_slice(&q1);
            let mut full_q = SliceWithSign::new_mut(&mut full_q_buf, 1);
            full_q.add_assign(&q0);

            Ok(full_q_buf)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::WORD_SIGNIFICANT_BIT;
    use rand::random;

    #[cfg(not(feature = "std"))]
    use alloc::vec::Vec;

    #[test]
    fn test_div_unbalanced() {
        const MAX_BUF: usize = 300;
        let mut wb = [0; MAX_BUF];
        let mut buf = [0; MAX_BUF];
        for _ in 0..1000 {
            let s1 = random_normalized_slice(1, MAX_BUF);
            let s2 = random_normalized_slice(s1.len(), MAX_BUF);

            //println!("let s1 = {:?};\nlet s2 = {:?};", s1, s2);

            let (q, r) = Mantissa::div_unbalanced(&s2, &s1).unwrap();

            buf[..s1.len()].copy_from_slice(&s1);
            buf[s1.len()..].fill(0);
            let mut d1 = SliceWithSign::new_mut(&mut buf, 1);
            let d2 = SliceWithSign::new(&q, 1);
            let d3 = SliceWithSign::new(&r, 1);
            d1.mul_assign(&d2, &mut wb);
            d1.add_assign(&d3);
            //println!("{:?}\n{:?}\n", s2, &d1[..s2.len()]);
            assert!(s2 == d1[..s2.len()]);
        }
    }

    #[test]
    fn test_div_short() {
        const MAX_BUF: usize = 100;
        let mut wb = [0; MAX_BUF * 3 + 1];
        let mut buf = [0; MAX_BUF * 3 + 1];

        for _ in 0..1000 {
            let s1 = random_normalized_slice(MAX_BUF, MAX_BUF);
            let mut s2 = random_normalized_slice(s1.len() * 2, s1.len() * 2);
            s2[..s1.len()].fill(0);

            //println!("s1{:?}\ns2{:?}", s1, &s2[s1.len()..]);

            let q = Mantissa::div_short(&s2, &s1).unwrap();

            buf[..s1.len()].copy_from_slice(&s1);
            buf[s1.len()..].fill(0);
            let mut d1 = SliceWithSign::new_mut(&mut buf, 1);
            let d2 = SliceWithSign::new(&q, 1);
            d1.mul_assign(&d2, &mut wb);
            s2[s1.len()] = 0; // q can be grater than floor(s2/s1) by at most 2*log2(n)
            d1[s1.len()] = 0;
            //println!("{:?}\n{:?}\n", &s2[s1.len()..], &d1[s1.len()..s2.len()]);
            assert!(s2[s1.len()..] == d1[s1.len()..s2.len()]);
            // TODO: also worth checking if remainder less than divizor
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn test_div_perf() {
        for _ in 0..5 {
            let sz1 = 16384;
            let sz2 = 800;
            let f = random_normalized_slice(sz1, sz1);
            let mut n = vec![];
            let l = 10;
            for _ in 0..l {
                let v = random_normalized_slice(sz2, sz2);
                n.push(v);
            }

            // basic
            let start_time = std::time::Instant::now();
            for ni in &n {
                let _ = Mantissa::div_basic(&f, ni).unwrap();
            }
            let time = start_time.elapsed();
            println!("div_basic {}", time.as_millis());

            // unbalanced
            let start_time = std::time::Instant::now();
            for ni in &n {
                let _ = Mantissa::div_unbalanced(&f, ni).unwrap();
            }
            let time = start_time.elapsed();
            println!("div_unbalanced {}", time.as_millis());
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn test_div_short_perf() {
        for _ in 0..5 {
            let sz1 = 1000;
            let sz2 = 500;
            let f = random_normalized_slice(sz1, sz1);
            let mut n = vec![];
            let l = 1000;
            for _ in 0..l {
                let v = random_normalized_slice(sz2, sz2);
                n.push(v);
            }

            // basic
            let start_time = std::time::Instant::now();
            for ni in &n {
                let _ = Mantissa::div_basic(&f, ni).unwrap();
            }
            let time = start_time.elapsed();
            println!("div_basic {}", time.as_millis());

            // unbalanced
            let start_time = std::time::Instant::now();
            for ni in &n {
                let _ = Mantissa::div_short(&f, ni).unwrap();
            }
            let time = start_time.elapsed();
            println!("div_short {}", time.as_millis());
        }
    }

    fn random_normalized_slice(min_len: usize, max_len: usize) -> Vec<Word> {
        let mut s1 = Vec::new();
        let l = if max_len > min_len {
            random::<usize>() % (max_len - min_len) + min_len
        } else {
            min_len
        };
        for _ in 0..l {
            s1.push(random());
        }
        let l = s1.len();
        s1[l - 1] |= WORD_SIGNIFICANT_BIT;
        s1
    }
}
