//! Square root.

use crate::common::buf::WordBuf;
use crate::common::int::SliceWithSign;
use crate::common::util::find_one_from;
use crate::common::util::shift_slice_left;
use crate::common::util::shift_slice_right;
use crate::defs::Error;
use crate::defs::Word;
use crate::defs::WORD_BIT_SIZE;
use crate::mantissa::Mantissa;

impl Mantissa {
    // Basic algorithm for small inputs.
    fn sqrt_rem_basic(m: &[Word]) -> Result<(WordBuf, WordBuf), Error> {
        let zc = m.iter().rev().take_while(|x| **x == 0).count();
        if zc == m.len() {
            // m is zero

            let mut qbuf = WordBuf::new(1)?;
            qbuf.fill(0);

            let mut rbuf = WordBuf::new(1)?;
            rbuf.fill(0);

            return Ok((qbuf, rbuf));
        }

        let m = &m[..m.len() - zc];

        let mut sbuf = WordBuf::new(m.len())?;
        sbuf.copy_from_slice(&m);

        loop {
            let (mut qbuf, _rbuf) = Self::div_basic(m, &sbuf)?;

            qbuf.try_extend_2((m.len() + 1) * WORD_BIT_SIZE)?;

            let s = SliceWithSign::new(&mut sbuf, 1);
            let mut q = SliceWithSign::new_mut(&mut qbuf, 1);

            q.add_assign(&s);
            q.shift_right(1);

            // compare with previous
            if q.cmp(&s) >= 0 {
                // q^2
                let mut sqbuf = WordBuf::new(sbuf.len() * 2)?;
                Self::mul_basic(&sbuf, &sbuf, &mut sqbuf);
                let sq = SliceWithSign::new(&sqbuf, 1);

                // remainder
                let mut rbuf = WordBuf::new(m.len())?;
                rbuf.copy_from_slice(m);
                let mut r = SliceWithSign::new_mut(&mut rbuf, 1);
                r.sub_assign(&sq);

                break Ok((sbuf, rbuf));
            }

            qbuf.trunc_leading_zeroes();
            sbuf = qbuf;
        }
    }

    /// Square root with the remainder from "Modern Computer Arithmetic" (R. P. Brent, P. Zimmermann)
    pub(super) fn sqrt_rem(m: &[Word]) -> Result<(WordBuf, WordBuf), Error> {
        let l = (m.len() - 1) / 4;

        let zc = m.iter().rev().take_while(|x| **x == 0).count();
        if zc == m.len() {
            // m is zero

            let mut qbuf = WordBuf::new(1)?;
            qbuf.fill(0);

            let mut rbuf = WordBuf::new(1)?;
            rbuf.fill(0);

            return Ok((qbuf, rbuf));
        }

        let m = &m[..m.len() - zc];

        if l == 0 {
            Self::sqrt_rem_basic(m)
        } else {
            let (m2, m1, m0) = Self::sqrt_rem_split(m, l);

            let (mut sbuf, mut rbuf) = Self::sqrt_rem(&m2)?;

            rbuf.try_extend((rbuf.len() + l) * WORD_BIT_SIZE)?;

            // r*2^n + m1
            let mut r = SliceWithSign::new_mut(&mut rbuf, 1);
            r.add_assign(&m1);

            // s*2 and normalize
            let mut s2buf = WordBuf::new(sbuf.len() + 1)?;
            s2buf[..sbuf.len()].copy_from_slice(&sbuf);
            *s2buf.last_mut().unwrap() = 0; // s2buf has at least 1 element.

            let pos = find_one_from(&s2buf, 0).unwrap(); // size of s2buf > size of sbuf

            shift_slice_left(&mut s2buf, pos);

            // scale dividentaccordingly
            let scale = pos - 1;

            rbuf.try_extend_2((rbuf.len() + 1) * WORD_BIT_SIZE)?;
            shift_slice_left(&mut rbuf, scale);

            // (r*2^n + m1) / (s*2)
            let (mut qbuf, mut ubuf) = Self::div_unbalanced(&rbuf, &s2buf)?;

            // descale remainder
            shift_slice_right(&mut ubuf, scale);

            // q^2
            let mut qsbuf = WordBuf::new(qbuf.len() * 2)?;
            Self::mul_unbalanced(&qbuf, &qbuf, &mut qsbuf)?;
            let qs = SliceWithSign::new(&qsbuf, 1);

            sbuf.try_extend((sbuf.len() + l) * WORD_BIT_SIZE)?;
            sbuf.try_extend_2((sbuf.len() + 1) * WORD_BIT_SIZE)?;
            ubuf.try_extend((ubuf.len() + l) * WORD_BIT_SIZE)?;

            let q = SliceWithSign::new_mut(&mut qbuf, 1);
            let mut r = SliceWithSign::new_mut(&mut ubuf, 1);
            let mut s = SliceWithSign::new_mut(&mut sbuf, 1);

            // s*2^n + q
            s.add_assign(&q);

            // r*2^n + m0 - q^2
            r.add_assign(&m0);
            r.sub_assign(&qs);

            if r.sign() < 0 {
                let one = SliceWithSign::new(&[1], 1);

                // r + 2s - 1
                r.add_assign(&s);
                r.add_assign(&s);
                r.sub_assign(&one);

                // decremet s
                s.sub_assign(&one);
            }

            debug_assert!(sbuf[sbuf.len() - 1] == 0);
            sbuf.trunc_to_2((sbuf.len() - 1) * WORD_BIT_SIZE);

            Ok((sbuf, ubuf))
        }
    }

    fn sqrt_rem_split(m: &[Word], l: usize) -> (SliceWithSign, SliceWithSign, SliceWithSign) {
        let (m, m2) = m.split_at(2 * l);
        let (m0, m1) = m.split_at(l);

        (
            SliceWithSign::new(m2, 1),
            SliceWithSign::new(m1, 1),
            SliceWithSign::new(m0, 1),
        )
    }
}

#[cfg(test)]
mod tests {

    use crate::defs::{WORD_MAX, WORD_SIGNIFICANT_BIT};

    use super::*;
    use rand::random;

    macro_rules! assert_sqrt {
        ($s1:expr, $qb:expr, $rb:expr, $MAX_BUF:ident, $op:literal) => {
            let mut wb = [0; MAX_BUF * 2];
            let mut buf = [0; MAX_BUF * 2];

            let q = SliceWithSign::new($qb, 1);
            let r = SliceWithSign::new($rb, 1);

            buf[q.len()..].fill(0);
            buf[..q.len()].copy_from_slice(&q);

            let mut qq = SliceWithSign::new_mut(&mut buf, 1);

            qq.mul_assign(&q, &mut wb);
            qq.add_assign(&r);

            assert_eq!(&qq[..$s1.len()], $s1, "{}", $op);
        };
    }

    #[test]
    fn test_sqrt_basic() {
        const MAX_BUF: usize = 4;

        let s1: &[Word] = &[WORD_MAX];
        let s2: &[Word] = &[WORD_MAX, WORD_MAX];
        let s3: &[Word] = &[WORD_MAX, WORD_MAX, WORD_MAX];
        let s4: &[Word] = &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX];
        for s1 in [s1, s2, s3, s4] {
            let (qb, rb) = Mantissa::sqrt_rem_basic(s1).unwrap();

            assert_sqrt!(s1, &qb, &rb, MAX_BUF, "max");
        }

        let s1: &[Word] = &[WORD_MAX - 1];
        let s2: &[Word] = &[WORD_MAX - 1, WORD_MAX];
        let s3: &[Word] = &[WORD_MAX - 1, WORD_MAX, WORD_MAX];
        let s4: &[Word] = &[WORD_MAX - 1, WORD_MAX, WORD_MAX, WORD_MAX];
        for s1 in [s1, s2, s3, s4] {
            let (qb, rb) = Mantissa::sqrt_rem_basic(s1).unwrap();

            assert_sqrt!(s1, &qb, &rb, MAX_BUF, "single zero");
        }

        for int in 1..32 {
            let s1: &[Word] = &[int];
            let s2: &[Word] = &[int, 0];
            let s3: &[Word] = &[int, 0, 0];
            let s4: &[Word] = &[int, 0, 0, 0];
            for s1 in [s1, s2, s3, s4] {
                let (qb, rb) = Mantissa::sqrt_rem_basic(s1).unwrap();

                assert_sqrt!(s1, &qb, &rb, MAX_BUF, "int");
            }
        }

        for _ in 0..1000 {
            let s1 = random_normalized_slice(MAX_BUF, MAX_BUF);

            let (qb, rb) = Mantissa::sqrt_rem_basic(&s1).unwrap();

            //println!("\n{:?}\n{:?}\n{:?}", s1, qb, rb);

            assert_sqrt!(&s1, &qb, &rb, MAX_BUF, "rand");
        }
    }

    #[test]
    fn test_sqrt_rem() {
        const MAX_BUF: usize = 100;

        /* let s1 = &[0, 0, 0, 0, 0, 0, 0, 1649495861915690046, 0, 0, 0, 9223372036854775808];

        let (qb, rb) = Mantissa::sqrt_rem(s1).unwrap();

        assert_sqrt!(s1, &qb, &rb, MAX_BUF, "zeroes between");
        return; */

        let s1: &[Word] = &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX];
        let s2: &[Word] = &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX];
        let s3: &[Word] = &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX];
        let s4: &[Word] =
            &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX];
        let s5: &[Word] = &[
            WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX,
            WORD_MAX,
        ];
        let s6: &[Word] = &[
            WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX,
            WORD_MAX, WORD_MAX,
        ];
        let s7: &[Word] = &[
            WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX,
            WORD_MAX, WORD_MAX, WORD_MAX,
        ];
        for s1 in [s1, s2, s3, s4, s5, s6, s7] {
            let (qb, rb) = Mantissa::sqrt_rem(s1).unwrap();

            assert_sqrt!(s1, &qb, &rb, MAX_BUF, "max");
        }

        let s1: &[Word] = &[WORD_MAX - 1, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX];
        let s2: &[Word] = &[WORD_MAX - 1, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX];
        let s3: &[Word] =
            &[WORD_MAX - 1, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX];
        let s4: &[Word] = &[
            WORD_MAX - 1,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
        ];
        let s5: &[Word] = &[
            WORD_MAX - 1,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
        ];
        let s6: &[Word] = &[
            WORD_MAX - 1,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
        ];
        let s7: &[Word] = &[
            WORD_MAX - 1,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
            WORD_MAX,
        ];
        for s1 in [s1, s2, s3, s4, s5, s6, s7] {
            let (qb, rb) = Mantissa::sqrt_rem(s1).unwrap();

            assert_sqrt!(s1, &qb, &rb, MAX_BUF, "single zero");
        }

        let s1: &[Word] = &[0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s2: &[Word] = &[0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s3: &[Word] = &[0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s4: &[Word] = &[0, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s5: &[Word] = &[0, 0, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s6: &[Word] = &[0, 0, 0, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s7: &[Word] = &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        for s1 in [s1, s2, s3, s4, s5, s6, s7] {
            let (qb, rb) = Mantissa::sqrt_rem(s1).unwrap();

            assert_sqrt!(s1, &qb, &rb, MAX_BUF, "msb set");
        }

        let s1: &[Word] = &[1, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s2: &[Word] = &[3, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s3: &[Word] = &[7, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s4: &[Word] = &[15, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s5: &[Word] = &[1, 0, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s6: &[Word] = &[3, 0, 0, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        let s7: &[Word] = &[7, 0, 0, 0, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT];
        for s1 in [s1, s2, s3, s4, s5, s6, s7] {
            let (qb, rb) = Mantissa::sqrt_rem(s1).unwrap();

            assert_sqrt!(s1, &qb, &rb, MAX_BUF, "zeroes between");
        }

        for _ in 0..1000 {
            let s1 = random_normalized_slice(MAX_BUF, MAX_BUF);

            let (qb, rb) = Mantissa::sqrt_rem(&s1).unwrap();

            //println!("\n{:?}\n{:?}\n{:?}", s1, qb, rb);

            assert_sqrt!(&s1, &qb, &rb, MAX_BUF, "rand");
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
