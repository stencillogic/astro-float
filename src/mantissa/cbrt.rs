//! Cube root.

use crate::common::buf::WordBuf;
use crate::common::int::SliceWithSign;
use crate::common::util::find_one_from;
use crate::common::util::shift_slice_left;
use crate::common::util::shift_slice_right;
use crate::defs::Error;
use crate::defs::WORD_BIT_SIZE;
use crate::mantissa::util::root_estimate;
use crate::mantissa::util::RightShiftedSlice;
use crate::mantissa::Mantissa;
use crate::Word;

impl Mantissa {
    // normalize for division
    fn crbt_normalize_div(
        m1: &mut WordBuf,
        m2: &mut [Word],
        m_shift: usize,
    ) -> Result<usize, Error> {
        if let Some(shift) = find_one_from(m2, 0) {
            shift_slice_left(m2, shift);

            if m_shift > shift {
                shift_slice_right(m1 as &mut [Word], m_shift - shift);
            } else if m_shift < shift {
                shift_slice_left(m1 as &mut [Word], shift - m_shift);
            }

            Ok(shift)
        } else {
            Ok(m_shift)
        }
    }

    /// Cube root with remainder.
    pub fn cbrt_rem(mut m: WordBuf) -> Result<(WordBuf, WordBuf), Error> {
        let mut sbuf = root_estimate(&m, 3)?;
        let mut tmpbuf = WordBuf::new(sbuf.len() * 5)?;
        let mut wb = WordBuf::new(sbuf.len() + 1)?;
        let mut m_shift = 0;

        // additional space for normalization
        m.try_extend_2((m.len() + 2) * WORD_BIT_SIZE)?;

        loop {
            let mut sqbuf = &mut tmpbuf[..sbuf.len() * 2];

            // sq = s^2
            Self::mul_unbalanced(&sbuf, &sbuf, &mut sqbuf)?;

            m_shift = Self::crbt_normalize_div(&mut m, sqbuf, m_shift)?;

            // m / sq
            let (mut qbuf, _rbuf) = Self::div_unbalanced(&m, &sqbuf)?;

            // w = s * 2
            wb.iter_mut()
                .zip(RightShiftedSlice::new(&sbuf, WORD_BIT_SIZE - 1, 0, 1))
                .for_each(|(u, v)| *u = v);

            qbuf.try_extend_2((qbuf.len().max(wb.len()) + 1) * WORD_BIT_SIZE)?;

            let s = SliceWithSign::new(&sbuf, 1);
            let w = SliceWithSign::new(&wb, 1);
            let mut q = SliceWithSign::new_mut(&mut qbuf, 1);

            // (q + w) / 3
            q.add_assign(&w);
            q.div_by_word(3);

            // compare with previous
            if q.cmp(&s) >= 0 {
                // remainder
                let mut rbuf = WordBuf::new(m.len() - 2)?;
                shift_slice_right(&mut m, m_shift);
                rbuf.copy_from_slice(&m[..m.len() - 2]);

                let mut r = SliceWithSign::new_mut(&mut rbuf, 1);

                Self::cbrt_remainder(&mut tmpbuf, &mut sbuf, &mut r)?;

                debug_assert!(r.sign() >= 0);

                break Ok((sbuf, rbuf));
            }

            qbuf.trunc_leading_zeroes();
            sbuf = qbuf;
        }
    }

    // compute remainder
    fn cbrt_remainder(
        tmpbuf: &mut WordBuf,
        sbuf: &mut WordBuf,
        r: &mut SliceWithSign,
    ) -> Result<(), Error> {
        let (sqbuf, rest) = tmpbuf.split_at_mut(sbuf.len() * 2);
        let scbuf = &mut rest[..sbuf.len() * 3];

        // q^3
        Self::mul_unbalanced(&sbuf, &sbuf, sqbuf)?;
        Self::mul_unbalanced(&sqbuf, &sbuf, scbuf)?;
        let sc = SliceWithSign::new(scbuf, 1);

        r.sub_assign(&sc);

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        defs::{WORD_MAX, WORD_SIGNIFICANT_BIT},
        Word,
    };

    use super::*;
    use rand::random;

    macro_rules! assert_sqrt {
        ($s1:expr, $qb:expr, $rb:expr, $MAX_BUF:ident, $op:literal) => {
            let mut wb = [0; MAX_BUF * 3];
            let mut buf = [0; MAX_BUF * 3];

            let q = SliceWithSign::new($qb, 1);
            let r = SliceWithSign::new($rb, 1);

            buf[q.len()..].fill(0);
            buf[..q.len()].copy_from_slice(&q);

            let mut qq = SliceWithSign::new_mut(&mut buf, 1);

            qq.mul_assign(&q, &mut wb);
            qq.mul_assign(&q, &mut wb);
            qq.add_assign(&r);

            assert_eq!(&qq[..$s1.len()], $s1, "{}", $op);
        };
    }

    fn wordbuf_from_words(s: &[Word]) -> WordBuf {
        let mut ret = WordBuf::new(s.len()).unwrap();
        ret.copy_from_slice(s);
        ret
    }

    #[test]
    fn test_cbrt_rem() {
        const MAX_BUF: usize = 100;

        /* let s1 = &[1, 1, 1, WORD_SIGNIFICANT_BIT];

        let (qb, rb) = Mantissa::cbrt_rem(wordbuf_from_words(s1)).unwrap();

        println!("\n{:?}\n{:?}", qb, rb);

        assert_sqrt!(s1, &qb, &rb, MAX_BUF, "zeroes between");
        return; */

        for s1 in [
            &[WORD_MAX] as &[Word],
            &[WORD_MAX, WORD_MAX],
            &[WORD_MAX, WORD_MAX, WORD_MAX],
            &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX],
            &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX],
            &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX],
            &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX],
            &[WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX, WORD_MAX],
        ] {
            let (qb, rb) = Mantissa::cbrt_rem(wordbuf_from_words(&s1)).unwrap();

            assert_sqrt!(&s1 as &[Word], &qb, &rb, MAX_BUF, "max");
        }

        for s1 in [
            &[WORD_SIGNIFICANT_BIT] as &[Word],
            &[0, WORD_SIGNIFICANT_BIT],
            &[0, 0, WORD_SIGNIFICANT_BIT],
            &[0, 0, 0, WORD_SIGNIFICANT_BIT],
            &[0, 0, 0, 0, WORD_SIGNIFICANT_BIT],
            &[0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT],
            &[0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT],
            &[0, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT],
        ] {
            let (qb, rb) = Mantissa::cbrt_rem(wordbuf_from_words(&s1)).unwrap();

            assert_sqrt!(&s1 as &[Word], &qb, &rb, MAX_BUF, "significant");
        }

        for s1 in [
            &[WORD_SIGNIFICANT_BIT + 1] as &[Word],
            &[1, WORD_SIGNIFICANT_BIT],
            &[1, 0, WORD_SIGNIFICANT_BIT],
            &[1, 0, 0, WORD_SIGNIFICANT_BIT],
            &[1, 0, 0, 0, WORD_SIGNIFICANT_BIT],
            &[1, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT],
            &[1, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT],
            &[1, 0, 0, 0, 0, 0, 0, WORD_SIGNIFICANT_BIT],
        ] {
            let (qb, rb) = Mantissa::cbrt_rem(wordbuf_from_words(&s1)).unwrap();

            assert_sqrt!(&s1 as &[Word], &qb, &rb, MAX_BUF, "lsb + msb");
        }

        for s1 in [
            &[1 as Word] as &[Word],
            &[1, 2],
            &[1, 0, 3],
            &[1, 0, 0, 4],
            &[1, 0, 0, 0, 5],
            &[1, 0, 0, 0, 0, 6],
            &[1, 0, 0, 0, 0, 0, 7],
            &[1, 0, 0, 0, 0, 0, 0, 8],
        ] {
            let (qb, rb) = Mantissa::cbrt_rem(wordbuf_from_words(&s1)).unwrap();

            assert_sqrt!(&s1 as &[Word], &qb, &rb, MAX_BUF, "subnormal");
        }

        for _ in 0..1000 {
            let s1 = random_normalized_slice(1, MAX_BUF);

            let (qb, rb) = Mantissa::cbrt_rem(wordbuf_from_words(&s1)).unwrap();

            //println!("\n{:?}\n{:?}\n{:?}", s1, qb, rb);

            assert_sqrt!(&s1 as &[Word], &qb, &rb, MAX_BUF, "rand");
        }
    }

    fn random_normalized_slice(min_len: usize, max_len: usize) -> WordBuf {
        let l = if max_len > min_len {
            random::<usize>() % (max_len - min_len) + min_len
        } else {
            min_len
        };

        let mut s1 = WordBuf::new(l).unwrap();

        for v in s1.iter_mut() {
            *v = random();
        }

        let l = s1.len();
        s1[l - 1] |= WORD_SIGNIFICANT_BIT;
        s1
    }
}
