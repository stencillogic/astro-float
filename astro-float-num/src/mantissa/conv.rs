//! Base conversion.

use crate::common::buf::WordBuf;
use crate::common::util::shift_slice_right;
use crate::mantissa::Mantissa;
use crate::{Error, WORD_BIT_SIZE};

impl Mantissa {
    /// Convert `input` words to an array of decimal digits with divide and conquer algorithm.
    /// `l` is the number of decimal digits in the input ceiled to a power of 10.
    /// `p` is the current depth of `tenpowers` for the given `input`.
    pub(crate) fn conv_to_dec(
        &mut self,
        l: usize,
        tenpowers: &[(WordBuf, usize)],
        p: usize,
    ) -> Result<Vec<u8>, Error> {
        if self.bit_len() == 0 {
            Ok(Vec::new())
        } else if self.bit_len() <= WORD_BIT_SIZE {
            let mut ret = Vec::new();
            ret.try_reserve_exact(l)?;

            let mut v = self.digits()[0];
            for _ in 0..l {
                ret.push((v % 10) as u8);
                v /= 10;
            }

            Ok(ret)
        } else {
            let (tenpower, shift) = &tenpowers[p];

            self.shift_left_resize(*shift)?;

            let (q, mut r) = Self::div_unbalanced(self.digits(), &tenpower)?;

            shift_slice_right(&mut r, *shift);

            let mut q = Mantissa::from_word_buf(q);
            let mut r = Mantissa::from_word_buf(r);

            let mut part1 = Self::conv_to_dec(&mut r, l / 2, tenpowers, p - 1)?;
            let mut part2 = Self::conv_to_dec(&mut q, l / 2, tenpowers, p - 1)?;

            part1.try_reserve_exact(part2.len())?;
            part1.append(&mut part2);

            Ok(part1)
        }
    }

    /// Compute powers of 10 up to the depth of `p` and save the result in `tenpowers`.
    pub(crate) fn compute_tenpowers(
        tenpowers: &mut Vec<(WordBuf, usize)>,
        p: usize,
    ) -> Result<(), Error> {
        if tenpowers.len() == 0 {
            let mut wb = WordBuf::new(1)?;
            wb[0] = 10;
            let shift = Self::maximize(&mut wb);
            tenpowers.push((wb, shift));
        }

        let l = tenpowers.len();
        if p > l {
            for _ in l..p {
                let last = tenpowers.len() - 1;
                let mut wb = WordBuf::new(tenpowers[last].0.len() * 2)?;

                Self::mul_unbalanced(&tenpowers[last].0, &tenpowers[last].0, &mut wb)?;

                shift_slice_right(&mut wb, 2 * tenpowers[last].1);
                wb.trunc_leading_zeroes();

                let shift = Self::maximize(&mut wb);
                tenpowers.push((wb, shift));
            }
        }

        Ok(())
    }

    pub fn conv_from_dec(input: &[u8]) -> Result<Self, Error> {
        Mantissa::new(1)
    }
}

#[cfg(test)]
mod tests {

    use core::ops::Deref;

    use rand::random;

    use crate::{common::util::log2_ceil, Word, WORD_BIT_SIZE, WORD_SIGNIFICANT_BIT};

    use super::*;

    #[test]
    fn test_compute_tenpowers() {
        fn tenpower_from(x: Word) -> (WordBuf, usize) {
            let mut wb = WordBuf::new(1).unwrap();
            wb[0] = x;
            let shift = Mantissa::maximize(&mut wb);
            assert!(wb[0] & WORD_SIGNIFICANT_BIT != 0);
            (wb, shift)
        }

        let mut tenpowers = Vec::with_capacity(4);
        let refval = [
            tenpower_from(10),
            tenpower_from(100),
            tenpower_from(10000),
            tenpower_from(100000000),
        ];

        Mantissa::compute_tenpowers(&mut tenpowers, 0).unwrap();
        Mantissa::compute_tenpowers(&mut tenpowers, 3).unwrap();
        Mantissa::compute_tenpowers(&mut tenpowers, 1).unwrap();
        Mantissa::compute_tenpowers(&mut tenpowers, 0).unwrap();
        Mantissa::compute_tenpowers(&mut tenpowers, 4).unwrap();

        for ((tenpower, shift), (refwb, refshift)) in tenpowers.iter().zip(refval.iter()) {
            assert_eq!(tenpower.deref() as &[Word], refwb.deref() as &[Word]);
            assert_eq!(shift, refshift);
        }

        // 10^32
        Mantissa::compute_tenpowers(&mut tenpowers, 8).unwrap();
        assert_eq!(tenpowers.len(), 8);

        let (tenpow, shift) = &tenpowers[7];
        let mut wb = WordBuf::new(tenpow.len()).unwrap();
        wb.copy_from_slice(tenpow.deref());
        shift_slice_right(&mut wb, *shift);

        for _ in 0..128 {
            let (q, r) = Mantissa::div_basic(&wb, &[10]).unwrap();
            assert!(r.iter().all(|x| *x == 0));
            assert!(q.iter().any(|x| *x != 0));
            wb = q;
        }

        wb.trunc_leading_zeroes();
        assert_eq!(wb.len(), 1);
        assert_eq!(wb[0], 1);
    }

    #[test]
    fn test_conv_to_dec() {
        let mut tenpowers = Vec::with_capacity(10);
        Mantissa::compute_tenpowers(&mut tenpowers, 10).unwrap();

        let ten = [10];

        let test_input = |input: WordBuf| {
            let mut expected = Vec::new();
            let (mut t, mut s) = Mantissa::div_basic(&input, &ten).unwrap();
            loop {
                expected.push(s[0] as u8);
                t.trunc_leading_zeroes();
                if t.len() == 0 {
                    break;
                }
                let (q, r) = Mantissa::div_basic(&t, &ten).unwrap();
                t = q;
                s = r;
            }

            let k = ((input.len() * WORD_BIT_SIZE) as u64 * 301029996 / 1000000000) as usize + 1;

            let p = log2_ceil(k);

            let mut m = Mantissa::from_word_buf(input);
            let ret = m.conv_to_dec(1 << p, &tenpowers, p - 1).unwrap();

            let nz = ret.len() - ret.iter().rev().take_while(|x| **x == 0).count();

            assert_eq!(ret[..nz], expected);
        };

        /* let tst = [30084890778824686, 11770605104927693244, 8544847625486449288, 11144046192367933953];
        let mut input = WordBuf::new(tst.len()).unwrap();
        input.copy_from_slice(&tst);
        test_input(input);
        return; */

        for _ in 0..100 {
            for l in 1..100 {
                let mut input = WordBuf::new(l).unwrap();
                for v in input.iter_mut() {
                    *v = random();
                }

                test_input(input);
            }
        }
    }
}
