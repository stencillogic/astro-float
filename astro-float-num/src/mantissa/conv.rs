//! Base conversion.

use crate::common::buf::WordBuf;
use crate::common::int::SliceWithSign;
use crate::common::util::shift_slice_right;
use crate::mantissa::Mantissa;
use crate::{Error, Word, WORD_BIT_SIZE};

impl Mantissa {
    /// Convert `input` words to an array of decimal digits with divide and conquer algorithm.
    /// `l` is the number of decimal digits in the input ceiled to a power of 10.
    /// `p` is the current depth of `tenpowers` for the given `input`.
    pub(crate) fn conv_to_dec(
        &mut self,
        l: usize,
        tenpowers: &[(WordBuf, WordBuf, usize)],
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
            let (tenpower, _, shift) = &tenpowers[p];

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
        tenpowers: &mut Vec<(WordBuf, WordBuf, usize)>,
        p: usize,
    ) -> Result<(), Error> {
        if tenpowers.len() == 0 {
            let mut wb = WordBuf::new(1)?;
            wb[0] = 10;
            let shift = Self::maximize(&mut wb);

            let mut wb2 = WordBuf::new(1)?;
            wb2[0] = 10;

            tenpowers.push((wb, wb2, shift));
        }

        let l = tenpowers.len();
        if p > l {
            for _ in l..p {
                let last: usize = tenpowers.len() - 1;
                let mut wb2 = WordBuf::new(tenpowers[last].1.len() * 2)?;

                Self::mul_unbalanced(&tenpowers[last].1, &tenpowers[last].1, &mut wb2)?;

                wb2.trunc_leading_zeroes();

                let mut wb = WordBuf::new(wb2.len())?;
                wb.copy_from_slice(&wb2);

                let shift = Self::maximize(&mut wb);

                tenpowers.push((wb, wb2, shift));
            }
        }

        Ok(())
    }

    /// Convert `input` in decimal base to the mantissa using divide and conquer.
    pub fn conv_from_dec(
        input: &[u8],
        tenpowers: &[(WordBuf, WordBuf, usize)],
    ) -> Result<Self, Error> {
        let leadzeroes = input.iter().take_while(|&&x| x == 0).count();

        const WORD_TENPOWER: usize = if WORD_BIT_SIZE < 64 { 8 } else { 16 };

        const TENPOWER_START_ID: usize = if WORD_BIT_SIZE < 64 { 3 } else { 4 };

        let mut chunks = Vec::new();
        chunks.try_reserve_exact((input.len() + WORD_TENPOWER - 1) / WORD_TENPOWER)?;

        let mut word: Word = 0;
        let mut i = 0;
        let mut t = 1;
        for &v in input.iter().skip(leadzeroes).rev() {
            if v > 9 {
                return Err(Error::InvalidArgument);
            }

            word += v as Word * t;
            t *= 10;
            i += 1;

            if i == WORD_TENPOWER {
                let mut wb = WordBuf::new(1)?;
                wb[0] = word;
                chunks.push(wb);
                i = 0;
                t = 1;
                word = 0;
            }
        }

        if i > 0 {
            let mut wb = WordBuf::new(1)?;
            wb[0] = word;
            chunks.push(wb);
        }

        let mut p = TENPOWER_START_ID;
        loop {
            if chunks.len() == 1 {
                break;
            }

            let (_, tenpower, _) = &tenpowers[p];

            let mut newchunks = Vec::new();
            newchunks.try_reserve_exact((chunks.len() + 1) / 2)?;

            for pair in chunks.chunks(2) {
                if pair.len() == 2 {
                    let mut wb1 = WordBuf::new(pair[1].len() + tenpower.len())?;
                    Self::mul_unbalanced(&pair[1], &tenpower, &mut wb1)?;

                    let mut wb2 = WordBuf::new(wb1.len() + 1)?;
                    wb2[..wb1.len()].copy_from_slice(&wb1);
                    wb2[wb1.len()] = 0;

                    let mut s = SliceWithSign::new_mut(&mut wb2, 1);
                    let a = SliceWithSign::new(&pair[0], 1);
                    s.add_assign(&a);

                    wb2.trunc_leading_zeroes();

                    newchunks.push(wb2);
                } else {
                    let mut wb = WordBuf::new(pair[0].len())?;
                    wb.copy_from_slice(&pair[0]);

                    newchunks.push(wb);
                }
            }

            chunks = newchunks;
            p += 1;
        }

        Ok(Mantissa::from_word_buf(chunks.remove(0)))
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
        fn tenpower_from(x: Word) -> (WordBuf, WordBuf, usize) {
            let mut wb = WordBuf::new(1).unwrap();
            wb[0] = x;

            let mut wb2 = WordBuf::new(1).unwrap();
            wb2[0] = x;

            let shift = Mantissa::maximize(&mut wb);
            assert!(wb[0] & WORD_SIGNIFICANT_BIT != 0);

            (wb, wb2, shift)
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

        for ((tenpower, tenpower2, shift), (refwb, refwb2, refshift)) in
            tenpowers.iter().zip(refval.iter())
        {
            assert_eq!(tenpower.deref() as &[Word], refwb.deref() as &[Word]);
            assert_eq!(tenpower2.deref() as &[Word], refwb2.deref() as &[Word]);
            assert_eq!(shift, refshift);
        }

        // 10^32
        Mantissa::compute_tenpowers(&mut tenpowers, 8).unwrap();
        assert_eq!(tenpowers.len(), 8);

        let (tenpow, tenpow2, shift) = &tenpowers[7];
        for (tenpow, shift) in [(tenpow, *shift), (tenpow2, 0)] {
            let mut wb = WordBuf::new(tenpow.len()).unwrap();
            wb.copy_from_slice(tenpow.deref());
            shift_slice_right(&mut wb, shift);

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
    }

    #[test]
    fn test_conv_dec() {
        let mut tenpowers = Vec::with_capacity(10);
        Mantissa::compute_tenpowers(&mut tenpowers, 16).unwrap();

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

            let mut m = Mantissa::from_word_buf(input);

            // from vec<u8>
            let input: Vec<u8> = expected.iter().rev().map(|x| *x).collect();

            let m2 = Mantissa::conv_from_dec(&input, &tenpowers).unwrap();

            assert_eq!(m.digits(), m2.digits());

            // to vec<u8>
            let k = ((input.len() * WORD_BIT_SIZE) as u64 * 301029996 / 1000000000) as usize + 1;

            let p = log2_ceil(k);

            let ret = m.conv_to_dec(1 << p, &tenpowers, p - 1).unwrap();

            let nz = ret.len() - ret.iter().rev().take_while(|x| **x == 0).count();

            assert_eq!(ret[..nz], expected);
        };

        /* let tst = [10973181860370429208, 10870792224498257307];
        let mut input = WordBuf::new(tst.len()).unwrap();
        input.copy_from_slice(&tst);
        test_input(input);
        return; */

        for _ in 0..10 {
            for l in 1..50 {
                let mut input = WordBuf::new(l).unwrap();
                for v in input.iter_mut() {
                    *v = random();
                }

                test_input(input);
            }
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn conv_to_dec_perf() {
        let n = 10000;
        let l = 5;

        let mut tenpowers = Vec::with_capacity(10);
        Mantissa::compute_tenpowers(&mut tenpowers, 16).unwrap();

        let mut inputs = Vec::with_capacity(n);

        fn basic_convert(input: &[Word]) -> Vec<u8> {
            let ten = [10];
            let mut ret = Vec::new();
            let (mut t, mut s) = Mantissa::div_basic(input, &ten).unwrap();
            loop {
                ret.push(s[0] as u8);
                t.trunc_leading_zeroes();
                if t.len() == 0 {
                    break;
                }
                let (q, r) = Mantissa::div_basic(&t, &ten).unwrap();
                t = q;
                s = r;
            }
            ret
        }

        for _ in 0..n {
            let mut input = WordBuf::new(l).unwrap();
            for v in input.iter_mut() {
                *v = random();
            }

            let m = Mantissa::from_word_buf(input);
            inputs.push(m);
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();

            for input in &inputs {
                let _ = basic_convert(input.digits());
            }
            let time = start_time.elapsed();
            println!("conv_to_dec_basic {}", time.as_millis());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();

            for input in inputs.iter_mut() {
                let k =
                    ((input.len() * WORD_BIT_SIZE) as u64 * 301029996 / 1000000000) as usize + 1;

                let p = log2_ceil(k);

                let _ = input.conv_to_dec(1 << p, &tenpowers, p - 1).unwrap();
            }

            let time = start_time.elapsed();
            println!("conv_to_dec {}", time.as_millis());
        }
    }
}
