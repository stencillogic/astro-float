//! Multiplication with FFT.

use crate::common::buf::WordBuf;
use crate::common::int::SliceWithSign;
use crate::common::util::add_carry;
use crate::common::util::log2_ceil;
use crate::common::util::shift_slice_left_copy;
use crate::common::util::sqrt_int;
use crate::common::util::sub_borrow;
use crate::defs::Error;
use crate::defs::Word;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_MAX;
use crate::mantissa::Mantissa;
use itertools::izip;
use smallvec::SmallVec;

impl Mantissa {
    fn fft_w_shift(j: usize, k: usize) -> usize {
        let mut j = j as u64;

        j = ((j >> 1) & 0x5555555555555555) | ((j & 0x5555555555555555) << 1);
        j = ((j >> 2) & 0x3333333333333333) | ((j & 0x3333333333333333) << 2);
        j = ((j >> 4) & 0x0F0F0F0F0F0F0F0F) | ((j & 0x0F0F0F0F0F0F0F0F) << 4);
        j = ((j >> 8) & 0x00FF00FF00FF00FF) | ((j & 0x00FF00FF00FF00FF) << 8);
        j = ((j >> 16) & 0x0000FFFF0000FFFF) | ((j & 0x0000FFFF0000FFFF) << 16);
        j = (j >> 32) | (j << 32);

        j >>= core::mem::size_of::<u64>() * 8 - k;

        j as usize
    }

    #[inline]
    fn fft_butterfly(
        a: &mut SliceWithSign,
        b: &mut SliceWithSign,
        n1: usize,
        modulus: &SliceWithSign,
    ) {
        debug_assert!(a.sign() > 0 && b.sign() > 0);

        // cmp
        let mut b_gt_a = false;
        for (a, b) in a.iter().rev().zip(b.iter().rev()) {
            if *a != *b {
                b_gt_a = *b > *a;
                break;
            }
        }

        let mut c1 = 0;
        let mut c2 = 0;
        let iter1 = a.iter_mut();
        let iter2 = b.iter_mut();
        for (a, b) in iter1.zip(iter2) {
            let mut v1 = *a;
            let mut v2 = *b;

            c1 = add_carry(v1, v2, c1, a);

            if b_gt_a {
                core::mem::swap(&mut v1, &mut v2);
            }

            c2 = sub_borrow(v1, v2, c2, b);
        }
        debug_assert!(c1 == 0 && c2 == 0);

        if b_gt_a {
            b.set_sign(-b.sign());
        }

        Self::fft_normalize(a, n1, modulus);
        Self::fft_normalize(b, n1, modulus);
    }

    // diagnostic with plain fft
    #[allow(dead_code)]
    fn fft3(
        parts: &mut [SliceWithSign],
        dst: &mut [SliceWithSign],
        w: usize,
        k1: usize,
        rev: bool,
    ) {
        let mut b = WordBuf::new(parts[0].len() + k1).unwrap();

        for (i, dst_i) in dst.iter_mut().enumerate() {
            for (j, part_j) in parts.iter().enumerate() {
                let mut ww = (i * j) % k1;
                if rev {
                    ww = k1 - ww;
                }

                b.fill(0);
                let mut bb = SliceWithSign::new_mut(&mut b, part_j.sign());
                bb.copy_from(part_j);
                bb.shift_left(w * ww);

                dst_i.add_assign(&bb);
            }
        }
    }

    fn fft_forward(
        parts: &mut [SliceWithSign],
        w: usize,
        k1: usize,
        k: usize,
        s: usize,
        n1: usize,
        modulus: &SliceWithSign,
        tmp_buf: &mut [Word],
    ) {
        if k1 == 2 {
            let (a, b) = parts.split_at_mut(s);
            Self::fft_butterfly(a.first_mut().unwrap(), b.first_mut().unwrap(), n1, modulus);
        } else {
            let k2 = k1 / 2;
            let kk = k - 1;
            let s2 = s * 2;

            Self::fft_forward(parts, w * 2, k2, kk, s2, n1, modulus, tmp_buf);
            Self::fft_forward(&mut parts[s..], w * 2, k2, kk, s2, n1, modulus, tmp_buf);

            let mut chunks = parts.chunks_mut(s2);

            for j in 0..k2 {
                let chunk = chunks.next().unwrap();
                let (a, b) = chunk.split_at_mut(s);

                let a = a.first_mut().unwrap();
                let b = b.first_mut().unwrap();

                let w_shift = Self::fft_w_shift(j, kk) * w;

                Self::fft_mul_mod(b, w_shift, n1, modulus, tmp_buf);

                Self::fft_butterfly(a, b, n1, modulus);
            }
        }
    }

    fn fft_reverse(
        parts: &mut [SliceWithSign],
        w: usize,
        k1: usize,
        n1: usize,
        modulus: &SliceWithSign,
        tmp_buf: &mut [Word],
    ) {
        if k1 == 2 {
            let (a, b) = parts.split_at_mut(1);
            Self::fft_butterfly(&mut a[0], &mut b[0], n1, modulus);
        } else {
            let k2 = k1 / 2;

            Self::fft_reverse(&mut parts[..k2], w * 2, k2, n1, modulus, tmp_buf);
            Self::fft_reverse(&mut parts[k2..], w * 2, k2, n1, modulus, tmp_buf);

            let (p1, p2) = parts.split_at_mut(k2);
            let mut iter = p1.iter_mut().zip(p2.iter_mut());

            if let Some((a, b)) = iter.next() {
                Self::fft_butterfly(a, b, n1, modulus);

                for (j, (a, b)) in iter.enumerate() {
                    let w_shift = w * (k1 - j - 1);

                    Self::fft_mul_mod(b, w_shift, n1, modulus, tmp_buf);

                    Self::fft_butterfly(a, b, n1, modulus);
                }
            }
        }
    }

    fn fft_params(n: usize) -> (usize, usize, usize, usize, usize, usize) {
        let mut k1 = sqrt_int(n as u32) as usize;
        if n / WORD_BIT_SIZE < 50000 {
            k1 /= 2;
        }
        let k = log2_ceil(k1).max(6);
        let k1 = 1 << k;
        let m = (n + k1 - 1) / k1;
        let n = m * k1;
        let n1 = (2 * n + k1 - 1) / k1 + k;
        let n1 = ((n1 + k1 - 1) / k1) * k1;
        let t = n1 / k1;
        (n, k1, k, m, n1, t)
    }

    // decompose in parts.len() = k1 parts, each of size m
    fn fft_decompose(d: &[Word], m: usize, parts: &mut [SliceWithSign]) {
        let mut parts_iter = parts.iter_mut();

        if m % WORD_BIT_SIZE == 0 {
            for (chunk, part) in d.chunks(m / WORD_BIT_SIZE).zip(parts_iter.by_ref()) {
                part[..chunk.len()].copy_from_slice(chunk);
                part[chunk.len()..].fill(0);
            }
        } else {
            let chunk_sz = (m + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE + 1;
            let mask = WORD_MAX >> (WORD_BIT_SIZE - (m % WORD_BIT_SIZE));
            let mut s = 0;
            let mut idx;
            let mut shift;

            loop {
                idx = s / WORD_BIT_SIZE;
                shift = s % WORD_BIT_SIZE;
                if idx + chunk_sz > d.len() {
                    break;
                }

                let part = parts_iter.next().unwrap();

                part[chunk_sz..].fill(0);
                part[..chunk_sz].copy_from_slice(&d[idx..idx + chunk_sz]);
                part.shift_right(shift);
                part[chunk_sz - 1] = 0;
                part[chunk_sz - 2] &= mask;

                s += m;
            }

            if idx < d.len() {
                let part = parts_iter.next().unwrap();

                part[d.len() - idx..].fill(0);
                part[..d.len() - idx].copy_from_slice(&d[idx..]);
                part.shift_right(shift);
            }
        }

        for rest in parts_iter {
            rest.fill(0);
        }
    }

    fn fft_compute_chunks<'a>(
        num: &[Word],
        n: usize,
        tmp_buf: &'a mut [Word],
        s: i8,
    ) -> SliceWithSign<'a> {
        let mut chunks = num.chunks(n / WORD_BIT_SIZE);

        if let Some(first_chunk) = chunks.next() {
            tmp_buf[first_chunk.len()..].fill(0);

            let mut acc = SliceWithSign::new_mut(tmp_buf, s);
            let n0 = SliceWithSign::new(first_chunk, s);
            acc.copy_from(&n0);

            let mut sign = -s;

            for chunk in chunks {
                let nn = SliceWithSign::new(chunk, sign);
                acc.add_assign(&nn);

                sign = -sign;
            }

            acc
        } else {
            tmp_buf.fill(0);

            SliceWithSign::new_mut(tmp_buf, 1)
        }
    }

    // results in  0 <= num < modulus, assuming abs(num) not much greater than modulus
    fn fft_normalize(num: &mut SliceWithSign, n: usize, modulus: &SliceWithSign) {
        if num.sign() < 0 && !num.is_zero() {
            let last = n / WORD_BIT_SIZE;

            while num.sign() < 0 {
                if num[last] > 0 && num[0] > 0 {
                    // simplified add
                    num[0] -= 1;
                    num[last] -= 1;
                } else {
                    num.add_assign(modulus);
                }
            }
        } else {
            let last = n / WORD_BIT_SIZE;

            while num[last] > 0 {
                if num[0] > 0 {
                    // simplified sub
                    num[0] -= 1;
                    num[last] -= 1;
                } else {
                    num.sub_assign(modulus);
                }
            }

            if num.sign() < 0 && !num.is_zero() {
                // unlikely
                num.add_assign(modulus);
            }
        }
    }

    // compute num*2^j mod (2^n+1) inplace
    // num and modulus should have up to n bits of additional free space for shifting.
    // tmp_buf is a reusable buffer of size == num.len().
    fn fft_mul_mod(
        num: &mut SliceWithSign,
        j: usize,
        n: usize,
        modulus: &SliceWithSign,
        tmp_buf: &mut [Word],
    ) {
        debug_assert!(n % WORD_BIT_SIZE == 0);

        let (work_buf, ext_buf) = tmp_buf.split_at_mut(num.len());

        let mut acc = if j == 0 {
            Self::fft_compute_chunks(num, n, work_buf, 1)
        } else {
            let shift = j % n;
            let q = j / n;

            shift_slice_left_copy(num, ext_buf, shift);

            let mut acc = Self::fft_compute_chunks(ext_buf, n, work_buf, 1);

            if q & 1 != 0 {
                acc.set_sign(-acc.sign());
            }

            acc
        };

        Self::fft_normalize(&mut acc, n, modulus);

        num.copy_from(&acc);
    }

    // compute num / 2^j mod (2^n+1) inplace
    // num should have up to n bits of additional free space for shifting.
    // tmp_buf is a reusable buffer of size == num.len().
    fn fft_div_mod(
        num: &mut SliceWithSign,
        j: usize,
        n: usize,
        modulus: &SliceWithSign,
        tmp_buf: &mut [Word],
    ) {
        debug_assert!(n % WORD_BIT_SIZE == 0);

        let n2 = n * 2;
        let mut shift = ((j + n2 - 1) / n2) * n2 - j;

        let mut s = 1;
        if shift >= n {
            shift -= n;
            s = -1;
        }

        let (work_buf, ext_buf) = tmp_buf.split_at_mut(num.len());

        shift_slice_left_copy(num, ext_buf, shift);

        let mut acc = Self::fft_compute_chunks(ext_buf, n, work_buf, s);

        Self::fft_normalize(&mut acc, n, modulus);

        num.copy_from(&acc);
    }

    fn fft_prepare_parts(
        buf: &mut [Word],
        k1: usize,
        part_len: usize,
    ) -> Result<SmallVec<[SliceWithSign; 0]>, Error> {
        let mut parts = SmallVec::<[SliceWithSign; 0]>::new();
        parts
            .try_reserve_exact(k1)
            .map_err(Error::MemoryAllocation)?;

        let mut rest = buf;

        for _ in 0..k1 {
            let (p1, p2) = rest.split_at_mut(part_len);

            let s = SliceWithSign::new_mut(p1, 1);
            parts.push(s);
            rest = p2;
        }

        Ok(parts)
    }

    // multiply two integer numbers.
    pub(super) fn fft_mul(d1: &[Word], d2: &[Word], d3: &mut [Word]) -> Result<(), Error> {
        let l: usize = (d1.len() + d2.len()) * WORD_BIT_SIZE;

        let (_n, k1, k, m, n1, t) = Self::fft_params(l);

        let w = t * 2;
        let part_len = n1 / WORD_BIT_SIZE + 1;

        let mut buf = WordBuf::new(3 * k1 * part_len + 6 * part_len)?;

        let (parts1_buf, rest) = buf.split_at_mut(k1 * part_len);
        let (parts2_buf, rest) = rest.split_at_mut(k1 * part_len);
        let (parts3_buf, rest) = rest.split_at_mut(k1 * part_len);
        //let (thres_buf, rest) = rest.split_at_mut(2*part_len);
        let (modulus_buf, rest) = rest.split_at_mut(part_len);
        let (tmp_buf, tmp_buf2) = rest.split_at_mut(part_len * 3);

        let mut parts1 = Self::fft_prepare_parts(parts1_buf, k1, part_len)?;
        let mut parts2 = Self::fft_prepare_parts(parts2_buf, k1, part_len)?;
        let mut parts3 = Self::fft_prepare_parts(parts3_buf, k1, part_len)?;

        Self::fft_decompose(d1, m, &mut parts1);
        Self::fft_decompose(d2, m, &mut parts2);

        modulus_buf.fill(0);
        modulus_buf[0] = 1;
        modulus_buf[n1 / WORD_BIT_SIZE] = 1;
        let modulus = SliceWithSign::new_mut(modulus_buf, 1);

        //let mut thres = SliceWithSign::new_mut(thres_buf, 1);

        for (j, (part1, part2)) in parts1.iter_mut().zip(parts2.iter_mut()).enumerate() {
            Self::fft_mul_mod(part1, t * j, n1, &modulus, tmp_buf);
            Self::fft_mul_mod(part2, t * j, n1, &modulus, tmp_buf);
        }

        Self::fft_forward(&mut parts1, w, k1, k, 1, n1, &modulus, tmp_buf);
        Self::fft_forward(&mut parts2, w, k1, k, 1, n1, &modulus, tmp_buf);

        for (part1, part2, part3) in izip!(parts1.iter(), parts2.iter(), parts3.iter_mut()) {
            Self::mul_unbalanced(part1, part2, tmp_buf2)?;

            part3.set_sign(part1.sign() * part2.sign());

            let mut t0 = SliceWithSign::new_mut(tmp_buf2, part3.sign());
            Self::fft_mul_mod(&mut t0, 0, n1, &modulus, tmp_buf);

            part3.copy_from_slice(&tmp_buf2[..part_len]);
        }

        Self::fft_reverse(&mut parts3, w, k1, n1, &modulus, tmp_buf);

        d3.fill(0);

        for (j, part3) in parts3.iter_mut().enumerate() {
            Self::fft_div_mod(part3, k + t * j, n1, &modulus, tmp_buf);

            while part3.sign() < 0 && !part3.is_zero() {
                part3.add_assign(&modulus);
            }

            /*             thres[m*2 / WORD_BIT_SIZE] = 0;
            thres[m*2 / WORD_BIT_SIZE + 1] = 0;
            thres[0] = (j + 1) as Word;
            thres.shift_left(m*2);
            if part3.cmp(&thres) >= 0 {
                part3.sub_assign(&modulus);
            } */

            let jm = j * m;
            let idx = jm / WORD_BIT_SIZE;
            let shift = jm % WORD_BIT_SIZE;

            if idx >= d3.len() {
                break;
            }

            let rng = if d3.len() > idx + part_len + 2 {
                idx..(idx + part_len + 2)
            } else {
                idx..d3.len()
            };
            let mut out = SliceWithSign::new_mut(&mut d3[rng], 1);
            part3.shift_left(shift);
            out.add_assign(part3);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::defs::DoubleWord;
    use crate::defs::WORD_BIT_SIZE;
    use rand::random;

    #[cfg(not(feature = "std"))]
    use alloc::vec::Vec;

    #[test]
    fn test_fft_mul() {
        // d1*d2
        let s1 = [
            1975132958, 2865607635, 3785004856, 2329109360, 82327679, 1315874535, 144553447,
            431779413,
        ];
        let s2 = [
            1725562336, 92718951, 4168989748, 1276933861, 3499392949, 562806663, 6667756, 549355095,
        ];

        let mut ref_s = [0; 16];
        let mut ret_s = [0; 16];

        mul(&s1, &s2, &mut ref_s);
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // d1*d2
        let s1 = [2628292838, 2277283921, 3515294573, 3177772552, 0];
        let s2 = [1623732616, 2662366248, 1730446853, 817631908, 0];

        let mut ref_s = [0; 10];
        let mut ret_s = [0; 10];

        mul(&s1, &s2, &mut ref_s);
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // d1*d2
        let s1 = [11, 12, 13, 14, 15, 16, 17, 18];
        let s2 = [21, 22, 23, 24, 25, 26, 27, 28];
        let mut ret_s = [0; 16];
        let mut ref_s = [0; 16];

        mul(&s1, &s2, &mut ref_s);
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // d1*d2
        let mut s1 = [0 as Word; 100];
        let mut s2 = [0 as Word; 100];

        for (i, v) in s1.iter_mut().enumerate() {
            *v = i as Word;
        }
        for (i, v) in s2.iter_mut().enumerate() {
            *v = i as Word + 1;
        }

        let mut ref_s = [0; 200];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 200];
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 999..99 * 999..99
        let s1 = [Word::MAX; 50];
        let s2 = [Word::MAX; 50];
        let mut ref_s = [0; 100];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 100];
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 0*0
        let s1 = [0, 0, 0, 0, 0, 0, 0, 0];
        let s2 = [0, 0, 0, 0, 0, 0, 0, 0];
        let mut ref_s = [0; 15];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 15];
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 1*1
        let s1 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let s2 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let mut ref_s = [0; 30];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 30];
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // random
        for _ in 0..1000 {
            let s1 = random_slice(128, 256);
            let s2 = random_slice(128, 256);

            let mut ref_s = Vec::new();
            ref_s.resize(s1.len() + s2.len(), 0);
            mul(&s1, &s2, ref_s.as_mut_slice());

            let mut ret_s = Vec::new();
            ret_s.resize(s1.len() + s2.len(), 0);
            Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

            //println!("{:?}\n{:?}\n", s1, s2);
            //println!("{:?}\n{:?}\n", ret_s, ref_s);
            assert!(ret_s == ref_s);
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn fft_mul_perf() {
        for _ in 0..5 {
            let sz = 5400;

            let f = random_slice(sz, sz);

            let mut ret1 = WordBuf::new(sz + sz).unwrap();
            let mut ret2 = WordBuf::new(sz + sz).unwrap();

            let mut n = vec![];
            let l = 100;
            for _ in 0..l {
                let v = random_slice(sz, sz);
                n.push(v);
            }

            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                Mantissa::fft_mul(ni, &f, &mut ret1).unwrap();
            }
            let time = start_time.elapsed();
            println!("fft_mul {}", time.as_millis());

            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                Mantissa::mul_unbalanced(ni, &f, &mut ret2).unwrap();
            }
            let time = start_time.elapsed();
            println!("mul_unbalanced  {}", time.as_millis());
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
