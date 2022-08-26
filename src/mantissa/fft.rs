//! Multiplication with FFT.

use crate::common::util::log2_ceil;
use crate::common::util::sqrt_int;
use crate::defs::DIGIT_BIT_SIZE;
use crate::defs::DIGIT_MAX;
use crate::defs::Error;
use crate::defs::Digit;
use crate::mantissa::Mantissa;
use crate::mantissa::buf::DigitBuf;
use crate::mantissa::util::SliceWithSign;
use itertools::izip;
use smallvec::SmallVec;


impl Mantissa {

    fn fft_w_shift(j: usize, k: usize) -> usize {

        let mut j = j as u64;

        j = ((j >> 1 ) & 0x5555555555555555) | ((j & 0x5555555555555555) << 1 );
        j = ((j >> 2 ) & 0x3333333333333333) | ((j & 0x3333333333333333) << 2 );
        j = ((j >> 4 ) & 0x0F0F0F0F0F0F0F0F) | ((j & 0x0F0F0F0F0F0F0F0F) << 4 );
        j = ((j >> 8 ) & 0x00FF00FF00FF00FF) | ((j & 0x00FF00FF00FF00FF) << 8 );
        j = ((j >> 16) & 0x0000FFFF0000FFFF) | ((j & 0x0000FFFF0000FFFF) << 16);
        j = ( j >> 32                      ) | ( j                       << 32);

        j >>= core::mem::size_of::<u64>()*8 - k;

        j as usize
    }

    #[inline]
    fn fft_butterfly(a: &mut SliceWithSign, b: &mut SliceWithSign) {
        a.add_assign(b);
        b.shift_left(1);
        b.sub_assign(a);
        b.set_sign(-b.sign());
    }

    // diagnostic with plain fft
    #[allow(dead_code)]
    fn fft3(parts: &mut [SliceWithSign], dst: &mut [SliceWithSign], w: usize, k1: usize, rev: bool) {

        let mut b = DigitBuf::new(parts[0].len() + k1).unwrap();

        for (i, dst_i) in dst.iter_mut().enumerate() {

            for (j, part_j) in parts.iter().enumerate() {

                let mut ww = (i*j) % k1;
                if rev {
                    ww = k1 - ww;
                }

                b.fill(0);
                let mut bb = SliceWithSign::new_mut(&mut b, part_j.sign());
                bb.copy_from(part_j);
                bb.shift_left(w*ww);

                dst_i.add_assign(&bb);
            }
        }
    }

    fn fft_forward(parts: &mut [SliceWithSign], w: usize, k1: usize, k: usize, s: usize) {

        if k1 == 2 {

            let (a, b) = parts.split_at_mut(s);
            Self::fft_butterfly(a.first_mut().unwrap(), b.first_mut().unwrap());

        } else {

            let k2 = k1 / 2;
            let kk = k - 1;
            let s2 = s * 2;

            Self::fft_forward(parts, w*2, k2, kk, s2);
            Self::fft_forward(&mut parts[s..], w*2, k2, kk, s2);
            
            let mut chunks = parts.chunks_mut(s2);

            for j in 0..k2 {
                let chunk = chunks.next().unwrap();
                let (a, b) = chunk.split_at_mut(s);

                let a = a.first_mut().unwrap();
                let b = b.first_mut().unwrap();

                let w_shift = Self::fft_w_shift(j, kk) * w;

                b.shift_left(w_shift);

                Self::fft_butterfly(a, b);
            }
        }
    }

    fn fft_reverse(parts: &mut [SliceWithSign], w: usize, k1: usize) {

        if k1 == 2 {

            let (a, b) = parts.split_at_mut(1);
            Self::fft_butterfly(&mut a[0], &mut b[0]);

        } else {

            let k2 = k1/2;

            Self::fft_reverse(&mut parts[..k2], w*2, k2);
            Self::fft_reverse(&mut parts[k2..], w*2, k2);

            let (p1, p2) = parts.split_at_mut(k2);
            let (mut p1i, mut p2i) = (p1.iter_mut(), p2.iter_mut());

            Self::fft_butterfly(p1i.next().unwrap(), p2i.next().unwrap());

            for j in 1..k2 {

                let (a, b) = (p1i.next().unwrap(), p2i.next().unwrap());

                let w_shift = w * (k1 - j);

                b.shift_left(w_shift);

                Self::fft_butterfly(a, b);
            }
        }
    }

    fn fft_params(n: usize) -> (usize, usize, usize, usize, usize, usize) {
        let k1 = sqrt_int(n as u32) as usize;
        let k = log2_ceil(k1);
        let k1 = 1 << k;
        let m = (n + k1 - 1) / k1;
        let n = m * k1;
        let n1 = (2*n + k1 - 1) / k1 + k;
        let n1 = ((n1 + k1 - 1) / k1) * k1;
        let t = n1 / k1;
        (n, k1, k, m, n1, t)
    }

    // decompose in parts.len() = k1 parts, each of size m
    fn fft_decompose(d: &[Digit], m: usize, parts: &mut [SliceWithSign]) {

        if m % DIGIT_BIT_SIZE == 0 {

            for (part, chunk) in parts.iter_mut().zip(d.chunks(m / DIGIT_BIT_SIZE)) {
                part[..chunk.len()].copy_from_slice(chunk);
            }

        } else {

            let chunk_sz = (m + DIGIT_BIT_SIZE - 1) / DIGIT_BIT_SIZE + 1;
            let mask = DIGIT_MAX >> (DIGIT_BIT_SIZE - (m % DIGIT_BIT_SIZE));
            let mut s = 0;
            let mut iter = parts.iter_mut();
            let mut idx;
            let mut shift;

            loop {

                idx = s / DIGIT_BIT_SIZE;
                shift = s % DIGIT_BIT_SIZE;
                if idx + chunk_sz > d.len() {
                    break;
                }

                let part = iter.next().unwrap();

                part[..chunk_sz].copy_from_slice(&d[idx..idx+chunk_sz]);
                part.shift_right(shift);
                part[chunk_sz-1] = 0;
                part[chunk_sz-2] &= mask;

                s += m;
            }

            if idx < d.len() {
                let part = iter.next().unwrap();
                part[..d.len()-idx].copy_from_slice(&d[idx..]);
                part.shift_right(shift);
            }
        }
    }

    fn fft_compute_chunks<'a>(num: &SliceWithSign, n: usize, tmp_buf: &'a mut [Digit]) -> SliceWithSign<'a> {

        let mut sign = 1;

        tmp_buf.fill(0);

        let mut acc = SliceWithSign::new_mut(tmp_buf, 1);

        for chunk in num.chunks(n / DIGIT_BIT_SIZE) {

            let n0 = SliceWithSign::new(chunk, sign);
            acc.add_assign(&n0);
            sign = -sign;
        }

        acc
    }

    // compute num*2^j mod (2^n+1) inplace
    // num and modulus should have up to n bits of additional free space for shifting.
    // tmp_buf is a reusable buffer of size == num.len().
    fn fft_mul_mod(num: &mut SliceWithSign, j: usize, n: usize, modulus: &mut SliceWithSign, tmp_buf: &mut [Digit]) {

        debug_assert!(n % DIGIT_BIT_SIZE == 0);

        let shift = j % n;
        let q = j / n;

        num.shift_left(shift);

        let mut acc = Self::fft_compute_chunks(num, n, tmp_buf);

        modulus.shift_left(shift);

        while acc.sign() < 0 {
            acc.add_assign(modulus);
        }

        modulus.shift_right(shift);

        while acc.cmp(modulus) >= 0 {
            acc.sub_assign(modulus);
        }

        if q & 1 != 0 {
            acc.set_sign(-acc.sign());
            if acc.sign() < 0 {
                acc.add_assign(modulus);
            }
        }

        num.copy_from_slice(tmp_buf);
    }

    // compute num / 2^j mod (2^n+1) inplace
    // num should have up to 2*n bits of additional free space for shifting.
    // tmp_buf is a reusable buffer of size == num.len().
    fn fft_div_mod(num: &mut SliceWithSign, j: usize, n: usize, modulus: &SliceWithSign, tmp_buf: &mut [Digit]) {

        debug_assert!(n % DIGIT_BIT_SIZE == 0);

        let n2 = n*2;
        let shift = ((j + n2 - 1) / n2) * n2 - j;

        num.shift_left(shift);

        let mut acc = Self::fft_compute_chunks(num, n, tmp_buf);

        while acc.sign() < 0 {
            acc.add_assign(modulus);
        }

        while acc.cmp(modulus) >= 0 {
            acc.sub_assign(modulus);
        }

        num.copy_from_slice(tmp_buf);
    }

    fn fft_prepare_parts(buf: &mut [Digit], k1: usize, part_len: usize) -> Result<SmallVec<[SliceWithSign; 0]>, Error> {

        let mut parts = SmallVec::<[SliceWithSign; 0]>::new();
        parts.try_reserve_exact(k1).map_err(Error::MemoryAllocation)?;

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
    fn fft_mul(d1: &[Digit], d2: &[Digit], d3: &mut [Digit]) -> Result<(), Error> {

        let l: usize = (d1.len() + d2.len())*DIGIT_BIT_SIZE;

        let (_n, k1, k, m, n1, t) = Self::fft_params(l);

        let w = t*2;
        let part_len = (n1 + (k1*w + 3)*k) / DIGIT_BIT_SIZE + 1;

        let mut buf = DigitBuf::new(4*k1*part_len + 3*part_len)?;
        buf.fill(0);
        let (parts1_buf, rest) = buf.split_at_mut(k1*part_len);
        let (parts2_buf, rest) = rest.split_at_mut(k1*part_len);
        let (parts3_buf, rest) = rest.split_at_mut(k1*2*part_len);
        //let (thres_buf, rest) = rest.split_at_mut(2*part_len);
        let (modulus_buf, rest) = rest.split_at_mut(part_len);
        let tmp_buf = rest;

        let mut parts1 = Self::fft_prepare_parts(parts1_buf, k1, part_len)?;
        let mut parts2 = Self::fft_prepare_parts(parts2_buf, k1, part_len)?;
        let mut parts3 = Self::fft_prepare_parts(parts3_buf, k1, part_len*2)?;

        Self::fft_decompose(d1, m, &mut parts1);
        Self::fft_decompose(d2, m, &mut parts2);

        let mut modulus = SliceWithSign::new_mut(modulus_buf, 1);
        modulus[0] = 1;
        modulus.shift_left(n1);
        modulus[0] = 1;

        //let mut thres = SliceWithSign::new_mut(thres_buf, 1);

        for (j, (part1, part2)) in parts1.iter_mut().zip(parts2.iter_mut()).enumerate() {
            Self::fft_mul_mod(part1, t*j, n1, &mut modulus, &mut tmp_buf[..part_len]);
            Self::fft_mul_mod(part2, t*j, n1, &mut modulus, &mut tmp_buf[..part_len]);
        }

        Self::fft_forward(&mut parts1, w, k1, k, 1);
        Self::fft_forward(&mut parts2, w, k1, k, 1);

        for (part1, part2) in parts1.iter_mut().zip(parts2.iter_mut()) {
            Self::fft_mul_mod(part1, 0, n1, &mut modulus, &mut tmp_buf[..part_len]);
            Self::fft_mul_mod(part2, 0, n1, &mut modulus, &mut tmp_buf[..part_len]);
        }

        for (part1, part2, part3) in izip!(parts1.iter(), parts2.iter(), parts3.iter_mut()) {

            Self::mul_unbalanced(part1, part2, part3)?;

            part3.set_sign(part1.sign() * part2.sign());

            Self::fft_mul_mod(part3, 0, n1, &mut modulus, tmp_buf);
        }

        Self::fft_reverse(&mut parts3, w, k1);

        d3.fill(0);

        for (j, part3) in parts3.iter_mut().enumerate() {

            Self::fft_div_mod(part3, k + t*j, n1, &modulus, tmp_buf);

            while part3.sign() < 0 && !part3.is_zero() {
                part3.add_assign(&modulus);
            }

            /* thres[m*2 / DIGIT_BIT_SIZE] = 0;
            thres[m*2 / DIGIT_BIT_SIZE + 1] = 0;
            thres[0] = (j + 1) as Digit;
            thres.shift_left(m*2);
            if part3.cmp(&thres) >= 0 {
                part3.sub_assign(&modulus);
            } */

            let jm = j * m;
            let idx = jm / DIGIT_BIT_SIZE;
            let shift = jm % DIGIT_BIT_SIZE;

            if idx >= d3.len() {
                break;
            }

            let mut out = SliceWithSign::new_mut(&mut d3[idx..], 1);
            part3.shift_left(shift);
            out.add_assign(part3);
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

    #[test]
    fn test_fft_mul() {

        // d1*d2
        let s1 = [1975132958, 2865607635, 3785004856, 2329109360, 82327679, 1315874535, 144553447, 431779413];
        let s2 = [1725562336, 92718951, 4168989748, 1276933861, 3499392949, 562806663, 6667756, 549355095];

        let ref_s = [2952880192u32, 1958788151, 2761307956, 531469294, 1413181254, 1343888367, 3454361913, 2408236624, 623340488, 2932102354, 1849986687, 259604987, 515123688, 3669028854, 26324828, 55227480];
        
        let mut ret_s = [0; 16];
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);


        // d1*d2
        let s1 = [2628292838, 2277283921, 3515294573, 3177772552, 0];
        let s2 = [1623732616, 2662366248, 1730446853, 817631908, 0];
        
        let ref_s = [4042850352, 2189439054, 3381778450, 3266026783, 2425920717, 2277314239, 1520284461, 604951809, 0, 0];
        
        let mut ret_s = [0; 10];
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
        let mut s1 = [0 as Digit; 100];
        let mut s2 = [0 as Digit; 100];

        for (i, v) in s1.iter_mut().enumerate() {
            *v = i as Digit;
        }
        for (i, v) in s2.iter_mut().enumerate() {
            *v = i as Digit + 1;
        }

        let mut ref_s = [0; 200];
        mul(&s1, &s2, &mut ref_s);

        let mut ret_s = [0; 200];
        Mantissa::fft_mul(&s1, &s2, &mut ret_s).unwrap();

        assert!(ret_s == ref_s);

        // 999..99 * 999..99
        let s1 = [Digit::MAX; 50];
        let s2 = [Digit::MAX; 50];
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
        for _ in 0..100 {

            let s1 = random_slice(30, 50);
            let s2 = random_slice(30, 50);

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
    fn fft_mul_perf() {

        for _ in 0..5 {
            let sz = 3840;
            let f = random_slice(459270, 459270);
            let mut n = vec![];
            let mut ret = DigitBuf::new(sz + 459270).unwrap();
            let l = 2;
            for _ in 0..l {
                let mut v = random_slice(sz, sz);
                v.resize(v.len() + f.len(), 0);
                n.push(v);
            }
            
            let start_time = std::time::Instant::now();
            for ni in n.drain(..) {
                Mantissa::fft_mul(&ni, &f, &mut ret).unwrap();
            }
            let time = start_time.elapsed();
            println!("fft_mul {}", time.as_millis());

            let mut ret = vec![];
            ret.resize(sz + f.len(), 0);
            for _ in 0..l {
                n.push(random_slice(sz, sz));
            }

            let start_time = std::time::Instant::now();
            for ni in n.drain(..) {
                mul(&ni, &f, &mut ret);
            }
            let time = start_time.elapsed();
            println!("mul  {}", time.as_millis());
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