//! Auxiliary functions.

use crate::{
    defs::{Word, WORD_BIT_SIZE, WORD_MAX, WORD_SIGNIFICANT_BIT},
    RoundingMode,
};

#[cfg(test)]
use crate::{num::BigFloatNumber, Sign, EXPONENT_MIN};

#[cfg(test)]
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

/// integer logarithm base 2 of a number.
pub fn log2_ceil(mut n: usize) -> usize {
    let mut ret = 0;
    let mut sticky = 0;
    while n > 1 {
        if n & 1 != 0 {
            sticky = 1;
        }
        ret += 1;
        n >>= 1;
    }
    ret + sticky
}

/// integer logarithm base 2 of a number.
pub fn log2_floor(mut n: usize) -> usize {
    let mut ret = 0;
    while n > 1 {
        ret += 1;
        n >>= 1;
    }
    ret
}

/// square root integer approximation.
pub fn sqrt_int(a: u32) -> u32 {
    let a = a as u64;
    let mut x = a;
    for _ in 0..20 {
        if x == 0 {
            break;
        }
        x = (a / x + x) >> 1;
    }
    x as u32
}

/// n-root integer approximation.
#[allow(dead_code)]
#[inline]
pub fn nroot_int(a: u64, n: usize) -> u64 {
    if a == 0 {
        return 0;
    }

    let a = a as i128;
    let mut x = a;
    let mut bl = 0;

    while x > 0 {
        x >>= 1;
        bl += 1;
    }
    let mut x = a >> if bl > n { bl / n - 1 } else { 0 };

    let n = n as i128;
    loop {
        let y = nroot_step(x, n, a);
        if y >= x {
            break;
        }
        x = y;
    }
    x as u64
}

#[inline]
fn nroot_step(x: i128, n: i128, a: i128) -> i128 {
    let mut xx = a;
    for _ in 0..n - 1 {
        xx /= x;
    }
    ((n - 1) * x + xx) / n
}

// cost of multiplication of two numbers with precision p.
pub fn calc_mul_cost(p: usize) -> usize {
    if p < 70 {
        p * p
    } else {
        // toom-3
        if p < 1625 {
            sqrt_int((p * p * p) as u32) as usize
        } else {
            let q = sqrt_int(p as u32) as usize;
            q * q * q
        }
    }
}

// cost of addition/subtraction of two numbers with precision p.
#[inline]
pub fn calc_add_cost(p: usize) -> usize {
    p
}

// Estimate of sqrt op cost.
#[inline]
pub fn calc_sqrt_cost(p: usize, cost_mul: usize, cost_add: usize) -> usize {
    let log3_estimate = (log2_floor(p) * 41349) >> 16;
    log3_estimate * (5 * cost_mul + 2 * cost_add) / 2
}

#[inline(always)]
pub fn add_carry(a: Word, b: Word, c: Word, r: &mut Word) -> Word {
    #[cfg(target_arch = "x86_64")]
    {
        // platform-specific operation
        unsafe { core::arch::x86_64::_addcarry_u64(c as u8, a, b, r) as Word }
    }

    #[cfg(target_arch = "x86")]
    {
        // platform-specific operation
        unsafe { core::arch::x86::_addcarry_u32(c as u8, a, b, r) as Word }
    }

    #[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
    {
        use crate::defs::DoubleWord;
        use crate::defs::WORD_BASE;

        let mut s = c as DoubleWord + a as DoubleWord + b as DoubleWord;
        if s >= WORD_BASE {
            s -= WORD_BASE;
            *r = s as Word;
            1
        } else {
            *r = s as Word;
            0
        }
    }
}

#[inline(always)]
pub fn sub_borrow(a: Word, b: Word, c: Word, r: &mut Word) -> Word {
    #[cfg(target_arch = "x86_64")]
    {
        // platform-specific operation
        unsafe { core::arch::x86_64::_subborrow_u64(c as u8, a, b, r) as Word }
    }

    #[cfg(target_arch = "x86")]
    {
        // platform-specific operation
        unsafe { core::arch::x86::_subborrow_u32(c as u8, a, b, r) as Word }
    }

    #[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
    {
        use crate::defs::DoubleWord;
        use crate::defs::WORD_BASE;

        let v1 = a as DoubleWord;
        let v2 = b as DoubleWord + c as DoubleWord;

        if v1 < v2 {
            *r = (v1 + WORD_BASE - v2) as Word;
            1
        } else {
            *r = (v1 - v2) as Word;
            0
        }
    }
}

// Shift m left by n digits.
pub fn shift_slice_left(m: &mut [Word], n: usize) {
    let idx = n / WORD_BIT_SIZE;
    let shift = n % WORD_BIT_SIZE;
    if idx >= m.len() {
        m.fill(0);
    } else if shift > 0 {
        let l = m.len() - 1;
        let end = m.as_mut_ptr();
        unsafe {
            let mut dst = end.add(l);
            let mut src = end.add(l - idx);
            loop {
                if src > end {
                    let mut d = *src << shift;
                    src = src.sub(1);
                    d |= *src >> (WORD_BIT_SIZE - shift);
                    *dst = d;
                    dst = dst.sub(1);
                } else {
                    break;
                }
            }
            *dst = *src << shift;
        }
        m[0..idx].fill(0);
    } else if idx > 0 {
        let r = m.len() - idx;
        m.copy_within(0..r, idx);
        m[..idx].fill(0);
    }
}

// Shift m left by n digits and put result in m2.
pub fn shift_slice_left_copy(m: &[Word], m2: &mut [Word], n: usize) {
    let idx = n / WORD_BIT_SIZE;
    let shift = n % WORD_BIT_SIZE;
    if idx >= m2.len() {
        m2.fill(0);
    } else if shift > 0 {
        m2[..idx].fill(0);
        let mut dst = m2[idx..].iter_mut();
        let src = m.iter();
        let mut prev = 0;
        for (a, b) in src.zip(dst.by_ref()) {
            *b = (prev >> (WORD_BIT_SIZE - shift)) | (*a << shift);
            prev = *a;
        }
        if let Some(b) = dst.next() {
            *b = prev >> (WORD_BIT_SIZE - shift);
        }
        for b in dst {
            *b = 0;
        }
    } else {
        m2[..idx].fill(0);
        let mut dst = m2[idx..].iter_mut();
        for (a, b) in m.iter().zip(dst.by_ref()) {
            *b = *a;
        }
        for b in dst {
            *b = 0;
        }
    }
}

// Shift m right by n digits.
pub fn shift_slice_right(m: &mut [Word], n: usize) {
    let idx = n / WORD_BIT_SIZE;
    let shift = n % WORD_BIT_SIZE;
    if idx >= m.len() {
        m.fill(0);
    } else if shift > 0 {
        let l = m.len();
        let mut dst = m.as_mut_ptr();
        unsafe {
            let end = dst.add(l - 1);
            let mut src = dst.add(idx);
            loop {
                if src < end {
                    let mut d = *src >> shift;
                    src = src.add(1);
                    d |= *src << (WORD_BIT_SIZE - shift);
                    *dst = d;
                    dst = dst.add(1);
                } else {
                    break;
                }
            }
            *dst = *src >> shift;
        }
        m[l - idx..].fill(0);
    } else if idx > 0 {
        let r = m.len() - idx;
        m.copy_within(idx.., 0);
        m[r..].fill(0);
    }
}

pub fn count_leading_zeroes_skip_first(m: &[Word]) -> usize {
    let mut iter = m.iter().rev();
    let mut w;
    let mut ret = 0;

    if let Some(v) = iter.next() {
        w = *v & (WORD_MAX >> 1);

        while w == 0 {
            ret += WORD_BIT_SIZE;

            w = match iter.next() {
                Some(v) => *v,
                None => break,
            }
        }

        if w != 0 {
            while w & WORD_SIGNIFICANT_BIT == 0 {
                w <<= 1;
                ret += 1;
            }
        }
    }

    ret
}

pub fn count_leading_ones(m: &[Word]) -> usize {
    let mut ret = 0;

    for &v in m.iter().rev() {
        if v == WORD_MAX {
            ret += WORD_BIT_SIZE;
        } else {
            let mut v = v;

            while v & WORD_SIGNIFICANT_BIT != 0 {
                v <<= 1;
                ret += 1;
            }

            break;
        }
    }

    ret
}

/// Round precision to word bounday.
pub fn round_p(p: usize) -> usize {
    ((p.saturating_add(WORD_BIT_SIZE - 1)) / WORD_BIT_SIZE) * WORD_BIT_SIZE
}

// Convert rounding mode for an opposite sign.
pub fn invert_rm_for_sign(rm: RoundingMode) -> RoundingMode {
    if rm == RoundingMode::Up {
        RoundingMode::Down
    } else if rm == RoundingMode::Down {
        RoundingMode::Up
    } else {
        rm
    }
}

pub fn find_one_from(slice: &[Word], start_pos: usize) -> Option<usize> {
    let start_idx = start_pos / WORD_BIT_SIZE;
    if start_idx >= slice.len() {
        None
    } else {
        let mut iter = slice.iter().rev().skip(start_idx);
        if let Some(v) = iter.next() {
            let mut d = *v;

            let start_bit = start_pos % WORD_BIT_SIZE;
            let mut shift = start_pos;

            d <<= start_bit;

            if d != 0 {
                while d & WORD_SIGNIFICANT_BIT == 0 {
                    d <<= 1;
                    shift += 1;
                }

                return Some(shift);
            }

            shift += WORD_BIT_SIZE - start_bit;

            for v in iter {
                d = *v;

                if d != 0 {
                    while d & WORD_SIGNIFICANT_BIT == 0 {
                        d <<= 1;
                        shift += 1;
                    }

                    return Some(shift);
                }

                shift += WORD_BIT_SIZE;
            }
        }

        None
    }
}

/// Returns random subnormal number.
#[cfg(test)]
pub(crate) fn random_subnormal(p: usize) -> BigFloatNumber {
    let p = round_p(if p < 3 * WORD_BIT_SIZE { 3 * WORD_BIT_SIZE } else { p });
    let n = p - rand::random::<usize>() % (2 * WORD_BIT_SIZE) - 1;
    let mut m = Vec::with_capacity(p / WORD_BIT_SIZE);

    for _ in 0..n / WORD_BIT_SIZE {
        m.push(rand::random::<Word>());
    }

    if n % WORD_BIT_SIZE > 0 {
        let w =
            (rand::random::<Word>() | WORD_SIGNIFICANT_BIT) >> (WORD_BIT_SIZE - n % WORD_BIT_SIZE);
        m.push(w);
    } else {
        *m.last_mut().unwrap() |= WORD_SIGNIFICANT_BIT;
    }

    m.resize(p / WORD_BIT_SIZE, 0);

    let s = if rand::random::<u8>() & 1 == 0 { Sign::Pos } else { Sign::Neg };

    BigFloatNumber::from_raw_parts(&m, n, s, EXPONENT_MIN, false).unwrap()
}

#[cfg(test)]
#[inline]
pub fn rand_p() -> usize {
    rand::random::<usize>() % 1000 + crate::defs::DEFAULT_P
}

// test add_carry and sub_borrow performance.
/* #[test]
fn test_carry() {
    for _ in 0..5 {
        let mut v = vec![];
        for _ in 0..100000 {
            let mut t = vec![];
            for _ in 0..1024 {
                t.push(rand::random::<Word>());
            }
            v.push(t);
        }

        let start_time = std::time::Instant::now();

        for slice in v.iter_mut() {
            shift_slice_right(slice, rand::random::<usize>() % 1000);
        }

        let time = start_time.elapsed();
        println!("{}", time.as_millis());

        let mut v = vec![];
        for _ in 0..100000 {
            let mut t = vec![];
            for _ in 0..1024 {
                t.push(rand::random::<Word>());
            }
            v.push(t);
        }

        let start_time = std::time::Instant::now();

        for slice in v.iter_mut() {
            shift_slice_left(slice, rand::random::<usize>() % 1000);
        }

        let time = start_time.elapsed();
        println!("{}", time.as_millis());
    }
}
 */
