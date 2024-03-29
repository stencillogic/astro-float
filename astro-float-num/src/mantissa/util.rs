//! Auxiliary structures.

use crate::{
    common::{buf::WordBuf, util::log2_floor},
    defs::WORD_SIGNIFICANT_BIT,
    Error, Word, WORD_BIT_SIZE,
};

/// Length of the slice extended by extra size.
pub struct ExtendedSlice<T, V>
where
    V: Iterator<Item = T>,
{
    s: V,
    extra: usize,
    default: T,
}

impl<T, V> ExtendedSlice<T, V>
where
    V: Iterator<Item = T>,
{
    pub fn new(s: V, extra: usize, default: T) -> Self {
        ExtendedSlice { s, extra, default }
    }
}

impl<T, V> Iterator for ExtendedSlice<T, V>
where
    V: Iterator<Item = T>,
    T: Copy + Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.extra > 0 {
            self.extra -= 1;
            Some(self.default)
        } else {
            self.s.next()
        }
    }
}

/// Slice values shifted to the right by the specified amount of bits.
pub struct RightShiftedSlice<'a, T> {
    s: core::slice::Iter<'a, T>,
    bits: usize,
    prev: Option<T>,
    default: T,
    extend_sz: usize,
}

impl<'a, T> RightShiftedSlice<'a, T>
where
    T: Copy + Clone,
{
    pub fn new(s: &'a [T], shift: usize, default: T, mut extend_sz: usize) -> Self {
        let elsz = core::mem::size_of::<T>() * 8;
        let mut idx = shift / elsz;
        let bits = shift % elsz;

        if extend_sz > idx {
            extend_sz -= idx;
            idx = 0;
        } else {
            idx -= extend_sz;
            extend_sz = 0;
        }

        let mut prev = None;
        let iter = if idx < s.len() {
            let mut iter = s[idx..].iter();
            prev = iter.next().copied();
            iter
        } else {
            [].iter()
        };

        RightShiftedSlice {
            s: iter,
            bits,
            prev,
            default,
            extend_sz,
        }
    }
}

impl<'a, T> Iterator for RightShiftedSlice<'a, T>
where
    T: core::ops::Shl<usize, Output = T>
        + core::ops::Shr<usize, Output = T>
        + core::ops::BitOr<T, Output = T>
        + Copy
        + Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.extend_sz > 0 {
            self.extend_sz -= 1;
            if self.extend_sz == 0 && self.bits > 0 {
                if let Some(hi) = self.prev {
                    Some(hi << (core::mem::size_of::<T>() * 8 - self.bits))
                } else {
                    Some(self.default)
                }
            } else {
                Some(self.default)
            }
        } else if let Some(lo) = self.prev {
            self.prev = self.s.next().copied();
            if self.bits == 0 {
                Some(lo)
            } else if let Some(hi) = self.prev {
                Some((hi << (core::mem::size_of::<T>() * 8 - self.bits)) | (lo >> self.bits))
            } else {
                Some(lo >> self.bits)
            }
        } else {
            Some(self.default)
        }
    }
}

// Represent subnormal as normalized.
pub struct NormalizedView<T>
where
    T: Iterator<Item = Word>,
{
    iter: T,
    shift: usize,
    prev: Word,
    end: bool,
}

impl<T> NormalizedView<T>
where
    T: Iterator<Item = Word>,
{
    pub fn new(mut iter: T) -> Self {
        let mut shift = 0;
        let mut end = true;
        let mut prev = 0;

        for mut v in iter.by_ref() {
            if v != 0 {
                prev = v;
                while v < WORD_SIGNIFICANT_BIT {
                    v <<= 1;
                    shift += 1;
                }
                end = false;
                break;
            }
        }

        Self {
            iter,
            shift,
            prev,
            end,
        }
    }
}

impl<T> Iterator for NormalizedView<T>
where
    T: Iterator<Item = Word>,
{
    type Item = Word;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.end {
            if self.shift == 0 {
                let ret = self.prev;
                if let Some(v) = self.iter.next() {
                    self.prev = v;
                } else {
                    self.end = true;
                };
                Some(ret)
            } else {
                let mut ret = self.prev << self.shift;
                if let Some(v) = self.iter.next() {
                    ret |= v >> (WORD_BIT_SIZE - self.shift);
                    self.prev = v;
                } else {
                    self.end = true;
                };
                Some(ret)
            }
        } else {
            None
        }
    }
}

/* #[inline]
fn bitle(mut v: Word) -> usize {
    let mut bitle = 0;
    while v > 0 {
        v >>= 1;
        bitle += 1;
    }
    bitle
}

/// Prepare an initial value for calculating n-root of an argument m.
pub fn root_estimate(m: &[Word], n: usize) -> Result<WordBuf, Error> {
    debug_assert!(!m.is_empty());
    debug_assert!(*m.last().unwrap() != 0);

    let last = *m.last().unwrap();

    if m.len() < 2 {
        let mut buf = WordBuf::new(1)?;
        buf[0] = nroot_int(last, n) + 1;
        return Ok(buf);
    }

    let last_bits = bitle(last);
    let shift_bits = WORD_BIT_SIZE - last_bits;
    let all_bits = (m.len() - 1) * WORD_BIT_SIZE + last_bits;

    let mut val = m[m.len() - 1] << shift_bits | if last_bits < WORD_BIT_SIZE { m[m.len() - 2] >> last_bits } else { 0 };

    let sub_bits = all_bits % n;
    let zero_bits = all_bits / n + usize::from(sub_bits != 0);

    val >>= sub_bits;

    let root = if val == WORD_MAX {
        1 << (WORD_BIT_SIZE / 2)
    } else {
        nroot_int(val + 1, n)
    };

    let root_bits = bitle(root);
    let l = root_bits + zero_bits;

    let mut buf = WordBuf::new((l + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE)?;
    buf.fill(0);

    let idx = zero_bits / WORD_BIT_SIZE;
    let shift_bits = zero_bits % WORD_BIT_SIZE;

    buf[idx] = root << shift_bits;
    if root_bits > WORD_BIT_SIZE - shift_bits {
        buf[idx + 1] = root >> (WORD_BIT_SIZE - shift_bits);
    }

    Ok(buf)
}
 */

/// Prepare an initial value for calculating n-root of an argument m.
pub fn root_estimate(m: &[Word], n: usize) -> Result<WordBuf, Error> {
    let mut buf = WordBuf::new(m.len() / n + 1)?;

    if buf.len() > 0 {
        buf.fill(0);

        let nbits = log2_floor(*m.last().unwrap() as usize);

        *buf.last_mut().unwrap() = 1 << (nbits / n + 1); // buf.len() > 0
    }
    Ok(buf)
}
