//! Auxiliary structures.

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
