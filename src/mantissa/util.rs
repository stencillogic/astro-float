/// Length of the slice extended by extra size.
pub struct ExtendedSlice<T, V> where V: Iterator<Item = T> {
    s: V,
    extra: usize,
    default: T,
}

impl<T, V> ExtendedSlice<T, V> where V: Iterator<Item = T> {
    pub fn new(s: V, extra: usize, default: T) -> Self {
        ExtendedSlice {
            s,
            extra,
            default,
        }
    }
}

impl<T, V> Iterator for ExtendedSlice<T, V> where V: Iterator<Item = T>, T: Copy + Clone {
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

/// Slice values shifted by the specified amount of bits.
pub struct ShiftedSlice<'a, T> {
    s: core::slice::Iter<'a, T>,
    bits: usize,
    prev: Option<T>,
    default: T,
}

impl<'a, T> ShiftedSlice<'a, T> where T: Copy + Clone {
    pub fn new(s: &'a [T], shift: usize, default: T, guard: bool) -> Self {
        let elsz = core::mem::size_of::<T>()*8;
        let mut idx = shift / elsz;
        let (prev, iter) = if guard && idx == 0 {
            (Some(default), s.iter())
        } else if idx < s.len() {
            if guard {
                idx -= 1;
            }
            let mut iter = s[idx..].iter();
            let prev = iter.next().copied();
            (prev, iter)
        } else {
            (None, s.iter())
        };
        let bits = shift % elsz;
        ShiftedSlice {
            s: iter,
            bits,
            prev,
            default,
        }
    }
}


impl<'a, T> Iterator for ShiftedSlice<'a, T> 
    where T: core::ops::Shl<usize, Output = T> 
        + core::ops::Shr<usize, Output = T> 
        + core::ops::BitOr<T, Output = T> 
        + Copy
        + Clone
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(lo) = self.prev {
            self.prev = self.s.next().copied();
            if self.bits == 0 {
                Some(lo)
            } else if let Some(hi) = self.prev {
                Some((hi << (core::mem::size_of::<T>()*8 - self.bits)) | (lo >> self.bits))
            } else {
                Some(lo >> self.bits)
            }
        } else {
            Some(self.default)
        }
    }
}