//! Buffer for holding mantissa gidits.

use crate::defs::Error;
use crate::defs::Word;
use crate::defs::WORD_BIT_SIZE;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::Index;
use core::ops::IndexMut;
use core::slice::SliceIndex;

use crate::common::util::shift_slice_left;
use crate::common::util::shift_slice_right;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

/// Buffer for holding mantissa gidits.
#[derive(Debug, Hash)]
pub struct WordBuf {
    inner: Vec<Word>,
}

impl WordBuf {
    #[inline]
    pub fn new(sz: usize) -> Result<Self, Error> {
        let mut inner = Vec::new();
        inner.try_reserve_exact(sz)?;
        unsafe {
            // values of the newely allocated words stay unitialized for performance reasons
            inner.set_len(sz);
        }
        Ok(WordBuf { inner })
    }

    #[inline]
    pub fn fill(&mut self, d: Word) {
        self.inner.fill(d);
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Decrease length of the buffer to l bits. Data is shifted.
    pub fn trunc_to(&mut self, l: usize) {
        let n = (l + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE;
        let sz = self.len();
        shift_slice_right(&mut self.inner, (sz - n) * WORD_BIT_SIZE);
        self.inner.truncate(n);
    }

    /// Decrease length of the buffer to l bits. Data is not moved.
    pub fn trunc_to_2(&mut self, l: usize) {
        let n = (l + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE;
        self.inner.truncate(n);
    }

    /// Try to exted the size to fit the precision p. Fill new elements with 0. Data is shifted to the left.
    pub fn try_extend(&mut self, p: usize) -> Result<(), Error> {
        let n = (p + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE;
        let l = self.inner.len();
        self.inner.try_reserve(n - l)?;
        unsafe {
            // values of the newely allocated words stay unitialized for performance reasons
            self.inner.set_len(n);
        }
        shift_slice_left(&mut self.inner, (n - l) * WORD_BIT_SIZE);
        Ok(())
    }

    /// Try to exted the size to fit the precision p. Fill new elements with 0. Data is not moved.
    pub fn try_extend_2(&mut self, p: usize) -> Result<(), Error> {
        let n = (p + WORD_BIT_SIZE - 1) / WORD_BIT_SIZE;
        if n > self.inner.capacity() {
            self.inner.try_reserve(n - self.inner.capacity())?;
        }
        if n > self.inner.len() {
            self.inner.resize(n, 0);
        }
        Ok(())
    }

    // Remove trailing words containing zeroes.
    pub fn trunc_trailing_zeroes(&mut self) {
        let mut n = 0;

        for v in self.inner.iter() {
            if *v == 0 {
                n += 1;
            } else {
                break;
            }
        }

        if n > 0 {
            let sz = self.len();
            shift_slice_right(&mut self.inner, n * WORD_BIT_SIZE);
            self.inner.truncate(sz - n);
        }
    }

    // Remove leading words containing zeroes.
    pub fn trunc_leading_zeroes(&mut self) {
        let mut n = 0;

        for v in self.inner.iter().rev() {
            if *v == 0 {
                n += 1;
            } else {
                break;
            }
        }

        if n > 0 {
            let sz = self.len();
            self.inner.truncate(sz - n);
        }
    }
}

impl<I: SliceIndex<[Word]>> IndexMut<I> for WordBuf {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.inner.index_mut(index)
    }
}

impl<I: SliceIndex<[Word]>> Index<I> for WordBuf {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        self.inner.index(index)
    }
}

impl Deref for WordBuf {
    type Target = [Word];

    #[inline]
    fn deref(&self) -> &[Word] {
        self.inner.deref()
    }
}

impl DerefMut for WordBuf {
    #[inline]
    fn deref_mut(&mut self) -> &mut [Word] {
        self.inner.deref_mut()
    }
}
