//! Buffer for holding mantissa gidits.


use smallvec::SmallVec;
use crate::defs::Digit;
use crate::defs::Error;
use crate::defs::DIGIT_BIT_SIZE;
use core::ops::Index;
use core::ops::IndexMut;
use core::ops::Deref;
use core::ops::DerefMut;
use core::slice::SliceIndex;


const STATIC_ALLOCATION: usize = 5;


/// Buffer for holding mantissa gidits.
#[derive(Debug)]
pub struct DigitBuf {
    inner: SmallVec<[Digit; STATIC_ALLOCATION]>,
}

impl DigitBuf {

    #[inline]
    pub fn new(sz: usize) -> Result<Self, Error> {
        let mut inner = SmallVec::new();
        inner.try_reserve_exact(sz).map_err(Error::MemoryAllocation)?;
        unsafe { inner.set_len(sz); }
        Ok(DigitBuf {
            inner,
        })
    }

    #[inline]
    pub fn fill(&mut self, d: Digit) {
        self.inner.fill(d);
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut Digit {
        self.inner.as_mut_ptr()
    }

    /// Decrease length of mantissa to l bits.
    pub fn trunc_to(&mut self, l: usize) {
        let n = (l + DIGIT_BIT_SIZE - 1)/DIGIT_BIT_SIZE;
        let sz = self.len();
        self.inner.rotate_left(sz - n);
        self.inner.truncate(n);
    }

    /// Try to exted the size to fit the precision p. Fill new elements with 0.
    pub fn try_extend(&mut self, p: usize) -> Result<(), Error> {
        let n = (p + DIGIT_BIT_SIZE - 1)/DIGIT_BIT_SIZE;
        let l = self.inner.len();
        self.inner.try_grow(n).map_err(Error::MemoryAllocation)?;
        unsafe { self.inner.set_len(n); }
        self.inner.rotate_right(n - l);
        self.inner[..l].fill(0);
        Ok(())
    }
}


impl<I: SliceIndex<[Digit]>> IndexMut<I> for DigitBuf {

    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.inner.index_mut(index)
    }
}

impl<I: SliceIndex<[Digit]>> Index<I> for DigitBuf {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        self.inner.index(index)
    }
}

impl Deref for DigitBuf {
    type Target = [Digit];

    #[inline]
    fn deref(&self) -> &[Digit] {
        self.inner.deref()
    }
}

impl DerefMut for DigitBuf {

    #[inline]
    fn deref_mut(&mut self) -> &mut [Digit] {
        self.inner.deref_mut()
    }
}