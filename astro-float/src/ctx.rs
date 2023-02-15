//! Context is used in expressions returning BigFloat.

use crate::Consts;
use crate::Error;
use crate::RoundingMode;

/// Context contains parameters, like rounding mode and precision, as well as constant values.
#[derive(Debug)]
pub struct Context {
    cc: Consts,
    p: usize,
    rm: RoundingMode,
}

impl Context {
    /// Create a new context.
    pub fn new(p: usize, rm: RoundingMode, cc: Consts) -> Self {
        Context { cc, p, rm }
    }

    /// Destructures the context and returns its parts.
    pub fn to_raw_parts(self) -> (usize, RoundingMode, Consts) {
        let Context { p, rm, cc } = self;
        (p, rm, cc)
    }

    /// Sets the precision of the context.
    pub fn set_precision(&mut self, p: usize) {
        self.p = p;
    }

    /// Sets the rounding mode of the context.
    pub fn set_rounding_mode(&mut self, rm: RoundingMode) {
        self.rm = rm;
    }

    /// Sets the constant cache of the context.
    pub fn set_consts(&mut self, cc: Consts) {
        self.cc = cc;
    }

    /// Returns the precision of the context.
    pub fn precision(&self) -> usize {
        self.p
    }

    /// Returns the rounding mode of the context.
    pub fn rounding_mode(&self) -> RoundingMode {
        self.rm
    }

    /// Returns a reference to the constant cache of the context.
    pub fn consts(&self) -> &Consts {
        &self.cc
    }

    /// Returns a mutable reference to the constant cache of the context.
    pub fn consts_mut(&mut self) -> &mut Consts {
        &mut self.cc
    }

    /// Clones `self` and returns the cloned context.
    ///
    /// # Errors
    ///
    /// - MemoryAllocation: failed to allocate memory for the constants cache.
    pub fn clone(&self) -> Result<Self, Error> {
        let cc = Consts::new()?;
        Ok(Context {
            p: self.p,
            rm: self.rm,
            cc,
        })
    }
}
