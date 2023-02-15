//! Context is used in expressions returning `BigFloat`.

use crate::BigFloat;
use crate::Consts;
use crate::Error;
use crate::RoundingMode;

/// Context contains parameters, like rounding mode and precision, as well as constant values, and is used with `expr!` macro.
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

    /// Returns a mutable reference to the constant cache of the context.
    pub fn consts(&mut self) -> &mut Consts {
        &mut self.cc
    }

    /// Returns the value of the pi number.
    pub fn const_pi(&mut self) -> BigFloat {
        self.cc.pi(self.p, self.rm)
    }

    /// Returns the value of the Euler number.
    pub fn const_e(&mut self) -> BigFloat {
        self.cc.e(self.p, self.rm)
    }

    /// Returns the value of the natural logarithm of 2.
    pub fn const_ln2(&mut self) -> BigFloat {
        self.cc.ln_2(self.p, self.rm)
    }

    /// Returns the value of the natural logarithm of 10.
    pub fn const_ln10(&mut self) -> BigFloat {
        self.cc.ln_10(self.p, self.rm)
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

/// Represents a type that can be used as context in `expr!` macro.
///
/// ## Examples
///
/// ```
/// # use astro_float_num::RoundingMode;
/// # use astro_float_num::Consts;
/// # use astro_float_num::ctx::Contextable;
///
/// let p = 123;
/// let rm = RoundingMode::Down;
/// let mut cc = Consts::new().expect("Constants cache allocated");
/// let pi = cc.pi(p, rm);
///
/// // Make context out of tuple.
/// let mut ctx = (p, rm, &mut cc);
///
/// assert_eq!(p, ctx.precision());
/// assert_eq!(rm, ctx.rounding_mode());
/// assert_eq!(pi, ctx.const_pi());
/// ```
pub trait Contextable {
    /// Returns the precision of the context.
    fn precision(&self) -> usize;

    /// Returns the rounding mode of the context.
    fn rounding_mode(&self) -> RoundingMode;

    /// Returns a mutable reference to the constant cache of the context.
    fn consts(&mut self) -> &mut Consts;

    /// Returns the value of the pi number.
    fn const_pi(&mut self) -> BigFloat;

    /// Returns the value of the Euler number.
    fn const_e(&mut self) -> BigFloat;

    /// Returns the value of the natural logarithm of 2.
    fn const_ln2(&mut self) -> BigFloat;

    /// Returns the value of the natural logarithm of 10.
    fn const_ln10(&mut self) -> BigFloat;
}

impl Contextable for (usize, RoundingMode, &mut Consts) {
    fn precision(&self) -> usize {
        self.0
    }

    fn rounding_mode(&self) -> RoundingMode {
        self.1
    }

    fn consts(&mut self) -> &mut Consts {
        self.2
    }

    fn const_pi(&mut self) -> BigFloat {
        let (p, rm) = (self.0, self.1);
        self.consts().pi(p, rm)
    }

    fn const_e(&mut self) -> BigFloat {
        let (p, rm) = (self.0, self.1);
        self.consts().e(p, rm)
    }

    fn const_ln2(&mut self) -> BigFloat {
        let (p, rm) = (self.0, self.1);
        self.consts().ln_2(p, rm)
    }

    fn const_ln10(&mut self) -> BigFloat {
        let (p, rm) = (self.0, self.1);
        self.consts().ln_10(p, rm)
    }
}

impl Contextable for Context {
    fn precision(&self) -> usize {
        Context::precision(self)
    }

    fn rounding_mode(&self) -> RoundingMode {
        Context::rounding_mode(self)
    }

    fn consts(&mut self) -> &mut Consts {
        Context::consts(self)
    }

    fn const_pi(&mut self) -> BigFloat {
        Context::const_pi(self)
    }

    fn const_e(&mut self) -> BigFloat {
        Context::const_e(self)
    }

    fn const_ln2(&mut self) -> BigFloat {
        Context::const_ln2(self)
    }

    fn const_ln10(&mut self) -> BigFloat {
        Context::const_ln10(self)
    }
}
