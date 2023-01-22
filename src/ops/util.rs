//! Auxiliary items.

use crate::{BigFloatNumber, Consts, Error, RoundingMode};

impl BigFloatNumber {
    /// Reduce `self` to interval (-2*pi; 2*pi)
    pub(crate) fn reduce_trig_arg(self, cc: &mut Consts, rm: RoundingMode) -> Result<Self, Error> {
        if self.get_exponent() > 2 {
            let mut pi = cc.pi_num(
                self.get_mantissa_max_bit_len() + self.get_exponent() as usize,
                rm,
            )?;

            pi.set_exponent(pi.get_exponent() + 1);

            self.rem(&pi)
        } else {
            Ok(self)
        }
    }
}

/// fast compute for small argument (mpfr compatibility)
macro_rules! fast_compute_small_arg {
    ($arg:ident, $factor:literal, $sign_inverse:literal, $p:ident, $rm:ident) => {
        if $p as isize + 1 < -($arg.get_exponent() as isize) + 2 && $rm as u32 & 0b11110 != 0 {
            let mut x = $arg.clone()?;
            x.set_precision($p, RoundingMode::None)?;
            let mut ret = x.add_correction($sign_inverse)?;
            ret.set_precision($p, $rm)?;
            return Ok(ret);
        }
    };
}

pub(super) use fast_compute_small_arg;
