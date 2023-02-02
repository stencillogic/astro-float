//! Auxiliary items.

use crate::{num::BigFloatNumber, Consts, Error, RoundingMode};

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

/// Compute result for argument with small exponent.
macro_rules! compute_small_exp {
    ($arg:ident, $exp:expr, $sign_inverse:expr, $p:ident, $rm:ident) => {
        if $p as isize + 1 < -($exp) {
            let mut x = $arg.clone()?;
            if $p > x.get_mantissa_max_bit_len() {
                x.set_precision($p, RoundingMode::None)?;
            }
            let mut ret = x.add_correction($sign_inverse)?;
            ret.set_precision($p, $rm)?;
            return Ok(ret);
        }
    };
}

pub(super) use compute_small_exp;
