//! Auxiliary items.

use crate::{RoundingMode, Error, BigFloatNumber, Consts};

impl BigFloatNumber {
    
    /// Reduce `self` to interval (-2*pi; 2*pi)
    pub(crate) fn reduce_trig_arg(&self, cc: &mut Consts, rm: RoundingMode) -> Result<Self, Error> {

        if self.get_exponent() > 2 {

            let mut pi = cc.pi(self.get_mantissa_max_bit_len() + self.get_exponent() as usize, rm)?;

            pi.set_exponent(pi.get_exponent() + 1);

            self.rem(&pi, rm)

        } else {

            self.clone()
        }
    }
}