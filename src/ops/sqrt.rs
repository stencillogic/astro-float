/// Square root.

use crate::num::BigFloatNumber;
use crate::num::Error;

impl BigFloatNumber {

    /// Return square root of a number.
    ///
    /// # Errors
    ///
    /// Returns ArgumentIsNegative if `self` is less than 0.
    pub fn sqrt(&self) -> Result<Self, Error> {

        // choose initial value
        let mut n = *self;

        // Newton's method
        let mut err = *self;
        loop {
            // n = (n + d1/n)/2
            // having d1 >= 1, n >= 1, d1 >= n -> n + d1/n >= 2 => 
            // we don't expect exponent overflow or division by 0
            let n2 = n.add(&self.div(&n)?)?.div_by_2();
            let err2 = n.sub(&n2)?;
            if err2.cmp(&err) >= 0 {
                break;
            }
            err = err2;
            n = n2;
        }
        Ok(n)
    }
}


#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_sqrt() {

        let mut d1 = BigFloatNumber::from_f64(2.0).unwrap();
        let d2 = d1.sqrt().unwrap();
    }
}
