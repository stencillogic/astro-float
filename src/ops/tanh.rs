//! Hyperbolic tangent.

use crate::common::consts::FIFTEEN;
use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::defs::EXPONENT_MAX;
use crate::num::BigFloatNumber;
use crate::Consts;

impl BigFloatNumber {
    /// Computes the hyperbolic tangent of a number. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn tanh(&self, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let mut x = self.clone()?;

        if self.get_exponent() as isize >= -(self.get_mantissa_max_bit_len() as isize) / 6 {
            // (e^(2*x) - 1) / (e^(2*x) + 1)

            let mut additional_prec = 2;
            if self.get_exponent() < 0 {
                additional_prec += self.get_exponent().unsigned_abs() as usize;
            }

            x.set_precision(
                x.get_mantissa_max_bit_len() + additional_prec,
                RoundingMode::None,
            )?;

            if x.get_exponent() == EXPONENT_MAX {
                return Err(Error::ExponentOverflow(self.get_sign()));
            }

            x.set_exponent(x.get_exponent() + 1);

            let xexp = x.exp(RoundingMode::None, cc)?;

            let d1 = xexp.sub(&ONE, RoundingMode::None)?;
            let d2 = xexp.add(&ONE, RoundingMode::None)?;

            let mut ret = d1.div(&d2, RoundingMode::None)?;

            ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

            Ok(ret)
        } else {
            // short series: x - x^3/3 + 2*x^5/15

            x.set_precision(x.get_mantissa_max_bit_len() + 2, RoundingMode::None)?;

            let xx = x.mul(&x, RoundingMode::None)?;
            let x3 = xx.mul(&x, RoundingMode::None)?;
            let p1 = x3.div(&THREE, RoundingMode::None)?;

            let mut ret = x.sub(&p1, RoundingMode::None)?;

            let mut x5 = x3.mul(&xx, RoundingMode::None)?;
            x5.set_exponent(x5.get_exponent() + 1);
            let p2 = x5.div(&FIFTEEN, RoundingMode::None)?;

            ret = ret.add(&p2, RoundingMode::None)?;

            ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

            Ok(ret)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_tanh() {
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, 320).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.tanh(rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // asymptotic & extrema testing
        let n1 = BigFloatNumber::parse("8.00000000000000100000000000000010B6200000000000000000000000000002E8B9840AAAAAAAAAAAAAAAAAAAAAAAAADE85C5950B78E38E38E38E38E38E38E3902814A92D7C21CDB6DB6DB6DB6DB6E_e+1", crate::Radix::Hex, 640, RoundingMode::None).unwrap();
        let n2 = n1.tanh(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF3455354A958B21BA74F856FDC3BA2D793AEBE0E1D1ADF118BD9D0B592FF14C815D2C_e-1", crate::Radix::Hex, 640, RoundingMode::None).unwrap();

        assert!(n2.cmp(&n3) == 0);

        // near zero
        let n1 = BigFloatNumber::parse("-4.029AC2B966FC8CD896222A09593F0751477AD7BA9C969E57290BDE947A2E1514DF2901A1C5624013106A5197035DCA72C221BA963E190A20_e-13", crate::Radix::Hex, 448, RoundingMode::None).unwrap();
        let n2 = n1.tanh(rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("-4.029AC2B966FC8CD896222A09593F0751477AC23B7FED67E140D1714FFCEC504D75DF70C388B621AF2FBC77C90C98C50F852D65BEDA273128_e-13", crate::Radix::Hex, 448, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Hex, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn tanh_perf() {
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(160, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.tanh(RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
