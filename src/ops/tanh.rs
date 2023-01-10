//! Hyperbolic tangent.

use crate::common::consts::FIFTEEN;
use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::defs::EXPONENT_MAX;
use crate::num::BigFloatNumber;
use crate::Consts;

impl BigFloatNumber {
    /// Computes the hyperbolic tangent of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// This function requires constants cache `cc` for computing the result.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - ExponentOverflow: the result is too large or too small number.
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn tanh(&self, p: usize, rm: RoundingMode, cc: &mut Consts) -> Result<Self, Error> {
        let p = round_p(p);

        let mut x = self.clone()?;

        if self.is_zero() {
            x.set_precision(p, RoundingMode::None)?;
            return Ok(x);
        }

        let mut ret = if self.get_exponent() as isize >= -(p as isize) / 6 {
            // (e^(2*x) - 1) / (e^(2*x) + 1)

            let mut additional_prec = 2;
            if self.get_exponent() < 0 {
                additional_prec += self.get_exponent().unsigned_abs() as usize;
            }

            let p_x = p + additional_prec;
            x.set_precision(p_x, RoundingMode::None)?;

            if x.get_exponent() == EXPONENT_MAX {
                return Self::from_i8(self.get_sign().as_int(), p);
            }

            x.set_exponent(x.get_exponent() + 1);

            let xexp = match x.exp(p_x, RoundingMode::None, cc) {
                Ok(v) => Ok(v),
                Err(e) => match e {
                    Error::ExponentOverflow(s) => return Self::from_i8(s.as_int(), p),
                    Error::DivisionByZero => Err(Error::DivisionByZero),
                    Error::InvalidArgument => Err(Error::InvalidArgument),
                    Error::MemoryAllocation(a) => Err(Error::MemoryAllocation(a)),
                },
            }?;

            let d1 = xexp.sub(&ONE, p_x, RoundingMode::None)?;
            let d2 = xexp.add(&ONE, p_x, RoundingMode::None)?;

            d1.div(&d2, p_x, RoundingMode::None)?
        } else {
            // short series: x - x^3/3 + 2*x^5/15

            let p_x = p + 2;
            x.set_precision(p_x, RoundingMode::None)?;

            let xx = x.mul(&x, p_x, RoundingMode::None)?;
            let x3 = xx.mul(&x, p_x, RoundingMode::None)?;
            let p1 = x3.div(&THREE, p_x, RoundingMode::None)?;

            if p1.is_zero() {
                if rm as u32 & 0b11110 != 0 {
                    x.add_correction(true)
                } else {
                    Ok(x)
                }
            } else {
                let ret = x.sub(&p1, p_x, RoundingMode::None)?;

                let mut x5 = x3.mul(&xx, p_x, RoundingMode::None)?;
                x5.set_exponent(x5.get_exponent() + 1);
                let p2 = x5.div(&FIFTEEN, p_x, RoundingMode::None)?;

                if p2.is_zero() {
                    if rm as u32 & 0b11110 != 0 {
                        ret.add_correction(false)
                    } else {
                        Ok(ret)
                    }
                } else {
                    ret.add(&p2, p_x, RoundingMode::None)
                }
            }?
        };

        ret.set_precision(p, rm)?;

        Ok(ret)
    }
}

#[cfg(test)]
mod tests {

    use crate::common::util::random_subnormal;

    use super::*;

    #[test]
    fn test_tanh() {
        let p = 320;
        let mut cc = Consts::new().unwrap();
        let rm = RoundingMode::ToEven;
        let mut n1 = BigFloatNumber::from_word(1, p).unwrap();
        n1.set_exponent(0);
        let _n2 = n1.tanh(p, rm, &mut cc).unwrap();
        //println!("{:?}", n2.format(crate::Radix::Dec, rm).unwrap());

        // asymptotic & extrema testing
        let p = 640;
        let n1 = BigFloatNumber::parse("8.00000000000000100000000000000010B6200000000000000000000000000002E8B9840AAAAAAAAAAAAAAAAAAAAAAAAADE85C5950B78E38E38E38E38E38E38E3902814A92D7C21CDB6DB6DB6DB6DB6E_e+1", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.tanh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF3455354A958B21BA74F856FDC3BA2D793AEBE0E1D1ADF118BD9D0B592FF14C815D2C_e-1", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        assert!(n2.cmp(&n3) == 0);

        // near zero
        let p = 448;
        let n1 = BigFloatNumber::parse("-4.029AC2B966FC8CD896222A09593F0751477AD7BA9C969E57290BDE947A2E1514DF2901A1C5624013106A5197035DCA72C221BA963E190A20_e-13", crate::Radix::Hex, p, RoundingMode::None).unwrap();
        let n2 = n1.tanh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("-4.029AC2B966FC8CD896222A09593F0751477AC23B7FED67E140D1714FFCEC504D75DF70C388B621AF2FBC77C90C98C50F852D65BEDA273128_e-13", crate::Radix::Hex, p, RoundingMode::None).unwrap();

        // println!("{:?}", n1.format(crate::Radix::Hex, rm).unwrap());
        // println!("{:?}", n2.format(crate::Radix::Hex, rm).unwrap());

        assert!(n2.cmp(&n3) == 0);

        let d1 = BigFloatNumber::max_value(p).unwrap();
        let d2 = BigFloatNumber::min_value(p).unwrap();

        assert!(d1.tanh(p, rm, &mut cc).unwrap().cmp(&ONE) == 0);
        assert!(d2.tanh(p, rm, &mut cc).unwrap().cmp(&ONE.neg().unwrap()) == 0);

        let d3 = BigFloatNumber::min_positive(p).unwrap();
        let zero = BigFloatNumber::new(1).unwrap();
        let n1 = random_subnormal(p);

        assert!(d3.tanh(p, rm, &mut cc).unwrap().cmp(&d3) == 0);
        assert!(zero.tanh(p, rm, &mut cc).unwrap().is_zero());
        assert!(n1.tanh(p, rm, &mut cc).unwrap().cmp(&n1) == 0);
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn tanh_perf() {
        let p = 160;
        let mut cc = Consts::new().unwrap();
        let mut n = vec![];
        for _ in 0..10000 {
            n.push(BigFloatNumber::random_normal(p, 0, 5).unwrap());
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.tanh(p, RoundingMode::ToEven, &mut cc).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
