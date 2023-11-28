//! Hyperbolic tangent.

use crate::common::consts::ONE;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::defs::RoundingMode;
use crate::defs::EXPONENT_MAX;
use crate::num::BigFloatNumber;
use crate::ops::util::compute_small_exp;
use crate::Consts;
use crate::Sign;
use crate::WORD_BIT_SIZE;

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

        if self.is_zero() {
            return Self::new2(p, self.sign(), self.inexact());
        }

        // prevent overflow
        if self.exponent() == EXPONENT_MAX {
            let mut ret = Self::from_i8(self.sign().to_int(), p)?;
            ret = ret.add_correction(true)?;
            ret.set_precision(p, rm)?;
            return Ok(ret);
        }

        compute_small_exp!(self, self.exponent() as isize * 2 - 1, true, p, rm);

        // (e^(2*x) - 1) / (e^(2*x) + 1)

        let mut additional_prec = 4;
        if self.exponent() < 0 {
            additional_prec += self.exponent().unsigned_abs() as usize;
        }

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p.max(self.mantissa_max_bit_len()) + p_inc;

        let mut x = self.clone()?;
        x.set_inexact(false);
        x.set_sign(Sign::Pos);

        loop {
            let p_x = p_wrk + additional_prec;
            x.set_precision(p_x, RoundingMode::None)?;

            x.set_exponent(x.exponent() + 1);

            let xexp = match x.exp(p_x, RoundingMode::FromZero, cc) {
                Ok(v) => Ok(v),
                Err(e) => match e {
                    Error::ExponentOverflow(_) => {
                        let rm_mask = if self.is_positive() {
                            0b1100 // rounding down or to zero
                        } else {
                            0b1010 // rounding up or to zero
                        };

                        let mut ret = if rm as u32 & rm_mask != 0 {
                            let mut ret = BigFloatNumber::max_value(p)?;
                            ret.set_sign(self.sign());
                            ret.set_exponent(0);
                            ret
                        } else {
                            Self::from_i8(self.sign().to_int(), p)?
                        };

                        ret.set_inexact(true);

                        return Ok(ret);
                    }
                    Error::DivisionByZero => Err(Error::DivisionByZero),
                    Error::InvalidArgument => Err(Error::InvalidArgument),
                    Error::MemoryAllocation => Err(Error::MemoryAllocation),
                },
            }?;

            let d1 = xexp.sub(&ONE, p_x, RoundingMode::Down)?;
            let d2 = xexp.add(&ONE, p_x, RoundingMode::Up)?;

            let mut ret = d1.div(&d2, p_x, RoundingMode::None)?;

            ret.set_sign(self.sign());

            if ret.try_set_precision(p, rm, p_wrk)? {
                ret.set_inexact(ret.inexact() | self.inexact());
                break Ok(ret);
            }

            p_wrk += p_inc;
            p_inc = round_p(p_wrk / 5);
        }
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
        let n1 = BigFloatNumber::parse("8.00000000000000100000000000000010B6200000000000000000000000000002E8B9840AAAAAAAAAAAAAAAAAAAAAAAAADE85C5950B78E38E38E38E38E38E38E3902814A92D7C21CDB6DB6DB6DB6DB6E_e+1", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();
        let n2 = n1.tanh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF3455354A958B21BA74F856FDC3BA2D793AEBE0E1D1ADF118BD9D0B592FF14C815D2C_e-1", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();

        assert!(n2.cmp(&n3) == 0);

        // near zero
        let p = 448;
        let n1 = BigFloatNumber::parse("-4.029AC2B966FC8CD896222A09593F0751477AD7BA9C969E57290BDE947A2E1514DF2901A1C5624013106A5197035DCA72C221BA963E190A20_e-13", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();
        let n2 = n1.tanh(p, rm, &mut cc).unwrap();
        let n3 = BigFloatNumber::parse("-4.029AC2B966FC8CD896222A09593F0751477AC23B7FED67E140D1714FFCEC504D75DF70C388B621AF2FBC77C90C98C50F852D65BEDA273128_e-13", crate::Radix::Hex, p, RoundingMode::None, &mut cc).unwrap();

        //println!("{:?}", n1.format(crate::Radix::Hex, rm, &mut cc).unwrap());
        //println!("{:?}", n2.format(crate::Radix::Hex, rm, &mut cc).unwrap());

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
