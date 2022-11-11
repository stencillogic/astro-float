//! Cube root computation.

use crate::{
    num::BigFloatNumber, 
    RoundingMode, 
    defs::{Error, EXPONENT_MIN, EXPONENT_MAX}, Exponent, common::util::log2_ceil
};


impl BigFloatNumber {

    /// Computes cube root of a number. The result is rounded using the rounding mode `rm`.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn cbrt(&self, rm: RoundingMode) -> Result<Self, Error> {

        if self.is_zero() {
            return self.clone();
        }

        let mut x = self.clone()?;

        let e = x.normalize2() as isize;
        let e = self.get_exponent() as isize - e;
        let e_shift = e % 3 - 3;

        x.set_precision(x.get_mantissa_max_bit_len() + 1, RoundingMode::None)?;
        x.set_exponent(e_shift as Exponent);

        let mut iters = log2_ceil(x.get_mantissa_max_bit_len()) * 2 / 3 + 3;
        let mut ret = x.clone()?;

        while iters > 0 {
            ret = x.cbrt_step(ret)?;
            iters -= 1;
        }

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;

        let mut e_corr = ret.get_exponent() as isize + ((e as isize - e_shift as isize) / 3);

        if e_corr < EXPONENT_MIN as isize {
            let is_positive = ret.is_positive();
            if !Self::process_subnormal(&mut ret.m, &mut e_corr, rm, is_positive) {
                return Self::new(self.get_mantissa_max_bit_len());
            }
        }

        if e_corr > EXPONENT_MAX as isize {
            return Err(Error::ExponentOverflow(ret.get_sign()));
        }

        ret.set_exponent(e_corr as Exponent);

        Ok(ret)
    }

    fn cbrt_step(&self, mut xn: Self) -> Result<Self, Error> {

        // x(n+1) = 2 * x(n) * (x(n)^3 / 2 + self) / (2 * x(n)^3 + self)

        let xxn = xn.mul(&xn, RoundingMode::None)?;
        let mut xxxn = xxn.mul(&xn, RoundingMode::None)?;

        let e = xxxn.get_exponent();

        xxxn.set_exponent(e - 1);
        let d1 = xxxn.add(self, RoundingMode::None)?;

        xn.set_exponent(xn.get_exponent() + 1);
        let d2 = xn.mul(&d1, RoundingMode::None)?;

        xxxn.set_exponent(e + 1);
        let d3 = xxxn.add(self, RoundingMode::None)?;

        d2.div(&d3, RoundingMode::None)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{Exponent, common::consts::ONE, defs::{EXPONENT_MIN, EXPONENT_MAX}};

    #[cfg(feature="std")]
    use crate::Sign;

    #[test]
    fn test_cbrt() {

        /* let n1 = BigFloatNumber::from_raw_parts(
            &[10240209581698738563, 18115871017240605025],
            128, Sign::Pos, 0).unwrap();
        let n2 = n1.cbrt(RoundingMode::ToEven).unwrap();
        println!("{:?}", n1.format(crate::Radix::Dec, RoundingMode::None));
        println!("{:?}", n2.format(crate::Radix::Dec, RoundingMode::None));
        return; */

        let mut eps = ONE.clone().unwrap();
        let prec = 320;

        for _ in 0..1000 {

            let d1 = BigFloatNumber::random_normal(prec, EXPONENT_MIN, EXPONENT_MAX).unwrap();
            let d2 = d1.cbrt(RoundingMode::ToEven).unwrap();
            let d3 = d2.mul(&d2, RoundingMode::ToEven).unwrap().mul(&d2, RoundingMode::ToEven).unwrap();

            eps.set_exponent(d1.get_exponent() - prec as Exponent + 3);

            // println!("d1 {:?}", d1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
            // println!("d2 {:?}", d2.format(crate::Radix::Dec, RoundingMode::None).unwrap());
            // println!("d3 {:?}", d3.format(crate::Radix::Dec, RoundingMode::None).unwrap());

            assert!(d1.sub(&d3, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);
        }

        // MAX
        let d1 = BigFloatNumber::max_value(prec).unwrap();
        let d2 = d1.cbrt(RoundingMode::ToEven).unwrap();
        let d3 = d2.mul(&d2, RoundingMode::ToEven).unwrap().mul(&d2, RoundingMode::ToEven).unwrap();
        eps.set_exponent(d1.get_exponent() - prec as Exponent + 3);
        assert!(d1.sub(&d3, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);

        // MIN
        let d1 = BigFloatNumber::min_value(prec).unwrap();
        let d2 = d1.cbrt(RoundingMode::ToEven).unwrap();
        let d3 = d2.mul(&d2, RoundingMode::ToEven).unwrap().mul(&d2, RoundingMode::ToEven).unwrap();
        eps.set_exponent(d1.get_exponent() - prec as Exponent + 3);
        assert!(d1.sub(&d3, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);

        // MIN POSITIVE
        let d1 = BigFloatNumber::min_positive(prec).unwrap();
        let d2 = d1.cbrt(RoundingMode::ToEven).unwrap();
        let d3 = d2.mul(&d2, RoundingMode::ToEven).unwrap().mul(&d2, RoundingMode::ToEven).unwrap();
        let eps = BigFloatNumber::min_positive(prec).unwrap();
        assert!(d1.sub(&d3, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) <= 0);


        // near 1
        let d1 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC4872DC85F7E77EC487_e-1", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let d2 = d1.cbrt(RoundingMode::ToEven).unwrap();
        let d3 = BigFloatNumber::parse("F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFB9ED752A27F96D7B9ED752A27F96D8_e-1", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        //println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        let d1 = BigFloatNumber::parse("1.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC4872DC85F7E77EC487", crate::Radix::Hex, 320, RoundingMode::None).unwrap();
        let d2 = d1.cbrt(RoundingMode::ToEven).unwrap();
        let d3 = BigFloatNumber::parse("1.428A2F98D728AE223DDAB715BE250D0C288F10291631FBC05EBDC396372FC4455EE80EC7DBBEC7D2", crate::Radix::Hex, 320, RoundingMode::None).unwrap();

        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);
    }


    #[ignore]
    #[test]
    #[cfg(feature="std")]
    fn cbrt_perf() {

        let mut n = vec![];
        for _ in 0..100000 {
            let mut n0 = BigFloatNumber::random_normal(132, -0, 0).unwrap();
            n0.set_sign(Sign::Pos);
            n.push(n0);
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.cbrt(RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}