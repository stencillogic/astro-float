//! Cube root computation.

use crate::{
    num::BigFloatNumber, 
    RoundingMode, 
    defs::Error, Exponent, common::util::log2_ceil
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

        let e = self.get_exponent();
        let e_shift = e % 3 - 3;

        let mut x = self.clone()?;
        x.set_precision(x.get_mantissa_max_bit_len() + 1, RoundingMode::None)?;
        x.set_exponent(e_shift);

        let mut iters = log2_ceil(x.get_mantissa_max_bit_len()) * 2 / 3 + 3;
        let mut ret = x.clone()?;

        while iters > 0 {
            ret = x.cbrt_step(ret)?;
            iters -= 1;
        }

        ret.set_precision(self.get_mantissa_max_bit_len(), rm)?;
        ret.set_exponent(ret.get_exponent() + ((e as isize - e_shift as isize) / 3) as Exponent);

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