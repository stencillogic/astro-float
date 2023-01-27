//! Cube root computation.

use crate::{
    common::util::{log2_ceil, round_p},
    defs::{Error, EXPONENT_MAX, EXPONENT_MIN},
    num::BigFloatNumber,
    Exponent, RoundingMode, Sign,
};

impl BigFloatNumber {
    /// Computes the cube root of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory.
    ///  - InvalidArgument: the precision is incorrect.
    pub fn cbrt(&self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        let p = round_p(p);

        if self.is_zero() {
            return Self::new(p);
        }

        let mut x = self.clone()?;

        let e = x.normalize2() as isize;
        let e = self.get_exponent() as isize - e;
        let e_shift = e % 3 - 3;

        let p_ext = p + 1;
        x.set_precision(p_ext, RoundingMode::None)?;
        x.set_exponent(e_shift as Exponent);

        let mut ret = x.clone()?;

        let mut iters = log2_ceil(p) * 2 / 3 + 4;
        while iters > 0 {
            ret = x.cbrt_step(ret)?;
            iters -= 1;
        }

        ret.set_precision(p, rm)?;

        let mut e_corr = ret.get_exponent() as isize + (e - e_shift) / 3;

        if e_corr < EXPONENT_MIN as isize {
            let is_positive = ret.is_positive();
            if !Self::process_subnormal(&mut ret.m, &mut e_corr, rm, is_positive) {
                let mut ret = if rm == RoundingMode::FromZero 
                    || (is_positive && rm == RoundingMode::Up)
                    || (!is_positive && rm == RoundingMode::Down) {
                        // non zero directed rounding modes
                        Self::min_positive(p)
                } else {
                    Self::new(p)
                }?;
                ret.set_sign(if is_positive { Sign::Pos } else { Sign::Neg });
                return Ok(ret);
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

        let p = self.get_mantissa_max_bit_len();

        let xxn = xn.mul(&xn, p, RoundingMode::None)?;
        let mut xxxn = xxn.mul(&xn, p, RoundingMode::None)?;

        let e = xxxn.get_exponent();

        xxxn.set_exponent(e - 1);
        let d1 = xxxn.add(self, p, RoundingMode::None)?;

        xn.set_exponent(xn.get_exponent() + 1);
        let d2 = xn.mul(&d1, p, RoundingMode::None)?;

        xxxn.set_exponent(e + 1);
        let d3 = xxxn.add(self, p, RoundingMode::None)?;

        d2.div(&d3, p, RoundingMode::None)
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{
        common::{consts::ONE, util::random_subnormal},
        defs::{EXPONENT_MAX, EXPONENT_MIN, WORD_BIT_SIZE},
        Exponent,
    };

    #[cfg(feature = "std")]
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

        for _ in 0..1000 {
            let prec = (rand::random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
            let d1 = BigFloatNumber::random_normal(prec, EXPONENT_MIN, EXPONENT_MAX).unwrap();
            let d2 = d1.cbrt(prec, RoundingMode::ToEven).unwrap();
            let d3 = d2
                .mul(&d2, prec, RoundingMode::ToEven)
                .unwrap()
                .mul(&d2, prec, RoundingMode::ToEven)
                .unwrap();

            eps.set_exponent(d1.get_exponent() - prec as Exponent + 3);

            // println!("d1 {:?}", d1.format(crate::Radix::Dec, RoundingMode::None).unwrap());
            // println!("d2 {:?}", d2.format(crate::Radix::Dec, RoundingMode::None).unwrap());
            // println!("d3 {:?}", d3.format(crate::Radix::Dec, RoundingMode::None).unwrap());

            assert!(
                d1.sub(&d3, prec, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&eps)
                    < 0
            );
        }

        // MAX
        let prec = 320;
        let d1 = BigFloatNumber::max_value(prec).unwrap();
        let d2 = d1.cbrt(prec, RoundingMode::ToEven).unwrap();
        let d3 = d2
            .mul(&d2, prec, RoundingMode::ToEven)
            .unwrap()
            .mul(&d2, prec, RoundingMode::ToEven)
            .unwrap();
        eps.set_exponent(d1.get_exponent() - prec as Exponent + 3);
        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );

        // MIN
        let d1 = BigFloatNumber::min_value(prec).unwrap();
        let d2 = d1.cbrt(prec, RoundingMode::ToEven).unwrap();
        let d3 = d2
            .mul(&d2, prec, RoundingMode::ToEven)
            .unwrap()
            .mul(&d2, prec, RoundingMode::ToEven)
            .unwrap();
        eps.set_exponent(d1.get_exponent() - prec as Exponent + 3);
        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );

        // MIN POSITIVE
        let d1 = BigFloatNumber::min_positive(prec).unwrap();
        let d2 = d1.cbrt(prec, RoundingMode::ToEven).unwrap();
        let d3 = d2
            .mul(&d2, prec, RoundingMode::ToEven)
            .unwrap()
            .mul(&d2, prec, RoundingMode::ToEven)
            .unwrap();
        let eps = BigFloatNumber::min_positive(prec).unwrap();
        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                <= 0
        );

        // near 1
        let p = 320;
        let d1 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC4872DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.cbrt(p, RoundingMode::ToEven).unwrap();
        let d3 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFB9ED752A27F96D7B9ED752A27F96D8_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();

        //println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        let d1 = BigFloatNumber::parse(
            "1.00000000000000000000000000000000000000000000000000000000000000002DC85F7E77EC487C",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.cbrt(p, RoundingMode::ToEven).unwrap();
        let d3 = BigFloatNumber::parse(
            "1.00000000000000000000000000000000000000000000000000000000000000000F42CA7F7D4EC2D4",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();

        // println!("{:?}", d2.format(crate::Radix::Hex, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        // random subnormal arg
        for _ in 0..1000 {
            let d1 = random_subnormal(prec);

            let d2 = d1.cbrt(prec, RoundingMode::ToEven).unwrap();
            let d3 = d2
                .mul(&d2, prec, RoundingMode::ToEven)
                .unwrap()
                .mul(&d2, prec, RoundingMode::ToEven)
                .unwrap();

            let eps = BigFloatNumber::min_positive(prec).unwrap();
            // eps.set_exponent(eps.get_exponent() + 3);

            // println!("{:?}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
            // println!("{:?}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());
            // println!("{:?}", eps.format(crate::Radix::Bin, RoundingMode::None).unwrap());

            assert!(
                d1.sub(&d3, prec, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&eps)
                    <= 0
            );
        }
    }

    #[ignore]
    #[test]
    #[cfg(feature = "std")]
    fn cbrt_perf() {
        let mut n = vec![];
        let p = 132;
        for _ in 0..100000 {
            let mut n0 = BigFloatNumber::random_normal(p, -0, 0).unwrap();
            n0.set_sign(Sign::Pos);
            n.push(n0);
        }

        for _ in 0..5 {
            let start_time = std::time::Instant::now();
            for ni in n.iter() {
                let _f = ni.cbrt(p, RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
