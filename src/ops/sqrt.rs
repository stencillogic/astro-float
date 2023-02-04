//! Sqrt computation.

use crate::common::util::round_p;
use crate::Sign;
use crate::{
    defs::{Error, EXPONENT_MIN},
    num::BigFloatNumber,
    Exponent, RoundingMode,
};

impl BigFloatNumber {
    /// Computes the square root of a number with precision `p`. The result is rounded using the rounding mode `rm`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Errors
    ///
    ///  - InvalidArgument: argument is negative, or the precision is incorrect.
    ///  - MemoryAllocation: failed to allocate memory.
    pub fn sqrt(&self, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        let p = round_p(p);
        Self::p_assertion(p)?;

        if self.is_zero() {
            return Self::new(p);
        }

        if self.is_negative() {
            return Err(Error::InvalidArgument);
        }

        let (e1, m1_opt) = self.normalize()?;
        let m1_normalized = m1_opt.as_ref().unwrap_or(&self.m);

        let (e_shift, m3) = m1_normalized.sqrt(p, rm, true, &mut true, e1 & 1 == 1)?;

        let e = (e1 + (e1 & 1)) / 2 + e_shift;

        if e < EXPONENT_MIN as isize {
            let mut ret = BigFloatNumber {
                m: m3,
                s: Sign::Pos,
                e: EXPONENT_MIN,
            };

            ret.subnormalize(e, rm, &mut true);

            Ok(ret)
        } else {
            Ok(BigFloatNumber {
                m: m3,
                s: Sign::Pos,
                e: e as Exponent,
            })
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::common::consts::ONE;
    use crate::{common::util::random_subnormal, defs::WORD_BIT_SIZE, Exponent};
    use crate::{Sign, EXPONENT_MAX};

    #[test]
    fn test_sqrt() {
        /* let n1 = BigFloatNumber::from_words(
            &[18446744073709551614, 18446744073709551615],
            Sign::Pos, 0).unwrap();
        let n2 = n1.sqrt(384, RoundingMode::ToEven).unwrap();
        println!("{:?}", n2.format(crate::Radix::Bin, RoundingMode::None).unwrap()); */

        // near 1
        let p = 320;
        let d1 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF2DC85F7E77EC4872DC85F7E77EC487_e-1",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();
        let d2 = d1.sqrt(p, RoundingMode::ToEven).unwrap();
        let d3 = BigFloatNumber::parse(
            "F.FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF96E42FBF3BF624396E42FBF3BF6243_e-1",
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
        let d2 = d1.sqrt(p, RoundingMode::ToEven).unwrap();
        let d3 = BigFloatNumber::parse(
            "1.000000000000000000000000000000000000000000000000000000000000000016E42FBF3BF6243E",
            crate::Radix::Hex,
            p,
            RoundingMode::None,
        )
        .unwrap();

        //println!("{:?}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        assert!(d2.cmp(&d3) == 0);

        // MAX
        let prec = 3200;
        let mut eps = ONE.clone().unwrap();

        let d1 = BigFloatNumber::max_value(prec).unwrap();
        let d2 = d1.sqrt(prec, RoundingMode::ToEven).unwrap();
        let d3 = d2.mul(&d2, prec, RoundingMode::ToEven).unwrap();
        eps.set_exponent(d1.exponent() - prec as Exponent + 2);
        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );

        // MIN
        let d1 = BigFloatNumber::min_positive(prec).unwrap();
        let d2 = d1.sqrt(prec, RoundingMode::ToEven).unwrap();
        let d3 = d2.mul(&d2, prec, RoundingMode::ToEven).unwrap();
        let eps = BigFloatNumber::min_positive(prec).unwrap();
        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                <= 0
        );

        // random
        let mut eps = ONE.clone().unwrap();

        for _ in 0..1000 {
            let prec = (rand::random::<usize>() % 32 + 1) * WORD_BIT_SIZE;

            let mut d1 = BigFloatNumber::random_normal(prec, EXPONENT_MIN, EXPONENT_MAX).unwrap();
            if d1.is_negative() {
                d1.inv_sign();
            }

            let d2 = d1.sqrt(prec, RoundingMode::ToEven).unwrap();
            let d3 = d2.mul(&d2, prec, RoundingMode::ToEven).unwrap();

            eps.set_exponent(d1.exponent() - prec as Exponent + 2);

            //println!("d1 {:?}\nd3 {:?}", d1, d3);

            assert!(
                d1.sub(&d3, prec, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&eps)
                    < 0
            );
        }

        // random subnormal arg
        for _ in 0..1000 {
            let mut d1 = random_subnormal(prec);
            d1.set_sign(Sign::Pos);

            let d2 = d1.sqrt(prec, RoundingMode::ToEven).unwrap();
            let d3 = d2.mul(&d2, prec, RoundingMode::ToEven).unwrap();

            let eps = BigFloatNumber::min_positive(prec).unwrap();
            // eps.set_exponent(eps.get_exponent() + 2);

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
    fn sqrt_perf() {
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
                let _f = ni.sqrt(p, RoundingMode::ToEven).unwrap();
            }
            let time = start_time.elapsed();
            println!("{}", time.as_millis());
        }
    }
}
