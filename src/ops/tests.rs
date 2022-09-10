//! tests

use crate::ops::consts::std::E;
use crate::{Exponent, Sign, Radix};
use crate::common::consts::ONE;
use crate::defs::{RoundingMode, EXPONENT_MIN, EXPONENT_MAX};
use crate::num::BigFloatNumber;


#[test]
fn test_ln_exp() {

    let prec = 320;
    let mut eps = ONE.clone().unwrap();

    let e_const = E.with(|v| -> BigFloatNumber {
        v.borrow_mut().for_prec(320, RoundingMode::None).unwrap()
    });

/*     let d1 = BigFloatNumber::from_raw_parts(&[2134170684, 3164033087, 409012923, 368468195, 719743879, 1804695412, 4180589568, 1528545767, 3297688378, 3632932384], 320, Sign::Pos, 4).unwrap();
    let d3 = d1.ln(RoundingMode::None).unwrap();

    println!("{:?}", d3.format(Radix::Dec, RoundingMode::None).unwrap());
    return; */


    for _ in 0..1000 {

        // avoid subnormal numbers
        let mut d1 = BigFloatNumber::random_normal(prec, -10, 10).unwrap();
        d1.set_sign(Sign::Pos);

        let d2 = d1.ln(RoundingMode::ToEven).unwrap();
        let d3 = d2.exp(RoundingMode::ToEven).unwrap();
//        println!("{}", d3.format(Radix::Dec, RoundingMode::None).unwrap());

        eps.set_exponent(d1.get_exponent() - prec as Exponent + 4);

        assert!(d1.sub(&d3, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);
    }
}