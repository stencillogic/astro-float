//! tests

use crate::common::consts::ONE;
use crate::common::util::{count_leading_ones, count_leading_zeroes_skip_first, log2_ceil};
use crate::defs::{RoundingMode, EXPONENT_MAX, EXPONENT_MIN, WORD_BIT_SIZE};
use crate::num::BigFloatNumber;
use crate::ops::consts::Consts;
use crate::{Exponent, Sign};
use rand::random;

// test for debugging
/* #[test]
fn ttt() {
    let n = BigFloatNumber::from_raw_parts(&[13835058055282163712], 64, Sign::Pos, 3).unwrap();
    let m = BigFloatNumber::from_raw_parts(&[6585903223086643450, 16094311991002073707, 17000984990068853901], 192, Sign::Neg, -192).unwrap();

    let _z = n.add(&m, 192, RoundingMode::None).unwrap();

    let mut cc = Consts::new().unwrap();
    let s = "";
    let n = BigFloatNumber::parse(s, crate::Radix::Bin, 7040, RoundingMode::None).unwrap();

    println!("\n\n\n\n\n\n\n\n");

    let v = n.tan(7040, RoundingMode::None, &mut cc).unwrap();

    println!("{}", v.format(crate::Radix::Bin, RoundingMode::None).unwrap());
} */

#[test]
fn test_ln_exp() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();

    let mut cc = Consts::new().unwrap();

    /*     let e_const = E.with(|v| -> BigFloatNumber {
        v.borrow_mut().for_prec(320, RoundingMode::None).unwrap()
    });

    let d1 = BigFloatNumber::from_raw_parts(&[2134170684, 3164033087, 409012923, 368468195, 719743879, 1804695412, 4180589568, 1528545767, 3297688378, 3632932384], 320, Sign::Pos, 4).unwrap();
    let d3 = d1.ln(RoundingMode::None).unwrap();

    println!("{:?}", d3.format(Radix::Dec, RoundingMode::None).unwrap());
    return; */

    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let mut d1 = BigFloatNumber::random_normal(prec, EXPONENT_MIN, EXPONENT_MAX).unwrap();
        d1.set_sign(Sign::Pos);

        let d2 = d1.ln(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = d2.exp(prec, RoundingMode::ToEven, &mut cc).unwrap();

        eps.set_exponent(d2.get_exponent() - prec as Exponent);
        let err = eps.exp(prec, RoundingMode::Up, &mut cc).unwrap();

        //println!("{}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        //println!("{}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        //println!("{}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        // d2 - ulp(d2)/2 <= ln(d1) <= d2 + ulp(d2)/2  ->  d3 / e^(ulp(d2)/2) <= d1 <= d3 * e^(ulp(d2)/2)
        assert!(d1.cmp(&d3.mul(&err, prec, RoundingMode::Up).unwrap()) <= 0);
        assert!(d1.cmp(&d3.div(&err, prec, RoundingMode::Down).unwrap()) >= 0);
    }
}

#[test]
fn test_powi() {
    let prec_rng = 32;

    for _ in 0..1000 {
        let i = random::<usize>() % 1000 + 1;
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let mut d1 = BigFloatNumber::random_normal(
            prec,
            EXPONENT_MIN / i as Exponent,
            EXPONENT_MAX / i as Exponent,
        )
        .unwrap();
        d1.set_sign(Sign::Pos);

        let d2 = d1.powi(i as usize, prec, RoundingMode::ToEven).unwrap();

        let mut d3 = d1.clone().unwrap();
        d3.set_precision(prec + core::mem::size_of::<usize>(), RoundingMode::None)
            .unwrap();
        for _ in 1..i {
            d3 = d3
                .mul(&d1, d3.get_mantissa_max_bit_len(), RoundingMode::None)
                .unwrap();
        }
        d3.set_precision(prec, RoundingMode::ToEven).unwrap();

        // println!("d1 {}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d2 {}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d3 {}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("i {}", i);

        assert!(d3.cmp(&d2) == 0);
    }
}

#[test]
fn test_log2_log10_pow() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();

    let mut cc = Consts::new().unwrap();

    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let mut d1 = BigFloatNumber::random_normal(prec, EXPONENT_MIN, EXPONENT_MAX).unwrap();
        d1.set_sign(Sign::Pos);

        let d2 = d1.log2(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let two = BigFloatNumber::from_word(2, prec).unwrap();
        let d3 = two.pow(&d2, prec, RoundingMode::ToEven, &mut cc).unwrap();

        let d4 = d1.log10(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let ten = BigFloatNumber::from_word(10, prec).unwrap();
        let d5 = ten.pow(&d4, prec, RoundingMode::ToEven, &mut cc).unwrap();

        //println!("{}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        //println!("{}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        //println!("{}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        // d2 - ulp(d2)/2 <= log2(d1) <= d2 + ulp(d2)/2  ->  d3 / 2^(ulp(d2)/2) <= d1 <= d3 * 2^(ulp(d2)/2)
        eps.set_exponent(d2.get_exponent() - prec as Exponent);
        let err = two.pow(&eps, prec, RoundingMode::Up, &mut cc).unwrap();

        assert!(d1.cmp(&d3.mul(&err, prec, RoundingMode::Up).unwrap()) <= 0);
        assert!(d1.cmp(&d3.div(&err, prec, RoundingMode::Down).unwrap()) >= 0);

        eps.set_exponent(d4.get_exponent() - prec as Exponent);
        let err = ten.pow(&eps, prec, RoundingMode::Up, &mut cc).unwrap();

        assert!(d1.cmp(&d5.mul(&err, prec, RoundingMode::Up).unwrap()) <= 0);
        assert!(d1.cmp(&d5.div(&err, prec, RoundingMode::Down).unwrap()) >= 0);
    }
}

#[test]
fn test_log_pow() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();

    let mut cc = Consts::new().unwrap();

    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let mut d1 = BigFloatNumber::random_normal(prec, EXPONENT_MIN, EXPONENT_MAX).unwrap();
        let mut b = BigFloatNumber::random_normal(prec, EXPONENT_MIN, EXPONENT_MAX).unwrap();
        d1.set_sign(Sign::Pos);
        b.set_sign(Sign::Pos);

        let d2 = d1.log(&b, prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = b.pow(&d2, prec, RoundingMode::ToEven, &mut cc).unwrap();

        // println!("d1 {}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d2 {}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d3 {}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("b  {}", b.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        // d2 - ulp(d2)/2 <= log_b(d1) <= d2 + ulp(d2)/2  ->  d3 / b^(ulp(d2)/2) <= d1 <= d3 * b^(ulp(d2)/2)
        eps.set_exponent(d2.get_exponent() - prec as Exponent);
        let err = b.pow(&eps, prec, RoundingMode::Up, &mut cc).unwrap();

        if b.get_exponent() > 0 {
            assert!(d1.cmp(&d3.mul(&err, prec, RoundingMode::Up).unwrap()) <= 0);
            assert!(d1.cmp(&d3.div(&err, prec, RoundingMode::Down).unwrap()) >= 0);
        } else {
            assert!(d1.cmp(&d3.div(&err, prec, RoundingMode::Down).unwrap()) <= 0);
            assert!(d1.cmp(&d3.mul(&err, prec, RoundingMode::Up).unwrap()) >= 0);
        }
    }
}

#[test]
fn test_sin_asin() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();
    let mut thres = ONE.clone().unwrap();
    let thres_exp = -8;
    thres.set_exponent(thres_exp);

    let mut cc = Consts::new().unwrap();

    let pi = cc
        .pi((prec_rng + 1) * WORD_BIT_SIZE, RoundingMode::None)
        .unwrap();

    let mut half_pi = pi.clone().unwrap();
    half_pi.set_exponent(1);

    /*     let d1 = BigFloatNumber::from_raw_parts(&[2097186588, 2125458061, 154726044, 1972526461, 2656367726, 814809964, 990939464, 2788161723, 3328293782, 3887912150], 320, Sign::Neg, 0).unwrap();

    let d2 = d1.sin(RoundingMode::ToEven).unwrap();
    let d3 = d2.asin(RoundingMode::ToEven).unwrap();

    println!("{:?}", d1.format(Radix::Dec, RoundingMode::None).unwrap());
    println!("{:?}", d2.format(Radix::Dec, RoundingMode::None).unwrap());
    println!("{:?}", d3.format(Radix::Dec, RoundingMode::None).unwrap());

    eps.set_exponent(d1.get_exponent() - prec as Exponent + 4);

    assert!(d1.sub(&d3, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);

    return; */

    // argument between -pi/2, pi/2
    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let mut d1 = BigFloatNumber::random_normal(prec, -100, 2).unwrap();

        // -pi/2, pi/2
        while d1.abs().unwrap().cmp(&half_pi) > 0 {
            if d1.is_positive() {
                d1 = d1.sub(&half_pi, prec, RoundingMode::None).unwrap();
            }
            if d1.is_negative() {
                d1 = d1.add(&half_pi, prec, RoundingMode::None).unwrap();
            }
        }

        let d2 = d1.sin(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = d2.asin(prec, RoundingMode::ToEven, &mut cc).unwrap();

        // println!("{}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("{}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        eps.set_exponent(
            d1.get_exponent() - prec as Exponent
                + 1
                + count_leading_ones(d2.get_mantissa_digits()) as Exponent,
        );

        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );
    }

    // argument between -pi, -pi/2 and between pi/2, pi
    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let mut d1 = BigFloatNumber::random_normal(prec, -100, 2).unwrap();

        // -pi, -pi/2 and pi/2, pi
        while d1.abs().unwrap().cmp(&half_pi) < 0 {
            if d1.is_positive() {
                d1 = d1.add(&half_pi, prec, RoundingMode::None).unwrap();
            }
            if d1.is_negative() {
                d1 = d1.sub(&half_pi, prec, RoundingMode::None).unwrap();
            }
        }

        let arg = if d1.is_positive() {
            pi.sub(&d1, prec, RoundingMode::ToEven).unwrap()
        } else {
            pi.add(&d1, prec, RoundingMode::ToEven).unwrap()
        };

        let d2 = arg.sin(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = d2.asin(prec, RoundingMode::ToEven, &mut cc).unwrap();

        // avoid values of sin close to 1 because of limited precision
        if ONE
            .sub(&d2.abs().unwrap(), prec, RoundingMode::None)
            .unwrap()
            .cmp(&thres)
            >= 0
        {
            // println!("{}", arg.format(Radix::Dec, RoundingMode::None).unwrap());
            // println!("{}", d1.format(Radix::Dec, RoundingMode::None).unwrap());
            // println!("{}", d2.format(Radix::Dec, RoundingMode::None).unwrap());
            // println!("{}", d3.format(Radix::Dec, RoundingMode::None).unwrap());

            eps.set_exponent(d1.get_exponent() - prec as Exponent - thres_exp);

            assert!(
                d1.abs()
                    .unwrap()
                    .sub(&d3, prec, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&eps)
                    < 0
                    || arg
                        .abs()
                        .unwrap()
                        .sub(&d3, prec, RoundingMode::ToEven)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps)
                        < 0
            );
        }
    }
}

#[test]
fn test_cos_acos() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();

    let mut cc = Consts::new().unwrap();

    let pi = cc
        .pi((prec_rng + 1) * WORD_BIT_SIZE, RoundingMode::None)
        .unwrap();

    /*     let d1 = BigFloatNumber::from_raw_parts(&[1456218531, 703164634, 3869174995, 728180707, 794142643, 1990575249, 415454075, 2075230275, 2346793028, 681445537, 145621716, 775498281, 2975140815, 876411724, 3147375501, 2338110642, 3577417010, 3095720384, 2063787162, 1985481632, 168798015, 2477960193, 2032112066, 2819367426, 3040156967, 1564854250, 1142645696, 4153181427, 2939931561, 2569220972, 3593998760, 3295389666, 910688784, 3044919667, 4232521584, 3705749987, 3872951028, 388358967, 758972985, 1173372405, 3549434686, 2065917958, 3850118209, 2075337935, 1139277028, 1620627819, 3530770031, 4204162626, 85810630, 561952971, 2901114392, 1321621731, 716297011, 315030023, 1192364819, 3159540812, 1379143592, 1329431425, 760869437, 3340442410, 1450918057, 4178162271, 2810251834, 366126051, 3753313945, 2784305836, 1730114869, 1207852067, 1792591336, 835955104, 2556793533, 1413506794, 1657823935, 4013600827, 3570589700, 1434587096, 4142313494, 2489567354, 3247747544, 2853876571, 3600630716, 3927628676, 1555580733, 2125119320, 3039930421, 3397107605, 3390076514, 296410084, 3322344380, 3590148927, 1318604625, 3138655051, 2632176848, 665236644, 3818083749, 2850228879, 1790884543, 1461204514, 1969835970, 3242394962], 3200, Sign::Pos, 1).unwrap();

    let d2 = d1.cos(RoundingMode::ToEven).unwrap();
    //true: 0.060900805730186218547429347627109365106512082250229884161298909955723839190203670604770901445495392564064386860114407899103368305046662926704473252804543377135300041886329773239415089780288408402321875008867274060425168282881388886753177861207482365091769102464909255621346430643576471380493375817779847183773365188448353671994946997602550406065476934118571597094195500506676516181061967000267347909752297172120124987043926503874631545487174976436167915083750695836241278002819478636311149590294448412826073353938798257211071385306705897958939807575152141145117239225071528436158218701007211977052248300003515947464011541568882578121284323561327975328184266343863644345638871691487784100629001122634975335236325478090984237195608908593487682918804848210853776926295230561257227965522510799078020382363470831021657611178180553270686440560469461203682222539567476235303990490980876469561001840208196731432070098560191731859620621332576311258843835858286310754807773069
    //err:  0.06090080573018621854742934762710936510651208225022988416129890995572383919020367060477090144549539256406438686011440789910336830504666292670447325280454337713530004188632977323941508978028840840232187500886727406042516828288138888675317786120748236509176910246490925562134643064357647138049337581777984718377336518844835367199494699760255040606547693411857159709419550050667651618106196700026734790975229717212012498704392650387463154548717497643616791508375069583624127800281947863631114959029444841282607335393879825721107138530670589795893980757515214114511723922507152843615821870100721197705224830000351594746401154156888257812128432356132797532818426634386364434563887169148778410062900112263497533523632547809098423719560890859348768291880484821085377692629523056125722796552251079907802038236347083102165761117818055327068644056046946120368222253956747623530399049098087646956100184020819673143207009856019173185962062133257631125884383585828631075480417577
    let d3 = d2.acos(RoundingMode::ToEven).unwrap();

    println!("{:?}", d1.format(Radix::Dec, RoundingMode::None).unwrap());
    println!("{:?}", d2.format(Radix::Dec, RoundingMode::None).unwrap());
    println!("{:?}", d3.format(Radix::Dec, RoundingMode::None).unwrap());

    eps.set_exponent(d1.get_exponent() - prec as Exponent + 4);

    assert!(d1.sub(&d3, RoundingMode::ToEven).unwrap().abs().unwrap().cmp(&eps) < 0);

    return; */

    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let mut d1 = BigFloatNumber::random_normal(prec, -(prec as Exponent) / 2, 3).unwrap();

        // -pi, pi
        while d1.abs().unwrap().cmp(&pi) > 0 {
            if d1.is_positive() {
                d1 = d1.sub(&pi, prec, RoundingMode::None).unwrap();
            }
            if d1.is_negative() {
                d1 = d1.add(&pi, prec, RoundingMode::None).unwrap();
            }
        }

        let d2 = d1.cos(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = d2.acos(prec, RoundingMode::ToEven, &mut cc).unwrap();

        // println!("d1 {}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d1 {:?}", d1);
        // println!("d2 {}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d3 {}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        if d2.cmp(&ONE) != 0 {
            eps.set_exponent(
                d1.get_exponent() - prec as Exponent
                    + 1
                    + count_leading_ones(d2.get_mantissa_digits()) as Exponent,
            );

            assert!(
                d1.abs()
                    .unwrap()
                    .sub(&d3, prec, RoundingMode::ToEven)
                    .unwrap()
                    .abs()
                    .unwrap()
                    .cmp(&eps)
                    < 0
            );
        }
    }
}

#[test]
fn test_tan_atan() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();

    let mut cc = Consts::new().unwrap();

    let pi = cc
        .pi((prec_rng + 1) * WORD_BIT_SIZE, RoundingMode::None)
        .unwrap();

    let mut half_pi = pi.clone().unwrap();
    half_pi.set_exponent(1);

    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let mut d1 = BigFloatNumber::random_normal(prec, -100, 2).unwrap();

        // -pi/2, pi/2
        while d1.abs().unwrap().cmp(&half_pi) > 0 {
            if d1.is_positive() {
                d1 = d1.sub(&half_pi, prec, RoundingMode::None).unwrap();
            }
            if d1.is_negative() {
                d1 = d1.add(&half_pi, prec, RoundingMode::None).unwrap();
            }
        }

        let d2 = d1.tan(prec, RoundingMode::ToEven, &mut cc).unwrap();
        let d3 = d2.atan(prec, RoundingMode::ToEven, &mut cc).unwrap();

        // println!("d1 {}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d2 {}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d3 {}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        eps.set_exponent(d1.get_exponent() - prec as Exponent + 2);

        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );
    }
}

#[test]
fn test_sinh_asinh() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();

    let mut cc = Consts::new().unwrap();

    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let d1 = BigFloatNumber::random_normal(prec, -100, 2).unwrap();

        let d2 = d1.sinh(prec, RoundingMode::ToEven).unwrap();
        let d3 = d2.asinh(prec, RoundingMode::ToEven, &mut cc).unwrap();

        // println!("d1 {}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d2 {}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d3 {}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        eps.set_exponent(
            d1.get_exponent() - prec as Exponent
                + 2
                + log2_ceil(d1.get_exponent().unsigned_abs() as usize) as Exponent,
        );

        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );
    }
}

#[test]
fn test_cosh_acosh() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();

    let mut cc = Consts::new().unwrap();

    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let d1 = BigFloatNumber::random_normal(prec, -100, 10).unwrap();

        let d2 = d1.cosh(prec, RoundingMode::ToEven).unwrap();
        let d3 = d2.acosh(prec, RoundingMode::ToEven, &mut cc).unwrap();

        eps.set_exponent(
            d1.get_exponent() - prec as Exponent
                + 2
                + count_leading_zeroes_skip_first(d2.get_mantissa_digits()) as Exponent,
        );

        // println!("d1 {}", d1.abs().unwrap().format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d2 {}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d3 {}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("e {}", eps.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        assert!(
            d1.abs()
                .unwrap()
                .sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );
    }
}

#[test]
fn test_tanh_atanh() {
    let prec_rng = 32;
    let mut eps = ONE.clone().unwrap();

    let mut cc = Consts::new().unwrap();

    for _ in 0..1000 {
        let prec = (rand::random::<usize>() % prec_rng + 1) * WORD_BIT_SIZE;
        let d1 = BigFloatNumber::random_normal(prec, -100, 1).unwrap();

        let d2 = d1.tanh(prec, RoundingMode::ToEven, &mut cc).unwrap();

        let d3 = d2.atanh(prec, RoundingMode::ToEven, &mut cc).unwrap();

        eps.set_exponent(d1.get_exponent() - prec as Exponent + 2);

        // println!("d1 {}", d1.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d2 {}", d2.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("d3 {}", d3.format(crate::Radix::Bin, RoundingMode::None).unwrap());
        // println!("e {}", eps.format(crate::Radix::Bin, RoundingMode::None).unwrap());

        assert!(
            d1.sub(&d3, prec, RoundingMode::ToEven)
                .unwrap()
                .abs()
                .unwrap()
                .cmp(&eps)
                < 0
        );
    }
}
