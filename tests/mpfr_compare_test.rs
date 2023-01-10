//! This test suite performs comparison of mpfr and astro-float at bit level.

use std::ops::Add;

use astro_float::{WORD_BIT_SIZE, BigFloat, EXPONENT_MIN, EXPONENT_MAX, Exponent, RoundingMode, Radix, Consts};
use rand::random;
use rug::{Float, float::{exp_min, exp_max}};
use gmp_mpfr_sys::{mpfr::{self, rnd_t}, gmp::exp_t};


macro_rules! test_astro_op {
    ($n1:ident, $n2:ident, $astro_op:ident, $f1:ident, $f2:ident, $mpfr_op:ident, $p:ident, $rm:ident, $rnd:ident, $op_name:literal) => {
        let n3 = BigFloat::$astro_op(&($n1), &($n2), $p, $rm);

        let mut f3 = Float::with_val($p as u32, 1);

        unsafe { mpfr::$mpfr_op(f3.as_raw_mut(), ($f1).as_raw(), ($f2).as_raw(), $rnd) };

        // println!("\n{:b}\n{}", $n1, $f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", $n2, $f2.to_string_radix(2, None));

        assert_float_eq(n3, f3, $p, $op_name);
    };
    ($n1:ident, $astro_op:ident, $f1:ident, $mpfr_op:ident, $p:ident, $rm:ident, $rnd:ident, $op_name:literal) => {
        let n3 = BigFloat::$astro_op(&($n1), $p, $rm);

        let mut f3 = Float::with_val($p as u32, 1);

        unsafe { mpfr::$mpfr_op(f3.as_raw_mut(), ($f1).as_raw(), $rnd) };

        // println!("\n{:b}\n{}", $n1, $f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", n3, f3.to_string_radix(2, None));

        assert_float_eq(n3, f3, $p, $op_name);
    };
    ($n1:ident, $astro_op:ident, $f1:ident, $mpfr_op:ident, $p:ident, $rm:ident, $rnd:ident, $op_name:literal, $cc:ident) => {
        let n3 = BigFloat::$astro_op(&($n1), $p, $rm, &mut $cc);

        let mut f3 = Float::with_val($p as u32, 1);

        unsafe { mpfr::$mpfr_op(f3.as_raw_mut(), ($f1).as_raw(), $rnd) };

        // println!("\n{:b}\n{}", $n1, $f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", n3, f3.to_string_radix(2, None));

        assert_float_eq(n3, f3, $p, $op_name);
    };
}

#[test]
fn mpfr_compare() {
    let run_cnt = 1000;

    let p_rng = 32; //157;    // >~ 10000 bit
    let p_min = 1;

    let mut cc = Consts::new().unwrap();

    unsafe {
        mpfr::set_emin(EXPONENT_MIN as exp_t);
        mpfr::set_emax(EXPONENT_MAX as exp_t);
    }

    assert_eq!(EXPONENT_MIN, exp_min());
    assert_eq!(EXPONENT_MAX, exp_max());
/* 
    let s = "1.01101100111001100101010010100100101110001100011001100001000101000000100110011001001011000100100011011001101011100111110101011010010011001000101010010111010100010100010000110001010001010010100e-10010110";
    let n1 = BigFloat::parse(s, Radix::Bin, 192, RoundingMode::None);
    

    let s = "1.1100010010100111111001000110011011100110101100101001100000101001110111111111110100100101010110011101100100000101011011111011001e+1000001";
    let n2 = BigFloat::parse(s, Radix::Bin, 128, RoundingMode::None);

    println!("{:?}", n1.sub(&n2, 128, RoundingMode::None));
    println!("{:?}", n1.sub(&n2, 128, RoundingMode::None));
    return; */

    // rounding
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + 3) * WORD_BIT_SIZE;
        let p = p1 - random::<usize>() % WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();

        let (n1, mut f1) = get_float_pair(p1, 0, 0);

        let n1 = n1.round(p, rm);

        unsafe { mpfr::prec_round(f1.as_raw_mut(), p as mpfr::prec_t, rnd); }

        assert_float_eq(n1, f1, p, "prec round");
    }

    // add, sub
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();

        let (n1, f1) = get_float_pair(p1, EXPONENT_MIN, EXPONENT_MAX);
        let n1e = n1.get_exponent().unwrap();
        let (n2, f2) = get_float_pair(p2, n1e.saturating_sub(2 * (p2 + p1) as Exponent), n1e.saturating_add(2 * (p2 + p1) as Exponent));

        // println!("\n{:?}", rm);
        // println!("{:b}\n{}", n1, f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", n2, f2.to_string_radix(2, None));

        test_astro_op!(n1, n2, add, f1, f2, add, p, rm, rnd, "add");
        test_astro_op!(n1, n2, sub, f1, f2, sub, p, rm, rnd, "sub");
    }

    // mul, div
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();

        let (n1, f1) = get_float_pair(p1, EXPONENT_MIN, EXPONENT_MAX);
        let (n2, f2) = get_float_pair(p2, EXPONENT_MIN, EXPONENT_MAX);

        // println!("\n{:?}", rm);
        // println!("{:b}\n{}", n1, f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", n2, f2.to_string_radix(2, None));

        test_astro_op!(n1, n2, mul, f1, f2, mul, p, rm, rnd, "mul");
        test_astro_op!(n1, n2, div, f1, f2, div, p, rm, rnd, "div");
    }

    // rem
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = p1.max(p2);

        let (_rm, rnd) = get_random_rnd_pair();

        let (n1, mut f1) = get_float_pair(p1, EXPONENT_MIN / 2 - p1 as Exponent, EXPONENT_MAX / 2);
        let (n2, mut f2) = get_float_pair(p2, EXPONENT_MIN / 2 - p2 as Exponent, EXPONENT_MAX / 2);
        f1 = f1.abs();
        f2 = f2.abs();

        // println!("\nn1 f1\n{:b}\n{}", n1, f1.to_string_radix(2, None));
        // println!("\nn2 f2\n{:b}\n{}", n2, f2.to_string_radix(2, None));

        let mut n3 = n1.rem(&n2);

        let mut f3 = Float::with_val(p as u32, 1);
        unsafe { mpfr::remainder(f3.as_raw_mut(), f1.as_raw(), f2.as_raw(), rnd) };

        n3 = n3.abs();  // n3 sign is set to the sign of n1.

        if f3.is_sign_negative() {  // f3 can become negative because quotinent rounding.
            f3 = f3.add(f2);
        }

        // println!("\nn3 f3\n{:b}\n{}", n3, f3.to_string_radix(2, None));

        assert_float_eq(n3, f3, p, "rem");
    }

    // n1 = -inf..log2(emax): sinh, cosh, tanh, exp
    assert_eq!(core::mem::size_of::<Exponent>(), 4);
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        //println!("{:?}", rm);

        let (n1, f1) = get_float_pair(p1, EXPONENT_MIN, 32);

        //println!("{:?}", n1);

        test_astro_op!(n1, exp, f1, exp, p, rm, rnd, "exp", cc);
        test_astro_op!(n1, sinh, f1, sinh, p, rm, rnd, "sinh", cc);
        test_astro_op!(n1, cosh, f1, cosh, p, rm, rnd, "cosh", cc);
        test_astro_op!(n1, tanh, f1, tanh, p, rm, rnd, "tanh", cc);
    }

    // n1 = 1.0..+inf: acosh
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        //println!("{:?}", rm);

        let (n1, f1) = get_float_pair(p1, 1, EXPONENT_MAX);

        //println!("{:?}", n1);

        test_astro_op!(n1, acosh, f1, acosh, p, rm, rnd, "acosh", cc);
    }

    // n1 = 0..1.0: acos, asin, atanh
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        // println!("{:?}", rm);

        let (n1, f1) = get_float_pair(p1, EXPONENT_MIN, 0);

        //println!("{:?}\n{:?}", n1, f1.to_string_radix(2, None));

        test_astro_op!(n1, acos, f1, acos, p, rm, rnd, "acos", cc);
        test_astro_op!(n1, asin, f1, asin, p, rm, rnd, "asin", cc);
        test_astro_op!(n1, atanh, f1, atanh, p, rm, rnd, "atanh", cc);
    }

    // n1 = -inf..+inf: sqrt, cbrt, ln, log2, log10, asinh, atan
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        //println!("{:?}", rm);

        let (n1, f1) = get_float_pair(p1, EXPONENT_MIN, EXPONENT_MAX);

        // println!("{:b}", n1);
        // println!("{}", f1.to_string_radix(2, None));

        test_astro_op!(n1, sqrt, f1, sqrt, p, rm, rnd, "sqrt");
        test_astro_op!(n1, cbrt, f1, cbrt, p, rm, rnd, "cbrt");
        test_astro_op!(n1, ln, f1, log, p, rm, rnd, "ln", cc);
        test_astro_op!(n1, log2, f1, log2, p, rm, rnd, "log2", cc);
        test_astro_op!(n1, log10, f1, log10, p, rm, rnd, "log10", cc);
        test_astro_op!(n1, asinh, f1, asinh, p, rm, rnd, "asinh", cc);
        test_astro_op!(n1, atan, f1, atan, p, rm, rnd, "atan", cc);
    }
}

fn get_float_pair(p: usize, emin: Exponent, emax: Exponent) -> (BigFloat, Float) {
    let n = BigFloat::random_normal(p, emin, emax);
    let s1 = conv_str_to_mpfr_compat(format!("{:b}", n));
    let f = Float::with_val(p as u32, Float::parse_radix(&s1, 2).unwrap());
    let s2 = conv_str_from_mpfr_compat(f.to_string_radix(2, None));
    //println!("\n{}\n{}", s1, s2);
    assert_eq!(n, BigFloat::parse(&s2, Radix::Bin, p, RoundingMode::None));
    (n, f)
}

fn assert_float_eq(n: BigFloat, f: Float, p: usize, op: &str) {
    if n.is_inf() {
        // inf
        let ovf = unsafe { mpfr::overflow_p() };
        assert!(ovf != 0);
        if n.is_positive() {
            assert!(f.is_sign_positive());
        } else {
            assert!(f.is_sign_negative());
        }
    } else if n.is_nan() {
        // nan
        assert!(f.is_nan());
    } else if n.is_subnormal() || n.is_zero() {
        // subnormal
        let unf = unsafe { mpfr::underflow_p() };
        assert!(unf != 0);
    } else {
        // n == f
        let s1 = f.to_string_radix(2, None);
        let s2 = conv_str_from_mpfr_compat(s1);
        let n2 = BigFloat::parse(&s2, Radix::Bin, p, RoundingMode::None);
        assert_eq!(n, n2, "{}", op);
    }
}

fn conv_str_to_mpfr_compat(s: String) -> String {
    let (sig, exp) = s.split_at(s.find('e').unwrap() + 1);
    let expn = i64::from_str_radix(exp, 2).unwrap();
    sig.to_owned() + &expn.to_string()
}

fn conv_str_from_mpfr_compat(s: String) -> String {
    if let Some(epos) = s.find('e') {
        let (sig, exp) = s.split_at(epos + 1);
        let expn = exp.parse::<i64>().unwrap();
        if expn < 0 {
            sig.to_owned() + "-" + &format!("{:b}", -expn)
        } else {
            sig.to_owned() + &format!("{:b}", expn)
        }
    } else {
        s
    }
}

fn get_random_rnd_pair() -> (RoundingMode, rnd_t) {
    match random::<u8>() % 5 {
        0 => (RoundingMode::ToEven, rnd_t::RNDN),
        1 => (RoundingMode::Up, rnd_t::RNDU),
        2 => (RoundingMode::Down, rnd_t::RNDD),
        3 => (RoundingMode::FromZero, rnd_t::RNDA),
        4 => (RoundingMode::ToZero, rnd_t::RNDZ),
        _ => unreachable!(),
    }
}
