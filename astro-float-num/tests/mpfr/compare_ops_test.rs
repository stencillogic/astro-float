//! This test suite performs comparison of mpfr and astro-float at bit level.
//! It uses normal numbers with randomly generated mantissa.

use std::ops::Add;

use crate::mpfr::common::get_prec_rng;
use crate::mpfr::common::test_astro_op;
use crate::mpfr::common::{assert_float_close, get_float_pair, get_random_rnd_pair};
use astro_float_num::{BigFloat, Consts, Exponent, EXPONENT_MAX, EXPONENT_MIN, WORD_BIT_SIZE};
use gmp_mpfr_sys::{gmp::exp_t, mpfr};
use rand::random;
use rug::{
    float::{exp_max, exp_min},
    Float,
};

#[test]
fn mpfr_compare_ops() {
    let run_cnt = 1000;
    let p_rng = get_prec_rng();
    let p_min = 1;

    run_compare_ops(run_cnt, p_rng, p_min);
}

#[test]
fn mpfr_compare_ops_large() {
    let run_cnt_large = 5;
    let p_rng_large = 1;
    let p_min_large;

    #[cfg(not(debug_assertions))]
    {
        p_min_large = 1563;
    }

    #[cfg(debug_assertions)]
    {
        p_min_large = 156;
    }

    run_compare_ops(run_cnt_large, p_rng_large, p_min_large);
}

fn run_compare_ops(run_cnt: usize, p_rng: usize, p_min: usize) {
    let mut cc = Consts::new().unwrap();

    unsafe {
        mpfr::set_emin(EXPONENT_MIN as exp_t);
        mpfr::set_emax(EXPONENT_MAX as exp_t);
    }

    assert_eq!(EXPONENT_MIN, exp_min());
    assert_eq!(EXPONENT_MAX, exp_max());

    /*     let s = "11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111";
    let n1 = BigFloat::parse(s, Radix::Bin, 192, RoundingMode::None);

    let s = "11100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
    let n2 = BigFloat::parse(s, Radix::Bin, 128, RoundingMode::None);

    println!("{:?}", n1.div(&n2, 960, RoundingMode::ToEven));
    return; */

    // rounding
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + 3) * WORD_BIT_SIZE;
        let p = p1 - random::<usize>() % WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();

        let (n1, mut f1) = get_float_pair(p1, 0, 0);

        let n2 = n1.round(p, rm);

        unsafe {
            mpfr::prec_round(f1.as_raw_mut(), p as mpfr::prec_t, rnd);
        }

        assert_float_close(n2, f1, p, &format!("{:?}", (n1, p, rm, "prec round")), true);
    }

    // add, sub
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();

        let (n1, f1) = get_float_pair(p1, EXPONENT_MIN, EXPONENT_MAX);
        let n1e = n1.exponent().unwrap();
        let (n2, f2) = get_float_pair(
            p2,
            n1e.saturating_sub(2 * (p2 + p1) as Exponent),
            n1e.saturating_add(2 * (p2 + p1) as Exponent),
        );

        // println!("\n{:?}", rm);
        // println!("{:b}\n{}", n1, f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", n2, f2.to_string_radix(2, None));

        test_astro_op!(
            true,
            n1,
            n2,
            add,
            f1,
            f2,
            add,
            p,
            rm,
            rnd,
            (&n1, &n2, p, rm, "add")
        );
        test_astro_op!(
            true,
            n1,
            n2,
            sub,
            f1,
            f2,
            sub,
            p,
            rm,
            rnd,
            (&n1, &n2, p, rm, "sub")
        );
    }

    // mul, div, reciprocal
    let mpfr_one = Float::with_val(64, 1);

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

        test_astro_op!(
            true,
            n1,
            n2,
            mul,
            f1,
            f2,
            mul,
            p,
            rm,
            rnd,
            (&n1, &n2, p, rm, "mul")
        );
        test_astro_op!(
            true,
            n1,
            n2,
            div,
            f1,
            f2,
            div,
            p,
            rm,
            rnd,
            (&n1, &n2, p, rm, "div")
        );

        let n3 = BigFloat::reciprocal(&n1, p, rm);

        let mut f3 = Float::with_val(p as u32, 1);
        unsafe { mpfr::div(f3.as_raw_mut(), mpfr_one.as_raw(), f1.as_raw(), rnd) };

        assert_float_close(
            n3,
            f3,
            p,
            &format!("{:?}", (&n1, &n2, p, rm, "reciprocal")),
            true,
        );
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

        n3 = n3.abs(); // n3 sign is set to the sign of n1.

        if f3.is_sign_negative() {
            // f3 can become negative because quotinent rounding.
            f3 = f3.add(f2);
        }

        // println!("\nn3 f3\n{:b}\n{}", n3, f3.to_string_radix(2, None));

        assert_float_close(n3, f3, p, &format!("{:?}", (n1, n2, "rem")), true);
    }

    // powi
    for _ in 0..run_cnt {
        let i = random::<usize>();
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        //println!("{:?}", rm);

        let (n1, f1) = get_float_pair(
            p1,
            EXPONENT_MIN / i as Exponent,
            EXPONENT_MAX / i as Exponent,
        );

        let n3 = BigFloat::powi(&n1, i, p, rm);

        let mut f3 = Float::with_val(p as u32, 1);

        unsafe { mpfr::pow_ui(f3.as_raw_mut(), f1.as_raw(), i as u64, rnd) };

        // println!("\n{}", i);
        // println!("{:b}\n{}", n1, f1.to_string_radix(2, None));

        assert_float_close(n3, f3, p, &format!("{:?}", (n1, i, p, rm, "powi")), true);
    }

    // pow
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        // println!("{:?}", rm);

        let (mut b, mut c) = get_float_pair(p2, EXPONENT_MIN, EXPONENT_MAX);

        b = b.abs();
        c = c.abs();

        let n = b.exponent().unwrap().unsigned_abs() as usize;
        let emax = EXPONENT_MAX / if n == 0 { 1 } else { n } as Exponent;
        let emin = -emax;

        let (n1, f1) = get_float_pair(p1, emin, emax);

        // println!("{:?}", b);
        // println!("{:?}", n1);

        test_astro_op!(
            true,
            b,
            n1,
            pow,
            c,
            f1,
            pow,
            p,
            rm,
            rnd,
            (b, n1, p, rm, "pow"),
            cc
        );
    }

    // n1 = -inf..2: sin, cos, tan
    assert_eq!(core::mem::size_of::<Exponent>(), 4);
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        //println!("{:?}", rm);

        let (n1, f1) = get_float_pair(p1, EXPONENT_MIN, 256);

        //println!("{:?}", n1);

        test_astro_op!(true, n1, sin, f1, sin, p, rm, rnd, (&n1, p, rm, "sin"), cc);
        test_astro_op!(true, n1, cos, f1, cos, p, rm, rnd, (&n1, p, rm, "cos"), cc);
        test_astro_op!(true, n1, tan, f1, tan, p, rm, rnd, (&n1, p, rm, "tan"), cc);
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

        test_astro_op!(true, n1, exp, f1, exp, p, rm, rnd, (&n1, p, rm, "exp"), cc);
        test_astro_op!(
            true,
            n1,
            sinh,
            f1,
            sinh,
            p,
            rm,
            rnd,
            (&n1, p, rm, "sinh"),
            cc
        );
        test_astro_op!(
            true,
            n1,
            cosh,
            f1,
            cosh,
            p,
            rm,
            rnd,
            (&n1, p, rm, "cosh"),
            cc
        );
        test_astro_op!(
            true,
            n1,
            tanh,
            f1,
            tanh,
            p,
            rm,
            rnd,
            (&n1, p, rm, "tanh"),
            cc
        );
    }

    // n1 = 1.0..+inf: acosh
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        //println!("{:?}", rm);

        let (n1, f1) = get_float_pair(p1, 1, EXPONENT_MAX);

        //println!("{:?}", n1);

        test_astro_op!(
            true,
            n1,
            acosh,
            f1,
            acosh,
            p,
            rm,
            rnd,
            (&n1, p, rm, "acosh"),
            cc
        );
    }

    // n1 = 0..1.0: acos, asin, atanh
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        // println!("{:?}", rm);

        let (n1, f1) = get_float_pair(p1, EXPONENT_MIN, 0);

        //println!("{:?}\n{:?}", n1, f1.to_string_radix(2, None));

        test_astro_op!(
            true,
            n1,
            acos,
            f1,
            acos,
            p,
            rm,
            rnd,
            (&n1, p, rm, "acos"),
            cc
        );
        test_astro_op!(
            true,
            n1,
            asin,
            f1,
            asin,
            p,
            rm,
            rnd,
            (&n1, p, rm, "asin"),
            cc
        );
        test_astro_op!(
            true,
            n1,
            atanh,
            f1,
            atanh,
            p,
            rm,
            rnd,
            (&n1, p, rm, "atanh"),
            cc
        );
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

        test_astro_op!(true, n1, sqrt, f1, sqrt, p, rm, rnd, (&n1, p, rm, "sqrt"));
        test_astro_op!(true, n1, cbrt, f1, cbrt, p, rm, rnd, (&n1, p, rm, "cbrt"));
        test_astro_op!(true, n1, ln, f1, log, p, rm, rnd, (&n1, p, rm, "ln"), cc);
        test_astro_op!(
            true,
            n1,
            log2,
            f1,
            log2,
            p,
            rm,
            rnd,
            (&n1, p, rm, "log2"),
            cc
        );
        test_astro_op!(
            true,
            n1,
            log10,
            f1,
            log10,
            p,
            rm,
            rnd,
            (&n1, p, rm, "log10"),
            cc
        );
        test_astro_op!(
            true,
            n1,
            asinh,
            f1,
            asinh,
            p,
            rm,
            rnd,
            (&n1, p, rm, "asinh"),
            cc
        );
        test_astro_op!(
            true,
            n1,
            atan,
            f1,
            atan,
            p,
            rm,
            rnd,
            (&n1, p, rm, "atan"),
            cc
        );
    }
}
