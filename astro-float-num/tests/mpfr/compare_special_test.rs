//! This test suite performs comparison of mpfr and astro-float at bit level.
//! It uses special cases of numbers, like zero, one, maximum possible value, a number with many trailing zeroes in mantissa, etc.

use std::ops::Add;

use crate::mpfr::common::{
    assert_float_close, conv_to_mpfr, get_last_zero, get_near_one, get_oned_sides, get_oned_zeroed,
    get_periodic, get_random_rnd_pair,
};
use crate::mpfr::common::{get_prec_rng, test_astro_op};
use astro_float_num::{BigFloat, Consts, Exponent, EXPONENT_MAX, EXPONENT_MIN, WORD_BIT_SIZE};
use gmp_mpfr_sys::{gmp::exp_t, mpfr};
use rand::random;
use rug::{
    float::{exp_max, exp_min},
    Float,
};

#[test]
fn mpfr_compare_special() {
    let run_cnt = 500;
    let p_rng = get_prec_rng();
    let p_min = 1;

    run_compare_special(run_cnt, p_rng, p_min);
}

#[test]
fn mpfr_compare_special_large() {
    let run_cnt_large = 3;
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

    run_compare_special(run_cnt_large, p_rng_large, p_min_large);
}

fn run_compare_special(run_cnt: usize, p_rng: usize, p_min: usize) {
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

    let mpfr_one = Float::with_val(64, 1);

    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();

        let nn = [
            BigFloat::new(p1),
            BigFloat::new(p1).neg(),
            BigFloat::from_i8(1, p1),
            BigFloat::from_i8(-1, p1),
            BigFloat::max_value(p1),
            BigFloat::min_value(p1),
            BigFloat::min_positive_normal(p1),
            BigFloat::min_positive_normal(p1).neg(),
            get_oned_zeroed(p1, EXPONENT_MIN, EXPONENT_MAX),
            get_oned_sides(p1, EXPONENT_MIN, EXPONENT_MAX),
            get_periodic(p1, EXPONENT_MIN, EXPONENT_MAX),
            get_last_zero(p1, EXPONENT_MIN, EXPONENT_MAX),
            get_near_one(p1),
        ];

        for n in nn.iter() {
            //println!("{:?}", n);

            let f = conv_to_mpfr(p1, n);

            let nn1 = [
                BigFloat::new(p2),
                BigFloat::new(p2).neg(),
                BigFloat::from_i8(1, p2),
                BigFloat::from_i8(-1, p2),
                BigFloat::max_value(p2),
                BigFloat::min_value(p2),
                BigFloat::min_positive_normal(p2),
                BigFloat::min_positive_normal(p2).neg(),
                get_oned_zeroed(p2, EXPONENT_MIN, EXPONENT_MAX),
                get_oned_sides(p2, EXPONENT_MIN, EXPONENT_MAX),
                get_periodic(p2, EXPONENT_MIN, EXPONENT_MAX),
                get_last_zero(p2, EXPONENT_MIN, EXPONENT_MAX),
                get_near_one(p2),
            ];

            for n1 in nn1.iter() {
                let f1 = conv_to_mpfr(p2, n1);

                //println!("rm {:?}", rm);
                //println!("\n--{:?}\n{:?}", n, n1);
                //println!("\n--{:?}\n{:?}", f, f1);
                test_astro_op!(
                    true,
                    n,
                    n1,
                    add,
                    f,
                    f1,
                    add,
                    p,
                    rm,
                    rnd,
                    (n, n1, p, rm, "add")
                );
                test_astro_op!(
                    true,
                    n,
                    n1,
                    sub,
                    f,
                    f1,
                    sub,
                    p,
                    rm,
                    rnd,
                    (n, n1, p, rm, "sub")
                );
                test_astro_op!(
                    true,
                    n,
                    n1,
                    mul,
                    f,
                    f1,
                    mul,
                    p,
                    rm,
                    rnd,
                    (n, n1, p, rm, "mul")
                );
                test_astro_op!(
                    true,
                    n,
                    n1,
                    div,
                    f,
                    f1,
                    div,
                    p,
                    rm,
                    rnd,
                    (n, n1, p, rm, "div")
                );

                test_astro_op!(
                    true,
                    n,
                    n1,
                    pow,
                    f,
                    f1,
                    pow,
                    p,
                    rm,
                    rnd,
                    (n, n1, p, rm, "pow"),
                    cc
                );

                // rem
                let p = p1.max(p2);
                let f = f.clone().abs();
                let f1 = f1.abs();

                let mut n3 = n.rem(n1);

                let mut f3 = Float::with_val(p as u32, 0);
                unsafe { mpfr::remainder(f3.as_raw_mut(), f.as_raw(), f1.as_raw(), rnd) };

                n3 = n3.abs(); // n3 sign is set to the sign of n1.

                if f3.is_sign_negative() && !f3.is_zero() {
                    // f3 can become negative because of quotinent rounding.
                    f3 = f3.add(f1);
                }

                //println!("\n{:?}\n{:?}", n3, f3);

                assert_float_close(n3, f3, p, &format!("{:?}", (n, n1, "rem")), true);
            }

            test_astro_op!(true, n, sqrt, f, sqrt, p, rm, rnd, (n, p, rm, "sqrt"));
            test_astro_op!(true, n, cbrt, f, cbrt, p, rm, rnd, (n, p, rm, "cbrt"));
            test_astro_op!(true, n, ln, f, log, p, rm, rnd, (n, p, rm, "ln"), cc);
            test_astro_op!(true, n, log2, f, log2, p, rm, rnd, (n, p, rm, "log2"), cc);
            test_astro_op!(
                true,
                n,
                log10,
                f,
                log10,
                p,
                rm,
                rnd,
                (n, p, rm, "log10"),
                cc
            );
            test_astro_op!(
                true,
                n,
                asinh,
                f,
                asinh,
                p,
                rm,
                rnd,
                (n, p, rm, "asinh"),
                cc
            );
            test_astro_op!(true, n, atan, f, atan, p, rm, rnd, (n, p, rm, "atan"), cc);

            let mut n_trig = n.clone();
            let f_trig = if n.exponent().unwrap() > 128 {
                n_trig.set_exponent(128); // large exponent causes very long computation.
                conv_to_mpfr(p1, &n_trig)
            } else {
                f.clone()
            };

            test_astro_op!(
                true,
                n_trig,
                sin,
                f_trig,
                sin,
                p,
                rm,
                rnd,
                (n, p, rm, "sin"),
                cc
            );
            test_astro_op!(
                true,
                n_trig,
                cos,
                f_trig,
                cos,
                p,
                rm,
                rnd,
                (n, p, rm, "cos"),
                cc
            );
            test_astro_op!(
                true,
                n_trig,
                tan,
                f_trig,
                tan,
                p,
                rm,
                rnd,
                (n, p, rm, "tan"),
                cc
            );

            test_astro_op!(true, n, exp, f, exp, p, rm, rnd, (n, p, rm, "exp"), cc);
            test_astro_op!(true, n, sinh, f, sinh, p, rm, rnd, (n, p, rm, "sinh"), cc);
            test_astro_op!(true, n, cosh, f, cosh, p, rm, rnd, (n, p, rm, "cosh"), cc);
            test_astro_op!(true, n, tanh, f, tanh, p, rm, rnd, (n, p, rm, "tanh"), cc);

            test_astro_op!(
                true,
                n,
                acosh,
                f,
                acosh,
                p,
                rm,
                rnd,
                (n, p, rm, "acosh"),
                cc
            );

            test_astro_op!(true, n, acos, f, acos, p, rm, rnd, (n, p, rm, "acos"), cc);
            test_astro_op!(true, n, asin, f, asin, p, rm, rnd, (n, p, rm, "asin"), cc);
            test_astro_op!(
                true,
                n,
                atanh,
                f,
                atanh,
                p,
                rm,
                rnd,
                (n, p, rm, "atanh"),
                cc
            );

            // powi
            for i in [0, 1, 2, 31, 32, usize::MAX] {
                let n3 = BigFloat::powi(n, i, p, rm);

                let mut f3 = Float::with_val(p as u32, 1);

                unsafe { mpfr::pow_ui(f3.as_raw_mut(), f.as_raw(), i as u64, rnd) };

                assert_float_close(n3, f3, p, &format!("{:?}", (n, i, p, rm, "powi")), true);
            }

            // reciprocal
            let n3 = BigFloat::reciprocal(n, p, rm);

            let mut f3 = Float::with_val(p as u32, 1);
            unsafe { mpfr::div(f3.as_raw_mut(), mpfr_one.as_raw(), f.as_raw(), rnd) };

            assert_float_close(n3, f3, p, &format!("{:?}", (n, p, rm, "reciprocal")), true);
        }
    }

    // grades of pi
    for _ in 0..run_cnt {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();
        let (rm2, _) = get_random_rnd_pair();

        let mut n = cc.pi(p1, rm2);
        let e = rand::random::<usize>() % (10 + EXPONENT_MAX as usize);
        n.set_exponent((EXPONENT_MIN as isize + e as isize) as Exponent);

        let f = conv_to_mpfr(p1, &n);

        test_astro_op!(true, n, sin, f, sin, p, rm, rnd, (&n, p, rm, "sin"), cc);

        test_astro_op!(true, n, cos, f, cos, p, rm, rnd, (&n, p, rm, "cos"), cc);

        test_astro_op!(true, n, tan, f, tan, p, rm, rnd, (n, p, rm, "tan"), cc);
    }
}
