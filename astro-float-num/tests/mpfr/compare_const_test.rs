//! This test suite performs comparison of mpfr constants and astro-float constants at bit level.

use crate::mpfr::common::get_prec_rng;
use crate::mpfr::common::test_astro_const;
use crate::mpfr::common::{assert_float_close, get_random_rnd_pair};
use astro_float_num::{BigFloat, Consts, EXPONENT_MAX, EXPONENT_MIN, WORD_BIT_SIZE};
use gmp_mpfr_sys::{
    gmp::exp_t,
    mpfr::{self, rnd_t},
};
use rand::random;
use rug::{
    float::{exp_max, exp_min},
    Float,
};

// constants computation
#[test]
fn mpfr_compare_const() {
    let repeat_cnt = 100;
    let run_cnt = 500;

    let p_rng = get_prec_rng();

    let p_min = 1;

    let p_max = (p_rng + p_min) * WORD_BIT_SIZE;

    unsafe {
        mpfr::set_emin(EXPONENT_MIN as exp_t);
        mpfr::set_emax(EXPONENT_MAX as exp_t);
    }

    assert_eq!(EXPONENT_MIN, exp_min());
    assert_eq!(EXPONENT_MAX, exp_max());

    let mut mpfr_e = Float::with_val((p_max + WORD_BIT_SIZE) as u32, 1);
    unsafe {
        mpfr::exp(
            mpfr_e.as_raw_mut(),
            Float::with_val(1, 1).as_raw(),
            rnd_t::RNDN,
        );
    }

    let mut mpfr_ln10 = Float::with_val((p_max + WORD_BIT_SIZE) as u32, 1);
    unsafe {
        mpfr::log(
            mpfr_ln10.as_raw_mut(),
            Float::with_val(32, 10).as_raw(),
            rnd_t::RNDN,
        );
    }

    for _ in 0..repeat_cnt {
        let mut cc = Consts::new().unwrap();

        for _ in 0..run_cnt {
            let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

            let (rm, rnd) = get_random_rnd_pair();

            // pi, ln(2)
            test_astro_const!(pi, const_pi, p, rm, rnd, (p, rm, "const pi"), cc);
            test_astro_const!(ln_2, const_log2, p, rm, rnd, (p, rm, "const ln(2)"), cc);

            // e
            let n1 = cc.e(p, rm);
            let mut f1 = mpfr_e.clone();
            unsafe {
                mpfr::prec_round(f1.as_raw_mut(), p as mpfr::prec_t, rnd);
            }

            assert_float_close(n1, f1, p, &format!("{:?}", (p, rm, "const e")), true);

            // ln(10)
            let n1 = cc.ln_10(p, rm);
            f1 = mpfr_ln10.clone();
            unsafe {
                mpfr::prec_round(f1.as_raw_mut(), p as mpfr::prec_t, rnd);
            }

            assert_float_close(n1, f1, p, &format!("{:?}", (p, rm, "const ln(10)")), true);
        }
    }
}
