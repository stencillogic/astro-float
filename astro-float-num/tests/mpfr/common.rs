//! Components used in MPFR integration tests

use astro_float_num::{
    BigFloat, Exponent, Radix, RoundingMode, Sign, Word, WORD_BIT_SIZE, WORD_SIGNIFICANT_BIT,
};
use gmp_mpfr_sys::mpfr::{self, rnd_t};
use rand::random;
use rug::Float;

macro_rules! test_astro_op {
    ($eq:literal, $n1:ident, $n2:ident, $astro_op:ident, $f1:ident, $f2:ident, $mpfr_op:ident, $p:ident, $rm:ident, $rnd:ident, $op_info:expr $(, $cc:ident)?) => {
        let n3 = BigFloat::$astro_op(&($n1), &($n2), $p, $rm$(, &mut $cc)?);

        let mut f3 = Float::with_val($p as u32, 1);

        unsafe { mpfr::$mpfr_op(f3.as_raw_mut(), ($f1).as_raw(), ($f2).as_raw(), $rnd) };

        //println!("\n{:b}\n{:b}", $n1, $n2);
        //println!("\n{:b}\n{}", $n1, $f1.to_string_radix(2, None));
        //println!("\n{:b}\n{}", n3, f3.to_string_radix(2, None));

        assert_float_close(n3, f3, $p, &format!("{:?}", $op_info), $eq);
    };
    ($eq:literal, $n1:ident, $astro_op:ident, $f1:ident, $mpfr_op:ident, $p:ident, $rm:ident, $rnd:ident, $op_info:expr) => {
        let n3 = BigFloat::$astro_op(&($n1), $p, $rm);

        let mut f3 = Float::with_val($p as u32, 1);

        unsafe { mpfr::$mpfr_op(f3.as_raw_mut(), ($f1).as_raw(), $rnd) };

        // println!("\n{:b}\n{}", $n1, $f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", n3, f3.to_string_radix(2, None));

        assert_float_close(n3, f3, $p, &format!("{:?}", $op_info), $eq);
    };
    ($eq:literal, $n1:ident, $astro_op:ident, $f1:ident, $mpfr_op:ident, $p:ident, $rm:ident, $rnd:ident, $op_info:expr, $cc:ident) => {
        let n3 = BigFloat::$astro_op(&($n1), $p, $rm, &mut $cc);

        let mut f3 = Float::with_val($p as u32, 1);

        unsafe { mpfr::$mpfr_op(f3.as_raw_mut(), ($f1).as_raw(), $rnd) };

        // println!("\n{:b}\n{}", $n1, $f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", n3, f3.to_string_radix(2, None));

        assert_float_close(n3, f3, $p, &format!("{:?}", $op_info), $eq);
    };
}

// test constant value match
macro_rules! test_astro_const {
    ($astro_const:ident, $mpfr_const:ident, $p:ident, $rm:ident, $rnd:ident, $op_info:expr, $cc:ident) => {
        let n1: BigFloat = $cc.$astro_const($p, $rm);

        let mut f1 = Float::with_val($p as u32, 1);

        unsafe {
            mpfr::$mpfr_const(f1.as_raw_mut(), $rnd);
        }

        assert_float_close(n1, f1, $p, &format!("{:?}", $op_info), true);
    };
}

pub(crate) use test_astro_const;
pub(crate) use test_astro_op;

pub const fn get_prec_rng() -> usize {
    #[cfg(not(debug_assertions))]
    {
        157
    }

    #[cfg(debug_assertions)]
    {
        32
    }
}

pub fn get_float_pair(p: usize, emin: Exponent, emax: Exponent) -> (BigFloat, Float) {
    let n = BigFloat::random_normal(p, emin, emax);
    let f = conv_to_mpfr(p, &n);
    (n, f)
}

pub fn conv_to_mpfr(p: usize, n: &BigFloat) -> Float {
    let s1 = conv_str_to_mpfr_compat(format!("{:b}", n));
    let f = Float::with_val(p as u32, Float::parse_radix(s1, 2).unwrap());
    let s2 = conv_str_from_mpfr_compat(f.to_string_radix(2, None));
    //println!("\n{}\n{}", s1, s2);
    assert_eq!(*n, BigFloat::parse(&s2, Radix::Bin, p, RoundingMode::None));
    f
}

// assert float values are equal or differ not more than 1 ulp.
pub fn assert_float_close(n: BigFloat, f: Float, p: usize, op: &str, eq: bool) {
    if n.is_inf() {
        // inf
        let ovf = unsafe { mpfr::overflow_p() };
        assert!(f.is_infinite() || ovf != 0, "{}", op);
        if n.is_positive() {
            assert!(f.is_sign_positive(), "{}", op);
        } else {
            assert!(f.is_sign_negative(), "{}", op);
        }
    } else if n.is_nan() {
        // nan
        assert!(f.is_nan(), "{}", op);
    } else if n.is_subnormal() || n.is_zero() {
        // subnormal
        let unf = unsafe { mpfr::underflow_p() };
        if !f.is_zero() {
            assert!(unf != 0, "{}", op);
        }
    } else if eq {
        // n == f
        let s1 = f.to_string_radix(2, None);
        let s2 = conv_str_from_mpfr_compat(s1);
        let n2 = BigFloat::parse(&s2, Radix::Bin, p, RoundingMode::None);
        assert_eq!(n, n2, "{}", op);
    } else {
        // at most 1 ulp difference
        let s1 = f.to_string_radix(2, None);
        let s2 = conv_str_from_mpfr_compat(s1);
        let n2 = BigFloat::parse(&s2, Radix::Bin, p, RoundingMode::None);
        assert_eq!(
            n.mantissa_max_bit_len(),
            n2.mantissa_max_bit_len(),
            "{}",
            op
        );

        let d = n.sub(&n2, 1, RoundingMode::None).abs();

        let e1 = n.exponent().unwrap() as isize
            - (n.mantissa_max_bit_len().unwrap() - n.precision().unwrap()) as isize;
        let e2 = d.exponent().unwrap() as isize
            - (d.mantissa_max_bit_len().unwrap() - d.precision().unwrap()) as isize;

        //println!("\n{:?}\n{:?}\n{:?}\n{} {}", n, n2, d, e1, e2);

        if !d.is_zero() {
            assert!(
                e1 - e2 >= n.mantissa_max_bit_len().unwrap() as isize - 1,
                "{}",
                op
            );
        }
    }
}

pub fn conv_str_to_mpfr_compat(s: String) -> String {
    let (sig, exp) = if let Some(pos) = s.find('e') {
        s.split_at(pos + 1)
    } else {
        (s.as_str(), "0")
    };
    let expn = i64::from_str_radix(exp, 2).unwrap();
    sig.to_owned() + &expn.to_string()
}

pub fn conv_str_from_mpfr_compat(s: String) -> String {
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

pub fn get_random_rnd_pair() -> (RoundingMode, rnd_t) {
    match random::<u8>() % 5 {
        0 => (RoundingMode::ToEven, rnd_t::RNDN),
        1 => (RoundingMode::Up, rnd_t::RNDU),
        2 => (RoundingMode::Down, rnd_t::RNDD),
        3 => (RoundingMode::FromZero, rnd_t::RNDA),
        4 => (RoundingMode::ToZero, rnd_t::RNDZ),
        _ => unreachable!(),
    }
}

// Generates a number with mantissa like 1111111..1110000..00000
pub fn get_oned_zeroed(p: usize, exp_from: Exponent, exp_to: Exponent) -> BigFloat {
    let zero_bits = random::<usize>() % (p - 1);
    let mut m1 = vec![Word::MAX; p / WORD_BIT_SIZE];
    let i = zero_bits / WORD_BIT_SIZE;
    m1.iter_mut().take(i).for_each(|v| *v = 0);
    m1[i] <<= zero_bits % WORD_BIT_SIZE;

    bf_from_mantissa_and_exp_rng(&m1, exp_from, exp_to)
}

// Generates a number with mantissa like 111..111000..000111..111
pub fn get_oned_sides(p: usize, exp_from: Exponent, exp_to: Exponent) -> BigFloat {
    let one_bits = random::<usize>() % (p / 2).min(WORD_BIT_SIZE * 2) + 1;
    let mut m1 = vec![0; p / WORD_BIT_SIZE];
    let i = one_bits / WORD_BIT_SIZE;
    let m1l = m1.len();
    m1.iter_mut().take(i + 1).for_each(|v| *v = Word::MAX);
    m1[i] >>= one_bits % WORD_BIT_SIZE;
    m1.iter_mut().rev().take(i + 1).for_each(|v| *v = Word::MAX);
    m1[m1l - i - 1] <<= one_bits % WORD_BIT_SIZE;

    bf_from_mantissa_and_exp_rng(&m1, exp_from, exp_to)
}

// Generates a number with periodic mantissa
pub fn get_periodic(p: usize, exp_from: Exponent, exp_to: Exponent) -> BigFloat {
    let nbits = 4;
    let bits = random::<Word>() % ((1 << nbits) - 1) + 1;
    let mut w: Word = bits;
    for _ in 1..WORD_BIT_SIZE / nbits {
        w <<= nbits;
        w |= bits;
    }
    let mut m1 = vec![w; p / WORD_BIT_SIZE];
    *(m1.last_mut().unwrap()) |= 1 << (WORD_BIT_SIZE - 1);

    bf_from_mantissa_and_exp_rng(&m1, exp_from, exp_to)
}

// Generates a number with oned mantissa, but last bit is zero
pub fn get_last_zero(p: usize, exp_from: Exponent, exp_to: Exponent) -> BigFloat {
    let mut m1 = vec![Word::MAX; p / WORD_BIT_SIZE];
    m1[0] = Word::MAX - 1;

    bf_from_mantissa_and_exp_rng(&m1, exp_from, exp_to)
}

// Generates a number near 1.
pub fn get_near_one(p: usize) -> BigFloat {
    let e = (rand::random::<u8>() & 1) as Exponent;

    let random_bits = random::<usize>() % (p - 1);
    let i = random_bits / WORD_BIT_SIZE;

    let mut m1;
    if e == 0 {
        m1 = vec![Word::MAX; p / WORD_BIT_SIZE];
    } else {
        m1 = vec![0; p / WORD_BIT_SIZE];
    }
    m1[i] ^= random::<Word>() >> (random_bits % WORD_BIT_SIZE);

    m1.iter_mut().take(i).for_each(|v| *v = random());

    *m1.last_mut().unwrap() |= WORD_SIGNIFICANT_BIT;

    bf_from_mantissa_and_exp_rng(&m1, e, e)
}

pub fn bf_from_mantissa_and_exp_rng(m: &[Word], exp_from: Exponent, exp_to: Exponent) -> BigFloat {
    let e = if exp_from < exp_to {
        (rand::random::<isize>().abs() % (exp_to as isize - exp_from as isize) + exp_from as isize)
            as Exponent
    } else {
        exp_from
    };

    let s = if rand::random::<u8>() & 1 == 0 { Sign::Pos } else { Sign::Neg };

    BigFloat::from_words(m, s, e)
}
