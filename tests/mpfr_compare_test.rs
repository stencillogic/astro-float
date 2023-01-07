use astro_float::{WORD_BIT_SIZE, BigFloat, EXPONENT_MIN, EXPONENT_MAX, Exponent, RoundingMode, Radix};
use rand::random;
use rug::{Float, float::{exp_min, exp_max}};
use gmp_mpfr_sys::{mpfr, gmp::exp_t};


#[test]
fn mpfr_compare() {
    let p_rng = 3; //157;    // >~ 10000 bit
    let p_min = 1;

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

    // round
    for _ in 0..10000 {
        let p1 = (random::<usize>() % p_rng + 3) * WORD_BIT_SIZE;
        let p = p1 - random::<usize>() % WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();

        let (n1, mut f1) = get_float_pair(p1, 0, 0);

        let n1 = n1.round(p, rm);

        unsafe { mpfr::prec_round(f1.as_raw_mut(), p as mpfr::prec_t, rnd); }

        assert_float_eq(n1, f1, p, "prec round");
    }

    // add, sub
    for _ in 0..10000 {
        let p1 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;
        let p = (random::<usize>() % p_rng + p_min) * WORD_BIT_SIZE;

        let (rm, rnd) = get_random_rnd_pair();

        let (n1, f1) = get_float_pair(p1, -(p1 as Exponent), p1 as Exponent);
        let (n2, f2) = get_float_pair(p2, -(p2 as Exponent), p2 as Exponent);

        // println!("\n{:?}", rm);
        // println!("{:b}\n{}", n1, f1.to_string_radix(2, None));
        // println!("\n{:b}\n{}", n2, f2.to_string_radix(2, None));

        // add
        let n3 = n1.add(&n2, p, rm);

        let mut f3 = Float::with_val(p as u32, 1);
        unsafe { mpfr::add(f3.as_raw_mut(), f1.as_raw(), f2.as_raw(), rnd) };

        // println!("\n{:b}\n{}", n3, f3.to_string_radix(2, None));
        // println!("\n{:b}", n1.add(&n2, p1.max(p2) + 1, rm));

        assert_float_eq(n3, f3, p, "add");

        // sub
        let n3 = n1.sub(&n2, p, rm);

        let mut f3 = Float::with_val(p as u32, 1);
        unsafe { mpfr::sub(f3.as_raw_mut(), f1.as_raw(), f2.as_raw(), rnd) };

        assert_float_eq(n3, f3, p, "sub");
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
    let s1 = f.to_string_radix(2, None);
    let s2 = conv_str_from_mpfr_compat(s1);
    let n2 = BigFloat::parse(&s2, Radix::Bin, p, RoundingMode::None);
    assert_eq!(n, n2, "{}", op);
}

fn conv_str_to_mpfr_compat(s: String) -> String {
    let (sig, exp) = s.split_at(s.find('e').unwrap() + 1);
    let expn = i32::from_str_radix(exp, 2).unwrap();
    sig.to_owned() + &expn.to_string()
}

fn conv_str_from_mpfr_compat(s: String) -> String {
    if let Some(epos) = s.find('e') {
        let (sig, exp) = s.split_at(epos + 1);
        let expn = exp.parse::<i32>().unwrap();
        if expn < 0 {
            sig.to_owned() + "-" + &format!("{:b}", -expn)
        } else {
            sig.to_owned() + &format!("{:b}", expn)
        }
        
    } else {
        s
    }
}

fn get_random_rnd_pair() -> (RoundingMode, mpfr::rnd_t) {
    match random::<u8>() % 5 {
        0 => (RoundingMode::ToEven, mpfr::rnd_t::RNDN),
        1 => (RoundingMode::Up, mpfr::rnd_t::RNDU),
        2 => (RoundingMode::Down, mpfr::rnd_t::RNDD),
        3 => (RoundingMode::FromZero, mpfr::rnd_t::RNDA),
        4 => (RoundingMode::ToZero, mpfr::rnd_t::RNDZ),
        _ => unreachable!(),
    }
}