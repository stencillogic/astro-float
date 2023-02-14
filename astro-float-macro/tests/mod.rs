use astro_float::{
    BigFloat, Consts, RoundingMode, Sign, WORD_BIT_SIZE, WORD_MAX, WORD_SIGNIFICANT_BIT,
};
use astro_float_macro::expr;

#[test]
fn macro_compile_tests() {
    let t = trybuild::TestCases::new();
    t.pass("./tests/tests/expr.rs");
}

#[test]
fn macro_run_basic_tests() {
    let p = 320;
    let rm = RoundingMode::None;
    let mut cc = Consts::new().unwrap();

    let x = BigFloat::from(1.23);
    let y = BigFloat::from(4.56);

    let res: BigFloat = expr!(-1, p, rm, &mut cc);
    debug_assert_eq!(res, BigFloat::from(-1));

    let res: BigFloat = expr!(2 + 3, p, rm, &mut cc);
    debug_assert_eq!(res, BigFloat::from(5));

    let res: BigFloat = expr!(3 - 4, p, rm, &mut cc);
    debug_assert_eq!(res, BigFloat::from(-1));

    let res: BigFloat = expr!(4 * 5, p, rm, &mut cc);
    debug_assert_eq!(res, BigFloat::from(20));

    let res: BigFloat = expr!(5 / 6, p, rm, &mut cc);
    debug_assert_eq!(res, BigFloat::from(5).div(&BigFloat::from(6), p, rm));

    let res: BigFloat = expr!(6 % 7, p, rm, &mut cc);
    debug_assert_eq!(res, BigFloat::from(6));

    let res: BigFloat = expr!(ln(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.ln(p, rm, &mut cc));

    let res: BigFloat = expr!(log2(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.log2(p, rm, &mut cc));

    let res: BigFloat = expr!(log10(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.log10(p, rm, &mut cc));

    let res: BigFloat = expr!(log(x, y), p, rm, &mut cc);
    debug_assert_eq!(res, x.log(&y, p, rm, &mut cc));

    let res: BigFloat = expr!(exp(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.exp(p, rm, &mut cc));

    let res: BigFloat = expr!(pow(x, y), p, rm, &mut cc);
    debug_assert_eq!(res, x.pow(&y, p, rm, &mut cc));

    let res: BigFloat = expr!(sin(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.sin(p, rm, &mut cc));

    let res: BigFloat = expr!(cos(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.cos(p, rm, &mut cc));

    let res: BigFloat = expr!(tan(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.tan(p, rm, &mut cc));

    let x = BigFloat::from(0.123);

    let res: BigFloat = expr!(asin(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.asin(p, rm, &mut cc));

    let res: BigFloat = expr!(acos(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.acos(p, rm, &mut cc));

    let res: BigFloat = expr!(atan(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.atan(p, rm, &mut cc));

    let x = BigFloat::from(1.23);

    let res: BigFloat = expr!(sinh(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.sinh(p, rm, &mut cc));

    let res: BigFloat = expr!(cosh(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.cosh(p, rm, &mut cc));

    let res: BigFloat = expr!(tanh(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.tanh(p, rm, &mut cc));

    let res: BigFloat = expr!(asinh(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.asinh(p, rm, &mut cc));

    let res: BigFloat = expr!(acosh(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.acosh(p, rm, &mut cc));

    let x = BigFloat::from(0.123);

    let res: BigFloat = expr!(atanh(x), p, rm, &mut cc);
    debug_assert_eq!(res, x.atanh(p, rm, &mut cc));
}

#[test]
fn macro_run_err_test() {
    // sub cancellation test
    let p = 192;
    let rm = RoundingMode::ToEven;
    let mut cc = Consts::new().unwrap();
    let two = BigFloat::from(2);
    let ten = BigFloat::from(10);

    // ln
    for x in [
        BigFloat::from_words(&[234, 0, WORD_SIGNIFICANT_BIT], Sign::Pos, -123),
        BigFloat::from_words(&[234, 0, WORD_SIGNIFICANT_BIT], Sign::Neg, -123),
    ] {
        let y1 = x.exp(p * 3, RoundingMode::None, &mut cc);
        let mut z1 = y1.ln(p * 3, RoundingMode::None, &mut cc);
        z1.set_precision(p, rm).unwrap();

        let y2 = x.exp(p + 1, RoundingMode::None, &mut cc);
        let z2 = y2.ln(p, rm, &mut cc);

        let y = expr!(ln(exp(x)), p, rm, &mut cc);

        assert_eq!(z1, y);
        assert_ne!(z2, y);
    }

    // exp
    for x in [
        BigFloat::from_words(&[234, 0, WORD_SIGNIFICANT_BIT], Sign::Pos, 1000000),
        BigFloat::from_words(&[234, 0, WORD_SIGNIFICANT_BIT], Sign::Pos, -1000000),
    ] {
        let y1 = x.ln(p * 3, RoundingMode::None, &mut cc);
        let mut z1 = y1.exp(p * 3, RoundingMode::None, &mut cc);
        z1.set_precision(p, rm).unwrap();

        let y2 = x.ln(p, RoundingMode::None, &mut cc);
        let z2 = y2.exp(p, rm, &mut cc);

        let y = expr!(exp(ln(x)), p, rm, &mut cc);

        assert_eq!(z1, y);
        assert_ne!(z2, y);
    }

    // log2
    for x in [
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Pos, -123),
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Neg, -123),
    ] {
        let y1 = two.pow(&x, p * 2, RoundingMode::None, &mut cc);
        let mut z1 = y1.log2(p * 2, RoundingMode::None, &mut cc);
        z1.set_precision(p, rm).unwrap();

        let y2 = two.pow(&x, p + 1, RoundingMode::None, &mut cc);
        let z2 = y2.log2(p, rm, &mut cc);

        let y = expr!(log2(pow(2, x)), p, rm, &mut cc);

        assert_eq!(z1, y);
        assert_ne!(z2, y);
    }

    // log10
    for x in [
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Pos, -123),
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Neg, -123),
    ] {
        let y1 = ten.pow(&x, p * 2, RoundingMode::None, &mut cc);
        let mut z1 = y1.log10(p * 2, RoundingMode::None, &mut cc);
        z1.set_precision(p, rm).unwrap();

        let y2 = ten.pow(&x, p + 1, RoundingMode::None, &mut cc);
        let z2 = y2.log10(p, rm, &mut cc);

        let y = expr!(log10(pow(10, x)), p, rm, &mut cc);

        assert_eq!(z1, y);
        assert_ne!(z2, y);
    }

    // log
    for x in [
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Pos, -123),
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Neg, -123),
    ] {
        for b in [
            BigFloat::from_words(&[123, WORD_MAX], Sign::Pos, 0),
            BigFloat::from_words(&[123, WORD_SIGNIFICANT_BIT], Sign::Pos, 1),
        ] {
            let y1 = b.pow(&x, p * 4, RoundingMode::None, &mut cc);
            let mut z1 = y1.log(&b, p * 4, RoundingMode::None, &mut cc);
            z1.set_precision(p, rm).unwrap();

            let y2 = b.pow(&x, p + 1, RoundingMode::None, &mut cc);
            let z2 = y2.log(&b, p, rm, &mut cc);

            let y = expr!(log(pow(b, x), b), p, rm, &mut cc);

            assert_eq!(z1, y);
            assert_ne!(z2, y);
        }
    }

    let s1 = "1.0000000000000000023456";
    let s2 = "1.234567890123456789e+20";
    let b = BigFloat::parse(s1, astro_float::Radix::Dec, p + 192, RoundingMode::None);
    let n = BigFloat::parse(s2, astro_float::Radix::Dec, p + 192, RoundingMode::None);
    let y1 = b.pow(&n, p, rm, &mut cc);
    let mut y2 = b.pow(&n, p + 192, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(pow(s1, s2), p, rm, &mut cc);

    assert_eq!(y2, z);
    assert_ne!(y1, z);

    let s1 = "0.9999999999999999923456";
    let s2 = "-1.234567890123456789e+25";
    let b = BigFloat::parse(s1, astro_float::Radix::Dec, p + 192, RoundingMode::None);
    let n = BigFloat::parse(s2, astro_float::Radix::Dec, p + 192, RoundingMode::None);
    let y1 = b.pow(&n, p, rm, &mut cc);
    let mut y2 = b.pow(&n, p + 192, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(pow(s1, s2), p, rm, &mut cc);

    assert_eq!(y2, z);
    assert_ne!(y1, z);

    // sin
    let s1 = "1.234567890123456789e+77";
    let n = BigFloat::parse(s1, astro_float::Radix::Dec, 128, RoundingMode::None);
    let y1 = n.sin(128, rm, &mut cc);
    let n = BigFloat::parse(s1, astro_float::Radix::Dec, 320, RoundingMode::None);
    let mut y2 = n.sin(320, RoundingMode::None, &mut cc);
    y2.set_precision(128, rm).unwrap();

    let z = expr!(sin(s1), 128, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // cos
    let n = BigFloat::parse(s1, astro_float::Radix::Dec, 128, RoundingMode::None);
    let y1 = n.cos(128, rm, &mut cc);
    let n = BigFloat::parse(s1, astro_float::Radix::Dec, 320, RoundingMode::None);
    let mut y2 = n.cos(320, RoundingMode::None, &mut cc);
    y2.set_precision(128, rm).unwrap();

    let z = expr!(cos(s1), 128, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // tan
    let s1 = "1.1001001000011111101101010100010001000010110100011000010001101001100010011000110011000101000101110000000110111000001110011010001e+0";
    let n = BigFloat::parse(s1, astro_float::Radix::Bin, p, RoundingMode::None);
    let y1 = n.tan(p, rm, &mut cc);

    let n = BigFloat::parse(
        s1,
        astro_float::Radix::Dec,
        y1.exponent().unwrap() as usize * 2 + p,
        RoundingMode::None,
    );
    let mut y2 = n.tan(
        y1.exponent().unwrap() as usize * 2 + p,
        RoundingMode::None,
        &mut cc,
    );
    y2.set_precision(p, rm).unwrap();

    let z = expr!(tan(s1), p, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // asin
    let mut x = cc.pi(p - WORD_BIT_SIZE, RoundingMode::None);
    x.set_exponent(1);

    let z = x.sin(p + 1, RoundingMode::None, &mut cc);
    let y1 = z.asin(p, rm, &mut cc);

    let z = x.sin(p * 2, RoundingMode::None, &mut cc);
    let mut y2 = z.asin(p * 2, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(asin(sin(x)), p, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // acos
    let x = BigFloat::from_words(&[234, WORD_MAX], Sign::Pos, -100);

    let z = x.cos(p + 1, RoundingMode::None, &mut cc);
    let y1 = z.acos(p, rm, &mut cc);

    let z = x.cos(p * 3, RoundingMode::None, &mut cc);
    let mut y2 = z.acos(p * 3, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(acos(cos(x)), p, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // atan
    let x = BigFloat::from_words(&[234, WORD_MAX], Sign::Neg, 128);
    let z = x.atan(p + 1, RoundingMode::None, &mut cc);
    let y1 = z.tan(p, rm, &mut cc);

    let z = x.atan(p + 256, RoundingMode::None, &mut cc);
    let mut y2 = z.tan(p + 256, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(tan(atan(x)), p, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // sinh
    let x = BigFloat::from_words(&[234, 0, WORD_SIGNIFICANT_BIT], Sign::Pos, 1000000);
    let y1 = x.asinh(p * 3, RoundingMode::None, &mut cc);
    let mut z1 = y1.sinh(p * 3, RoundingMode::None, &mut cc);
    z1.set_precision(p, rm).unwrap();

    let y2 = x.asinh(p, RoundingMode::None, &mut cc);
    let z2 = y2.sinh(p, rm, &mut cc);

    let y = expr!(sinh(asinh(x)), p, rm, &mut cc);

    assert_eq!(z1, y);
    assert_ne!(z2, y);

    // cosh
    let x = BigFloat::from_words(&[234, 0, WORD_SIGNIFICANT_BIT], Sign::Pos, 1000000);
    let y1 = x.acosh(p * 3, RoundingMode::None, &mut cc);
    let mut z1 = y1.cosh(p * 3, RoundingMode::None, &mut cc);
    z1.set_precision(p, rm).unwrap();

    let y2 = x.acosh(p, RoundingMode::None, &mut cc);
    let z2 = y2.cosh(p, rm, &mut cc);

    let y = expr!(cosh(acosh(x)), p, rm, &mut cc);

    assert_eq!(z1, y);
    assert_ne!(z2, y);

    // tanh
    let x = BigFloat::from_words(
        &[
            9236992107743244213,
            15337583864450254957,
            14091965535849219585,
            16039319970605309248,
        ],
        Sign::Pos,
        -98,
    );
    let y1 = x.tanh(p, rm, &mut cc);

    let mut y2 = x.tanh(p + 1, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(tanh(x), p, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // asinh
    let x = BigFloat::from_words(
        &[
            15072532489182604725,
            17813245450760625462,
            6342009188451080896,
            16404240047229715662,
        ],
        Sign::Pos,
        -57,
    );

    let y1 = x.asinh(p, rm, &mut cc);

    let mut y2 = x.asinh(p + 1, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(asinh(x), p, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // acosh
    let x = BigFloat::from_words(&[123, 123, WORD_SIGNIFICANT_BIT], Sign::Pos, -100);

    let z = x.cosh(p + 1, RoundingMode::None, &mut cc);
    let y1 = z.acosh(p, rm, &mut cc);

    let z = x.cosh(p + 256, RoundingMode::None, &mut cc);
    let mut y2 = z.acosh(p + 256, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(acosh(cosh(x)), p, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // atanh
    let x = BigFloat::from_words(&[123, 123, WORD_SIGNIFICANT_BIT], Sign::Pos, 7);

    let z = x.tanh(p + 1, RoundingMode::None, &mut cc);
    let y1 = z.atanh(p, rm, &mut cc);

    let z = x.tanh(p + 256, RoundingMode::None, &mut cc);
    let mut y2 = z.atanh(p + 256, RoundingMode::None, &mut cc);
    y2.set_precision(p, rm).unwrap();

    let z = expr!(atanh(tanh(x)), p, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);
}
