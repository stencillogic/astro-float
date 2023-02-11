use astro_float::{BigFloat, Consts, RoundingMode, Sign, WORD_MAX, WORD_SIGNIFICANT_BIT};
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
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Pos, -123),
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Neg, -123),
    ] {
        let y1 = x.exp(p * 2, RoundingMode::None, &mut cc);
        let mut z1 = y1.ln(p * 2, RoundingMode::None, &mut cc);
        z1.set_precision(p, rm).unwrap();

        let y2 = x.exp(p, RoundingMode::None, &mut cc);
        let z2 = y2.ln(p, RoundingMode::None, &mut cc);

        let y = expr!(ln(exp(x)), p, rm, &mut cc);

        assert_eq!(z1, y);
        assert_ne!(z2, y);
    }

    // exp
    for x in [
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Pos, 1000000),
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Pos, 1000000),
    ] {
        let y1 = x.ln(p * 2, RoundingMode::None, &mut cc);
        let mut z1 = y1.exp(p * 2, RoundingMode::None, &mut cc);
        z1.set_precision(p, rm).unwrap();

        let y2 = x.ln(p, RoundingMode::None, &mut cc);
        let z2 = y2.exp(p, RoundingMode::None, &mut cc);

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

        let y2 = two.pow(&x, p, RoundingMode::None, &mut cc);
        let z2 = y2.log2(p, RoundingMode::None, &mut cc);

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

        let y2 = ten.pow(&x, p, RoundingMode::None, &mut cc);
        let z2 = y2.log10(p, RoundingMode::None, &mut cc);

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

            let y2 = b.pow(&x, p, RoundingMode::None, &mut cc);
            let z2 = y2.log(&b, p, RoundingMode::None, &mut cc);

            let y = expr!(log(pow(b, x), b), p, rm, &mut cc);

            assert_eq!(z1, y);
            assert_ne!(z2, y);
        }
    }

    // pow
    for x in [
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Pos, 1000000),
        BigFloat::from_words(&[234, WORD_SIGNIFICANT_BIT], Sign::Pos, -1000000),
    ] {
        for b in [
            BigFloat::from_words(&[123, WORD_MAX], Sign::Pos, 0),
            BigFloat::from_words(&[123, WORD_SIGNIFICANT_BIT], Sign::Pos, 1),
        ] {
            let y1 = x.log(&b, p * 4, RoundingMode::None, &mut cc);
            let mut z1 = b.pow(&y1, p * 4, RoundingMode::None, &mut cc);
            z1.set_precision(p, rm).unwrap();

            let y2 = x.log(&b, p, RoundingMode::None, &mut cc);
            let z2 = b.pow(&y2, p, RoundingMode::None, &mut cc);

            let y = expr!(pow(b, log(x, b)), p, rm, &mut cc);

            assert_eq!(z1, y);
            assert_ne!(z2, y);
        }
    }

    // sin
    let n = BigFloat::parse(
        "1.234567890123456789e+77",
        astro_float::Radix::Dec,
        128,
        RoundingMode::None,
    );
    let y1 = n.sin(128, rm, &mut cc);
    let n = BigFloat::parse(
        "1.234567890123456789e+77",
        astro_float::Radix::Dec,
        320,
        RoundingMode::None,
    );
    let mut y2 = n.sin(320, rm, &mut cc);
    y2.set_precision(128, rm).unwrap();

    let z = expr!(sin("1.234567890123456789e+77"), 128, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);

    // cos
    let n = BigFloat::parse(
        "1.234567890123456789e+77",
        astro_float::Radix::Dec,
        128,
        RoundingMode::None,
    );
    let y1 = n.cos(128, rm, &mut cc);
    let n = BigFloat::parse(
        "1.234567890123456789e+77",
        astro_float::Radix::Dec,
        320,
        RoundingMode::None,
    );
    let mut y2 = n.cos(320, rm, &mut cc);
    y2.set_precision(128, rm).unwrap();

    let z = expr!(cos("1.234567890123456789e+77"), 128, rm, &mut cc);

    assert_ne!(y1, z);
    assert_eq!(y2, z);
}
