use astro_float::{BigFloat, Consts, RoundingMode};
use astro_float_macro::expr;

#[test]
fn macro_compile_tests() {
    let t = trybuild::TestCases::new();
    t.pass("./tests/tests/expr.rs");
}

#[test]
fn macro_run_tests() {
    let p = 320;
    let rm = RoundingMode::None;
    let mut cc = Consts::new().unwrap();

    let x = BigFloat::from(1.23);
    let y = BigFloat::from(4.56);

    let res: BigFloat = expr!(- 1, p, rm, &mut cc);
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
