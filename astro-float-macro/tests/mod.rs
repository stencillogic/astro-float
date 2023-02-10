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
    let x = BigFloat::from(6);
    let res: BigFloat = expr!(
        p,
        rm,
        &mut cc,
        log(
            log10(log2(ln(cbrt(sqrt(recip(-1 + 2 - 3 * 4 / 5 % 6)))))),
            3
        ) + exp(pow(1, 2)
            + sin(100)
            + cos(100)
            + tan(100)
            + asin(100)
            + acos(100)
            + atan(100)
            + sinh(100)
            + cosh(100)
            + tanh(100)
            + asinh(100)
            + acosh(100)
            + atanh(100))
    );
    let pi = cc.pi(p, rm);
    println!("{:?}", res);
    println!("{:?}", pi);
}
