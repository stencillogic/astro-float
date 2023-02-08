#[test]
fn run_macro_tests() {
    let t = trybuild::TestCases::new();
    t.pass("./tests/tests/expr.rs");
}
