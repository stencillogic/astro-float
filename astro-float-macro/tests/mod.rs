//! Tests to verify the macro expands.

#[test]
fn macro_compile_tests() {
    let t = trybuild::TestCases::new();
    t.pass("./tests/tests/expr.rs");
}
