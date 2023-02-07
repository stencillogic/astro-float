use astro_float_macro::expr;
use astro_float::BigFloat;
use astro_float::RoundingMode;

fn main() {
    let x = BigFloat::from_word(1, 128);
    let rm = RoundingMode::None;
    expr!(256, rm, 1 + 2.300000000000000000000000000000000000000001 * ln(x) + exp(x, 129, RoundingMode::ToEven));
}