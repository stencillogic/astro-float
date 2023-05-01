use astro_float::BigFloat;
use astro_float::Consts;
use astro_float::RoundingMode;
use astro_float_macro::expr;

fn main() {
    let rm = RoundingMode::None;
    let mut cc = Consts::new().unwrap();
    let _res: BigFloat = expr!(-6 * atan(1.0 / sqrt(3)), (256, rm, &mut cc));
}
