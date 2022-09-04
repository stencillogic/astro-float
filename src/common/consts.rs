//! Static constants.

use crate::num::BigFloatNumber;
use lazy_static::lazy_static;


lazy_static! {
    pub static ref ONE: BigFloatNumber = BigFloatNumber::from_word(1, 1).unwrap();
    pub static ref TWO: BigFloatNumber = BigFloatNumber::from_word(2, 1).unwrap();
    pub static ref FOUR: BigFloatNumber = BigFloatNumber::from_word(4, 1).unwrap();
    pub static ref EIGHT: BigFloatNumber = BigFloatNumber::from_word(8, 1).unwrap();
    pub static ref SIXTEEN: BigFloatNumber = BigFloatNumber::from_word(16, 1).unwrap();
    pub static ref THREE: BigFloatNumber = BigFloatNumber::from_word(3, 1).unwrap();
    pub static ref TEN: BigFloatNumber = BigFloatNumber::from_word(10, 1).unwrap();
    pub static ref FIFTEEN: BigFloatNumber = BigFloatNumber::from_word(15, 1).unwrap();
}