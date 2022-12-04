//! Static constants.

use crate::num::BigFloatNumber;
use lazy_static::lazy_static;

lazy_static! {

    /// 1
    pub static ref ONE: BigFloatNumber = BigFloatNumber::from_word(1, 1).unwrap();

    /// 2
    pub static ref TWO: BigFloatNumber = BigFloatNumber::from_word(2, 1).unwrap();

    /// 4
    pub static ref FOUR: BigFloatNumber = BigFloatNumber::from_word(4, 1).unwrap();

    /// 6
    pub static ref SIX: BigFloatNumber = BigFloatNumber::from_word(6, 1).unwrap();

    /// 8
    pub static ref EIGHT: BigFloatNumber = BigFloatNumber::from_word(8, 1).unwrap();

    /// 16
    pub static ref SIXTEEN: BigFloatNumber = BigFloatNumber::from_word(16, 1).unwrap();

    /// 3
    pub static ref THREE: BigFloatNumber = BigFloatNumber::from_word(3, 1).unwrap();

    /// 10
    pub static ref TEN: BigFloatNumber = BigFloatNumber::from_word(10, 1).unwrap();

    /// 15
    pub static ref FIFTEEN: BigFloatNumber = BigFloatNumber::from_word(15, 1).unwrap();

    /// 40
    pub static ref FOURTY: BigFloatNumber = BigFloatNumber::from_word(40, 1).unwrap();

    /// 10^9
    pub static ref TEN_POW_9: BigFloatNumber = BigFloatNumber::from_word(1000000000, 1).unwrap();
}
