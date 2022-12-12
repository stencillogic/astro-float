//! Static constants.

use crate::{defs::DEFAULT_P, num::BigFloatNumber};
use lazy_static::lazy_static;

lazy_static! {

    /// 1
    pub static ref ONE: BigFloatNumber = BigFloatNumber::from_word(1, DEFAULT_P).expect("Constant ONE initialization.");

    /// 2
    pub static ref TWO: BigFloatNumber = BigFloatNumber::from_word(2, DEFAULT_P).expect("Constant TWO initialization.");

    /// 4
    pub static ref FOUR: BigFloatNumber = BigFloatNumber::from_word(4, DEFAULT_P).expect("Constant FOUR initialization.");

    /// 6
    pub static ref SIX: BigFloatNumber = BigFloatNumber::from_word(6, DEFAULT_P).expect("Constant SIX initialization.");

    /// 8
    pub static ref EIGHT: BigFloatNumber = BigFloatNumber::from_word(8, DEFAULT_P).expect("Constant EIGHT initialization.");

    /// 16
    pub static ref SIXTEEN: BigFloatNumber = BigFloatNumber::from_word(16, DEFAULT_P).expect("Constant SIXTEEN initialization.");

    /// 3
    pub static ref THREE: BigFloatNumber = BigFloatNumber::from_word(3, DEFAULT_P).expect("Constant THREE initialization.");

    /// 10
    pub static ref TEN: BigFloatNumber = BigFloatNumber::from_word(10, DEFAULT_P).expect("Constant TEN initialization.");

    /// 15
    pub static ref FIFTEEN: BigFloatNumber = BigFloatNumber::from_word(15, DEFAULT_P).expect("Constant FIFTEEN initialization.");

    /// 40
    pub static ref FOURTY: BigFloatNumber = BigFloatNumber::from_word(40, DEFAULT_P).expect("Constant FOURTY initialization.");

    /// 10^9
    pub static ref TEN_POW_9: BigFloatNumber = BigFloatNumber::from_word(1000000000, DEFAULT_P).expect("Constant TEN_POW_9 initialization.");
}
