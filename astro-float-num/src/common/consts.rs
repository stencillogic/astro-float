//! Static constants.

use crate::{defs::DEFAULT_P, num::BigFloatNumber};
use lazy_static::lazy_static;

#[cfg(feature = "std")]
use crate::ops::consts::Consts;
#[cfg(feature = "std")]
use core::cell::RefCell;

lazy_static! {

    /// 1
    pub(crate) static ref ONE: BigFloatNumber = BigFloatNumber::from_word(1, DEFAULT_P).expect("Constant ONE initialization.");

    /// 2
    pub(crate) static ref TWO: BigFloatNumber = BigFloatNumber::from_word(2, DEFAULT_P).expect("Constant TWO initialization.");

    /// 4
    pub(crate) static ref FOUR: BigFloatNumber = BigFloatNumber::from_word(4, DEFAULT_P).expect("Constant FOUR initialization.");

    /// 6
    pub(crate) static ref SIX: BigFloatNumber = BigFloatNumber::from_word(6, DEFAULT_P).expect("Constant SIX initialization.");

    /// 8
    pub(crate) static ref EIGHT: BigFloatNumber = BigFloatNumber::from_word(8, DEFAULT_P).expect("Constant EIGHT initialization.");

    /// 16
    pub(crate) static ref SIXTEEN: BigFloatNumber = BigFloatNumber::from_word(16, DEFAULT_P).expect("Constant SIXTEEN initialization.");

    /// 3
    pub(crate) static ref THREE: BigFloatNumber = BigFloatNumber::from_word(3, DEFAULT_P).expect("Constant THREE initialization.");

    /// 5
    pub(crate) static ref FIVE: BigFloatNumber = BigFloatNumber::from_word(5, DEFAULT_P).expect("Constant FIVE initialization.");

    /// 10
    pub(crate) static ref TEN: BigFloatNumber = BigFloatNumber::from_word(10, DEFAULT_P).expect("Constant TEN initialization.");

    /// 15
    pub(crate) static ref FIFTEEN: BigFloatNumber = BigFloatNumber::from_word(15, DEFAULT_P).expect("Constant FIFTEEN initialization.");

    /// 24
    pub(crate) static ref C24: BigFloatNumber = BigFloatNumber::from_word(24, DEFAULT_P).expect("Constant C24 initialization.");

    /// 40
    pub(crate) static ref FOURTY: BigFloatNumber = BigFloatNumber::from_word(40, DEFAULT_P).expect("Constant FOURTY initialization.");

    /// 120
    pub(crate) static ref C120: BigFloatNumber = BigFloatNumber::from_word(120, DEFAULT_P).expect("Constant C24 initialization.");
}

// TODO: Consider using in std environment everywhere Consts are needed.
#[cfg(feature = "std")]
thread_local! {
    pub static TENPOWERS: RefCell<Consts> = RefCell::new(Consts::new().expect("Failed to initialize thread-local constants cache"));
}
