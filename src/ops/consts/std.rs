//! Std library declarations.


use super::e::ECache;
use super::ln2::Ln2Cache;
use super::ln10::Ln10Cache;
use super::pi::PiCache;

use std::cell::RefCell;

thread_local! {

    /// Euler's number.
    pub static E: RefCell<ECache> = {
        RefCell::new(ECache::new().unwrap())
    };

    /// Natural logarithm of 2.
    pub static LN_2: RefCell<Ln2Cache> = {
        RefCell::new(Ln2Cache::new().unwrap())
    };

    /// Natural logarithm of 10.
    pub static LN_10: RefCell<Ln10Cache> = {
        RefCell::new(Ln10Cache::new().unwrap())
    };

    /// Pi number.
    pub static PI: RefCell<PiCache> = {
        RefCell::new(PiCache::new().unwrap())
    };
}
