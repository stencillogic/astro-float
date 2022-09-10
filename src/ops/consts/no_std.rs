//! Std library declarations.


use super::e::ECache;
use super::ln2::Ln2Cache;
use super::ln10::Ln10Cache;
use super::pi::PiCache;


struct consts {

    /// Euler's number.
    pub E: ECache,

    /// Ln of 2.
    pub Ln2: Ln2Cache,

    /// Ln of 10.
    pub Ln10: Ln10Cache,

    /// Pi number.
    pub PI: PiCache,
}
