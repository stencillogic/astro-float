/// Arbitrary precision constants.

pub mod ln2;
pub mod ln10;
pub mod pi;
pub mod e;

#[cfg(feature = "std")]
pub mod std;

#[cfg(not(feature = "std"))]
pub mod no_std;