//! Serialization of BigFloatNumber.
//! Serialization to a string uses decimal radix.

use serde::ser::Error;
use serde::{Serialize, Serializer};
use crate::{BigFloatNumber, Radix, RoundingMode};

#[cfg(not(feature="std"))]
use alloc::format;


impl Serialize for BigFloatNumber {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.format(Radix::Dec, RoundingMode::None) {
            Ok(s) => serializer.serialize_str(&s),
            Err(e) => Err(Error::custom(format!("{e:?}"))),
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::to_string;

    use crate::BigFloatNumber;

    #[test]
    fn to_json() {
        assert_eq!(
            to_string(&BigFloatNumber::new(0).unwrap()).unwrap(),
            "\"0.0\""
        );
        assert_eq!(
            to_string(&BigFloatNumber::from_f32(64 + 1, 0.3).unwrap()).unwrap(),
            "\"3.00000011920928955078125e-1\""
        );
    }
}
