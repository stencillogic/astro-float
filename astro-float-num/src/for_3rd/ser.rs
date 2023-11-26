//! Serialization of BigFloat.
//! Serialization to a string uses decimal radix.

use crate::BigFloat;
use serde::{Serialize, Serializer};

impl Serialize for BigFloat {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_string())
    }
}

#[cfg(test)]
mod tests {
    use serde_json::to_string;

    use crate::BigFloat;

    #[test]
    fn to_json() {
        assert_eq!(to_string(&BigFloat::new(0)).unwrap(), "\"0.0\"");
        assert_eq!(
            to_string(&BigFloat::from_f32(0.3, 64 + 1)).unwrap(),
            "\"3.00000011920928955078125e-1\""
        );
    }
}
