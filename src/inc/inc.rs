//! BigFloat number with increased mantissa length for providing more accurate compuations.
use crate::defs::DECIMAL_PARTS as DECIMAL_PARTS_BASE;
use crate::defs::DECIMAL_SIGN_POS;
use crate::defs::DECIMAL_BASE;
use crate::defs::DECIMAL_BASE_LOG10;

pub const DECIMAL_PARTS: usize = DECIMAL_PARTS_BASE + 1;
pub const DECIMAL_POSITIONS: usize = DECIMAL_PARTS * DECIMAL_BASE_LOG10;
pub const ZEROED_MANTISSA: [i16; DECIMAL_PARTS] = [0; DECIMAL_PARTS];

/// Eulers number.
pub(crate) const E: BigFloatInc = BigFloatInc {
    m: [2471, 7757, 6249, 3526, 7471, 6028, 2353, 9045, 2845, 2818, 2718],
    n: DECIMAL_POSITIONS as i16, 
    sign: DECIMAL_SIGN_POS, 
    e: 1 - (DECIMAL_POSITIONS as i8),
};

/// BigFloat number with increased mantissa length for providing more accurate compuations.
#[derive(Copy, Clone, Debug)]
pub (crate) struct BigFloatInc {
    pub (crate) sign: i8,                // sign
    pub (crate) e: i8,                   // exponent
    pub (crate) n: i16,                  // the number of decimal positions in the mantissa excluding leading zeroes
    pub (crate) m: [i16; DECIMAL_PARTS], // mantissa
}


impl BigFloatInc {

    /// Return new BigFloatInc with value zero.
    pub fn new() -> Self {
        BigFloatInc {
            sign: DECIMAL_SIGN_POS,
            e: 0,
            n: 0,
            m: ZEROED_MANTISSA,
        }
    }

    /// Return new BigFloatInc with value one.
    pub fn one() -> Self {
        let mut val = Self::new();
        val.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/10;
        val.n = DECIMAL_POSITIONS as i16;
        val.e = 1 - DECIMAL_POSITIONS as i8;
        val
    }

    /// Return new BigFloat with value two.
    pub fn two() -> Self {
        let mut val = Self::new();
        val.m[DECIMAL_PARTS-1] = DECIMAL_BASE as i16/5;
        val.n = DECIMAL_POSITIONS as i16;
        val.e = 1 - DECIMAL_POSITIONS as i8;
        val
    }

}
