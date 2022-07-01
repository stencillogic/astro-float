//! Parser parses numbers represented in scientific format.

use std::str::Chars;
use crate::defs::{DECIMAL_SIGN_POS, DECIMAL_SIGN_NEG, DECIMAL_POSITIONS};

pub struct ParserState<'a> {
    chars: Chars<'a>,
    cur_ch: Option<char>,
    sign: i8,
    mantissa_bytes: [u8; DECIMAL_POSITIONS],
    n: usize,
    e: i32,
    inf: bool,
    nan: bool,
    valid: bool,
}

impl<'a> ParserState<'a> {
    fn new(s: &'a str) -> Self {
        ParserState {
            chars: s.chars(),
            cur_ch: None,
            sign: DECIMAL_SIGN_POS,
            mantissa_bytes: [0; DECIMAL_POSITIONS],
            n: 0,
            e: 0,
            inf: false,
            nan: false,
            valid: false,
        }
    }

    /// Returns next character of a string in lower case, 
    /// or None if string end reached.
    fn next_char(&mut self) -> Option<char> {
        self.cur_ch = self.chars.next().map(|c| c.to_ascii_lowercase());
        self.cur_ch
    }

    fn cur_char(&self) -> Option<char> {
        self.cur_ch
    }

    pub fn is_valid(&self) -> bool {
        self.valid
    }

    pub fn is_inf(&self) -> bool {
        self.inf
    }

    pub fn is_nan(&self) -> bool {
        self.nan
    }

    pub fn sign(&self) -> i8 {
        self.sign
    }

    /// Returns mantissa digits, mantissa length, sign, exponent.
    pub fn raw_parts(&self) -> ([u8; DECIMAL_POSITIONS], usize, i8, i32) {
        (self.mantissa_bytes, self.n, self.sign, self.e)
    }
}

/// Parse BigFloat.
pub fn parse(s: &str) -> ParserState<> {
    let mut parser_state = ParserState::new(s);
    let mut ch = parser_state.next_char();

    // sign
    if let Some(c) = ch {
        match c {
            '+' => { ch = parser_state.next_char() },
            '-' => { parser_state.sign = DECIMAL_SIGN_NEG; ch = parser_state.next_char() },
            _ => {},
        };
    }

    if let Some(c) = ch {
        match c {
            'i' => parse_inf(&mut parser_state),
            'n' => parse_nan(&mut parser_state),
            '.' | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' => 
                parse_num(&mut parser_state),
            _ => {},
        };
    }
    parser_state

}

fn parse_inf(parser_state: &mut ParserState) {
    let n = parser_state.next_char();
    let f = parser_state.next_char();
    if Some('n') == n && Some('f') == f {
        parser_state.inf = true;
        parser_state.valid = true;
    }
}

fn parse_nan(parser_state: &mut ParserState) {
    let a = parser_state.next_char();
    let n = parser_state.next_char();
    if Some('n') == n && Some('a') == a {
        parser_state.nan = true;
        parser_state.valid = true;
    }
}

fn parse_num(parser_state: &mut ParserState) {
    let (int_len, skip_cnt1) = parse_digits(parser_state, true, true);
    if Some('.') == parser_state.cur_char() {
        parser_state.next_char();
    }
    let (frac_len, skip_cnt2) = parse_digits(parser_state, int_len == 0, false);
    if frac_len > 0 || int_len > 0 {
        parser_state.valid = true;
        if Some('e') == parser_state.cur_char() {
            parser_state.next_char();
            parse_exp(parser_state);
        }
        if int_len == 0 {
            parser_state.e -= DECIMAL_POSITIONS as i32 - parser_state.n as i32 + frac_len as i32;
        } else {
            parser_state.e -= DECIMAL_POSITIONS as i32 - int_len as i32;
        }
    } else if skip_cnt1 > 0 || skip_cnt2 > 0 {
        // just zeroes
        parser_state.valid = true;
    }
}

fn parse_digits(parser_state: &mut ParserState, skip_zeroes: bool, int: bool) -> (usize, usize) {
    let mut ch = parser_state.cur_char();
    let mut len = 0;
    let mut skip_cnt = 0;
    if skip_zeroes {
        // skip leading zeroes
        while let Some(c) = ch {
            if c.is_ascii_digit() && c.to_digit(10).unwrap() == 0 {
                skip_cnt += 1;
                if !int {
                    len += 1;   // for fractionl part count length
                }
            } else {
                break;
            }
            ch = parser_state.next_char();
        }
    }
    while let Some(c) = ch {
        if c.is_ascii_digit() {
            if parser_state.n < parser_state.mantissa_bytes.len() {
                parser_state.mantissa_bytes[parser_state.n] = c.to_digit(10).unwrap() as u8;
                parser_state.n += 1;
                len += 1;
            } else {
                break;
            }
        } else {
            break;
        }
        ch = parser_state.next_char();
    }
    if skip_cnt == len {
        // just zeroes
        len = 0;
    }
    (len, skip_cnt)
}

fn parse_exp(parser_state: &mut ParserState) {
    let mut neg = false;
    let mut ch = parser_state.cur_char();
    if let Some(c) = ch {
        match c {
            '+' => { ch = parser_state.next_char(); },
            '-' => { neg = true; ch = parser_state.next_char(); },
            _ => { },
        };
    }
    while let Some(c) = ch {
        if c.is_ascii_digit() {
            if parser_state.e >= i32::MAX/10 {
                break;
            }
            parser_state.e *= 10;
            parser_state.e += c.to_digit(10).unwrap() as i32;
        } else {
            break;
        }
        ch = parser_state.next_char();
    }
    if neg {
        parser_state.e = -parser_state.e;
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    pub fn test_parser() {

        // combinations of possible valid components of a number and expected resulting characteristics.
        let mantissas = ["0.0", "0", ".000", "00.", "00123", "456.", "789.012", ".3456", "0.0078"];
        let expected_mantissas = [
            [0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
            [0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
            [0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
            [0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
            [1,2,3,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
            [4,5,6,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
            [7,8,9,0,1,2,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
            [3,4,5,6,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
            [7,8,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0, ],
        ];
        let expected_mantissa_len = [0, 0, 0, 0, 3, 3, 6, 4, 2];
        let expected_exp_shifts = [0, 0, 0, 0, -37, -37, -37, -40, -42];

        let signs = ["", "+", "-"];
        let expected_signs = [1, 1, -1];

        let exponents = ["", "E", "e", "e123", "e+345", "e-678", "e901", "E+234", "E-567",];
        let expected_exponents = [0, 0, 0, 123, 345, -678, 901, 234, -567];

        let infs = ["inf", "INF", "Inf"];
        let nans = ["nan", "NaN", "NAN"];

        // test numbers.
        for i in 0..signs.len() {
            for j in 0..mantissas.len() {
                for k in 0..exponents.len() {
                    let s = signs[i];
                    let m = mantissas[j];
                    let e = exponents[k];
                    let numstr = (s.to_owned() + m).to_owned() + e;

                    let ps = parse(&numstr);

                    assert!(!ps.is_inf());
                    assert!(!ps.is_nan());
                    assert!(ps.is_valid());

                    let (m, n, s, e) = ps.raw_parts();
                    assert!(s == expected_signs[i]);
                    assert!(m == expected_mantissas[j]);
                    assert!(n == expected_mantissa_len[j]);
                    if expected_mantissa_len[j] > 0 {
                        assert!(e == expected_exponents[k] + expected_exp_shifts[j]);
                    } else {
                        assert!(e == 0);
                    }
                }
            }
        }

        // test inf
        for i in 0..signs.len() {
            for inf in infs {
                let s = signs[i];
                let numstr = s.to_owned() + inf;

                let ps = parse(&numstr);

                assert!(ps.is_inf());
                assert!(ps.sign() == expected_signs[i]);
                assert!(!ps.is_nan());
                assert!(ps.is_valid());
            }
        }

        // test nan
        for nan in nans {
            let ps = parse(nan);
            assert!(!ps.is_inf());
            assert!(ps.is_nan());
            assert!(ps.is_valid());
        }
    }
}