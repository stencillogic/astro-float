//! Parser parses numbers represented in scientific format.

use crate::defs::Exponent;
use crate::defs::Sign;
use crate::defs::EXPONENT_MAX;
use crate::Radix;

#[cfg(feature = "std")]
use std::str::Chars;

#[cfg(not(feature = "std"))]
use {alloc::vec::Vec, core::str::Chars};

pub struct ParserState<'a> {
    chars: Chars<'a>,
    cur_ch: Option<char>,
    sign: Sign,
    mantissa_bytes: Vec<u8>,
    e: Exponent,
    inf: bool,
    nan: bool,
    valid: bool,
}

impl<'a> ParserState<'a> {
    fn new(s: &'a str) -> Self {
        ParserState {
            chars: s.chars(),
            cur_ch: None,
            sign: Sign::Pos,
            mantissa_bytes: Vec::new(),
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

    #[allow(dead_code)]
    pub fn is_inf(&self) -> bool {
        self.inf
    }

    #[allow(dead_code)]
    pub fn is_nan(&self) -> bool {
        self.nan
    }

    #[allow(dead_code)]
    pub fn sign(&self) -> Sign {
        self.sign
    }

    /// Returns mantissa digits, mantissa length, sign, exponent.
    pub fn raw_parts(&self) -> (&[u8], Sign, Exponent) {
        (&self.mantissa_bytes, self.sign, self.e)
    }
}

/// Parse BigFloat.
pub fn parse(s: &str, rdx: Radix) -> ParserState {
    let mut parser_state = ParserState::new(s);
    let mut ch = parser_state.next_char();

    // sign
    if let Some(c) = ch {
        match c {
            '+' => ch = parser_state.next_char(),
            '-' => {
                parser_state.sign = Sign::Neg;
                ch = parser_state.next_char()
            }
            _ => {}
        };
    }

    if let Some(c) = ch {
        match (c, rdx) {
            ('i', _) => parse_inf(&mut parser_state),
            ('n', _) => parse_nan(&mut parser_state),
            ('.' | '0' | '1', Radix::Bin) => parse_num(&mut parser_state, rdx),
            ('.' | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7', Radix::Oct) => {
                parse_num(&mut parser_state, rdx)
            }
            ('.' | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9', Radix::Dec) => {
                parse_num(&mut parser_state, rdx)
            }
            (
                '.' | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' | 'a' | 'b' | 'c'
                | 'd' | 'e' | 'f',
                Radix::Hex,
            ) => parse_num(&mut parser_state, rdx),
            _ => {}
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

fn parse_num(parser_state: &mut ParserState, rdx: Radix) {
    let (int_len, skip_cnt1) = parse_digits(parser_state, true, true, rdx);
    if Some('.') == parser_state.cur_char() {
        parser_state.next_char();
    }
    let (frac_len, skip_cnt2) = parse_digits(parser_state, int_len == 0, false, rdx);
    if frac_len > 0 || int_len > 0 {
        parser_state.valid = true;
        if rdx == Radix::Hex {
            if Some('_') == parser_state.cur_char() {
                parser_state.next_char();
                if Some('e') == parser_state.cur_char() {
                    parser_state.next_char();
                    parse_exp(parser_state, rdx);
                }
            }
        } else if Some('e') == parser_state.cur_char() {
            parser_state.next_char();
            parse_exp(parser_state, rdx);
        }
        if int_len != 0 {
            parser_state.e += int_len as Exponent;
        } else {
            parser_state.e -= skip_cnt2 as Exponent;
        }
    } else if skip_cnt1 > 0 || skip_cnt2 > 0 {
        // just zeroes
        parser_state.valid = true;
    }
}

fn parse_digits(
    parser_state: &mut ParserState,
    skip_zeroes: bool,
    int: bool,
    rdx: Radix,
) -> (usize, usize) {
    let mut ch = parser_state.cur_char();
    let mut len = 0;
    let mut skip_cnt = 0;
    if skip_zeroes {
        // skip leading zeroes
        while let Some(c) = ch {
            if is_radix_digit(c, rdx) && c.to_digit(rdx as u32).unwrap() == 0 {
                // call to unwrap() is unreachable, because c is surely a digit.
                skip_cnt += 1;
                if !int {
                    len += 1; // for fractional part count length
                }
            } else {
                break;
            }
            ch = parser_state.next_char();
        }
    }
    while let Some(c) = ch {
        if is_radix_digit(c, rdx) {
            parser_state
                .mantissa_bytes
                .push(c.to_digit(rdx as u32).unwrap() as u8); // call to unwrap() is unreachable, because c is surely a digit.
            len += 1;
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

fn is_radix_digit(c: char, rdx: Radix) -> bool {
    matches!(
        (rdx, c),
        (Radix::Bin, '0' | '1')
            | (Radix::Oct, '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7')
            | (
                Radix::Dec,
                '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
            )
            | (
                Radix::Hex,
                '0' | '1'
                    | '2'
                    | '3'
                    | '4'
                    | '5'
                    | '6'
                    | '7'
                    | '8'
                    | '9'
                    | 'a'
                    | 'b'
                    | 'c'
                    | 'd'
                    | 'e'
                    | 'f'
            )
    )
}

fn parse_exp(parser_state: &mut ParserState, rdx: Radix) {
    let mut neg = false;
    let mut ch = parser_state.cur_char();
    if let Some(c) = ch {
        match c {
            '+' => {
                ch = parser_state.next_char();
            }
            '-' => {
                neg = true;
                ch = parser_state.next_char();
            }
            _ => {}
        };
    }
    while let Some(c) = ch {
        if is_radix_digit(c, rdx) {
            if parser_state.e >= EXPONENT_MAX / 10 {
                break;
            }
            parser_state.e *= rdx as Exponent;
            parser_state.e += c.to_digit(rdx as u32).unwrap() as Exponent; // call to unwrap() is unreachable, because c is surely a digit.
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

    #[cfg(not(feature = "std"))]
    use {alloc::string::String, alloc::vec};

    #[test]
    pub fn test_parser() {
        // combinations of possible valid components of a number and expected resulting characteristics.
        let mantissas = ["0.0", "0", ".000", "00.", "00123", "456.", "789.012", ".3456", "0.0078"];
        let expected_mantissas = [
            vec![],
            vec![],
            vec![],
            vec![],
            vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9, 0, 1, 2],
            vec![3, 4, 5, 6],
            vec![7, 8],
        ];
        let expected_mantissa_len = [0, 0, 0, 0, 3, 3, 6, 4, 2];
        let expected_exp_shifts = [0, 0, 0, 0, 3, 3, 3, 0, -2];

        let signs = ["", "+", "-"];
        let expected_signs = [Sign::Pos, Sign::Pos, Sign::Neg];

        let exponents = ["", "E", "e", "e123", "e+345", "e-678", "e901", "E+234", "E-567"];
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
                    let numstr = String::from(s) + m + e;

                    let ps = parse(&numstr, Radix::Dec);

                    assert!(!ps.is_inf());
                    assert!(!ps.is_nan());
                    assert!(ps.is_valid());

                    let (m, s, e) = ps.raw_parts();
                    assert!(s == expected_signs[i]);
                    assert!(m == expected_mantissas[j]);
                    assert!(m.len() == expected_mantissa_len[j]);
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
                let numstr = String::from(s) + inf;

                let ps = parse(&numstr, Radix::Dec);

                assert!(ps.is_inf());
                assert!(ps.sign() == expected_signs[i]);
                assert!(!ps.is_nan());
                assert!(ps.is_valid());
            }
        }

        // test nan
        for nan in nans {
            let ps = parse(nan, Radix::Dec);
            assert!(!ps.is_inf());
            assert!(ps.is_nan());
            assert!(ps.is_valid());
        }

        // bin
        let ps = parse("101.00101e+1101", Radix::Bin);
        let (m, s, e) = ps.raw_parts();
        assert!(m == [1, 0, 1, 0, 0, 1, 0, 1]);
        assert!(s == Sign::Pos);
        assert!(e == 16);

        // oct
        let ps = parse("2670.343e+703", Radix::Oct);
        let (m, s, e) = ps.raw_parts();
        assert!(m == [2, 6, 7, 0, 3, 4, 3]);
        assert!(s == Sign::Pos);
        assert!(e == 0o707);

        // hex
        let ps = parse("abc.def09123e_e-1fa", Radix::Hex);
        let (m, s, e) = ps.raw_parts();
        assert!(m == [10, 11, 12, 13, 14, 15, 0, 9, 1, 2, 3, 14]);
        assert!(s == Sign::Pos);
        assert!(e == -0x1f7);
    }
}
