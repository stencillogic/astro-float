//! Parser parses numbers represented in scientific format.

use crate::defs::Exponent;
use crate::defs::Sign;
use crate::defs::EXPONENT_MAX;
use crate::Error;
use crate::Radix;
use crate::EXPONENT_MIN;
use core::str::Chars;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

pub struct ParserState<'a> {
    chars: Chars<'a>,
    cur_ch: Option<char>,
    s_len: usize,
    sign: Sign,
    mantissa_bytes: Vec<u8>,
    e: isize,
    inf: bool,
    nan: bool,
}

impl<'a> ParserState<'a> {
    fn new(s: &'a str) -> Self {
        ParserState {
            chars: s.chars(),
            s_len: s.len(),
            cur_ch: None,
            sign: Sign::Pos,
            mantissa_bytes: Vec::new(),
            e: 0,
            inf: false,
            nan: true,
        }
    }

    // Returns next character of a string in lower case,
    // or None if string end reached.
    fn next_char(&mut self) -> Option<char> {
        self.cur_ch = self.chars.next().map(|c| c.to_ascii_lowercase());
        self.cur_ch
    }

    fn cur_char(&self) -> Option<char> {
        self.cur_ch
    }

    pub fn is_inf(&self) -> bool {
        self.inf
    }

    pub fn is_nan(&self) -> bool {
        self.nan
    }

    pub fn sign(&self) -> Sign {
        self.sign
    }

    /// Returns mantissa digits, mantissa length, sign, exponent.
    pub fn raw_parts(&self) -> (&[u8], Sign, Exponent) {
        (&self.mantissa_bytes, self.sign, self.e as Exponent)
    }
}

/// Parse BigFloat.
pub fn parse(s: &str, rdx: Radix) -> Result<ParserState, Error> {
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
            ('.' | '0' | '1', Radix::Bin) => parse_num(&mut parser_state, rdx)?,
            ('.' | '0'..='7', Radix::Oct) => parse_num(&mut parser_state, rdx)?,
            ('.' | '0'..='9', Radix::Dec) => parse_num(&mut parser_state, rdx)?,
            ('.' | '0'..='9' | 'a'..='f', Radix::Hex) => parse_num(&mut parser_state, rdx)?,
            _ => {}
        };
    }

    Ok(parser_state)
}

fn parse_inf(parser_state: &mut ParserState) {
    let n = parser_state.next_char();
    let f = parser_state.next_char();
    if Some('n') == n && Some('f') == f {
        parser_state.inf = true;
        parser_state.nan = false;
    }
}

fn parse_nan(parser_state: &mut ParserState) {
    let a = parser_state.next_char();
    let n = parser_state.next_char();
    if Some('n') == n && Some('a') == a {
        parser_state.nan = true;
    }
}

fn parse_num(parser_state: &mut ParserState, rdx: Radix) -> Result<(), Error> {
    let (int_len, skip_cnt1) = parse_digits(parser_state, true, true, rdx)?;
    if Some('.') == parser_state.cur_char() {
        parser_state.next_char();
    }
    let (frac_len, _) = parse_digits(parser_state, false, false, rdx)?;
    if frac_len > 0 || int_len > 0 {
        parser_state.nan = false;
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
            parser_state.e = parser_state.e.saturating_add(int_len as isize);
        }

        if parser_state.e < EXPONENT_MIN as isize {
            let mut zero = Vec::new();
            zero.try_reserve_exact(1)?;
            zero.push(0);
            parser_state.mantissa_bytes = zero;
            parser_state.e = 0;
        } else if parser_state.e > EXPONENT_MAX as isize {
            parser_state.inf = true;
        }
    } else if skip_cnt1 > 0 {
        // just zeroes
        parser_state.nan = false;
    }

    Ok(())
}

fn parse_digits(
    parser_state: &mut ParserState,
    skip_zeroes: bool,
    int: bool,
    rdx: Radix,
) -> Result<(usize, usize), Error> {
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

    if ch.is_some() && is_radix_digit(ch.unwrap(), rdx) {
        parser_state
            .mantissa_bytes
            .try_reserve_exact(parser_state.s_len)?;

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
    }

    if !int && skip_cnt == len {
        // just zeroes
        len = 0;
    }

    Ok((len, skip_cnt))
}

fn is_radix_digit(c: char, rdx: Radix) -> bool {
    matches!(
        (rdx, c),
        (Radix::Bin, '0' | '1')
            | (Radix::Oct, '0'..='7')
            | (
                Radix::Dec,
                '0'..='9'
            )
            | (
                Radix::Hex,
                '0'..='9' | 'a'..='f'
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
    let e_thres = EXPONENT_MAX.unsigned_abs().max(EXPONENT_MIN.unsigned_abs()) as isize;
    while let Some(c) = ch {
        if is_radix_digit(c, rdx) {
            if parser_state.e > e_thres {
                break;
            }
            parser_state.e = parser_state.e.saturating_mul(rdx as isize);
            let digit = c.to_digit(rdx as u32).unwrap(); // call to unwrap() is unreachable, because c is surely a digit.
            parser_state.e = parser_state.e.saturating_add(digit as isize);
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
    use {alloc::format, alloc::string::String, alloc::vec};

    #[test]
    pub fn test_parser() {
        // combinations of possible valid components of a number and expected resulting characteristics.
        let mantissas = ["0.0", "0", ".000", "00.", "000123", "456.", "789.012", ".3456", "0.0078"];
        let expected_mantissas = [
            vec![0],
            vec![],
            vec![0, 0, 0],
            vec![],
            vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9, 0, 1, 2],
            vec![3, 4, 5, 6],
            vec![0, 0, 7, 8],
        ];
        let expected_mantissa_len = [1, 0, 3, 0, 3, 3, 6, 4, 4];
        let expected_exp_shifts = [0, 0, 0, 0, 3, 3, 3, 0, 0];

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

                    let ps = parse(&numstr, Radix::Dec).unwrap();

                    assert!(!ps.is_inf());
                    assert!(!ps.is_nan());

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

                let ps = parse(&numstr, Radix::Dec).unwrap();

                assert!(ps.is_inf());
                assert!(ps.sign() == expected_signs[i]);
                assert!(!ps.is_nan());
            }
        }

        // test nan
        for nan in nans {
            let ps = parse(nan, Radix::Dec).unwrap();
            assert!(!ps.is_inf());
            assert!(ps.is_nan());
        }

        // bin
        let ps = parse("101.00101e+1101", Radix::Bin).unwrap();
        let (m, s, e) = ps.raw_parts();
        assert!(m == [1, 0, 1, 0, 0, 1, 0, 1]);
        assert!(s == Sign::Pos);
        assert!(e == 16);

        // oct
        let ps = parse("2670.343e+703", Radix::Oct).unwrap();
        let (m, s, e) = ps.raw_parts();
        assert!(m == [2, 6, 7, 0, 3, 4, 3]);
        assert!(s == Sign::Pos);
        assert!(e == 0o707);

        // hex
        let ps = parse("abc.def09123e_e-1fa", Radix::Hex).unwrap();
        let (m, s, e) = ps.raw_parts();
        assert!(m == [10, 11, 12, 13, 14, 15, 0, 9, 1, 2, 3, 14]);
        assert!(s == Sign::Pos);
        assert!(e == -0x1f7);

        // large exp
        let numstr;
        #[cfg(not(target_arch = "x86"))]
        {
            numstr = "abc.def09123e_e+7FFFFFFF";
        }
        #[cfg(target_arch = "x86")]
        {
            numstr = "abc.def09123e_e+1FFFFFFF";
        }
        let ps = parse(numstr, Radix::Hex).unwrap();
        assert!(ps.is_inf());
        assert!(ps.sign().is_positive());

        let numstr;
        #[cfg(not(target_arch = "x86"))]
        {
            numstr = "-abc.def09123e_e+7FFFFFFF";
        }
        #[cfg(target_arch = "x86")]
        {
            numstr = "-abc.def09123e_e+1FFFFFFF";
        }
        let ps = parse(numstr, Radix::Hex).unwrap();
        assert!(ps.is_inf());
        assert!(!ps.is_nan());
        assert!(ps.sign().is_negative());

        let ps = parse(
            "-abc.def09123e_e+ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            Radix::Hex,
        )
        .unwrap();
        assert!(ps.is_inf());
        assert!(!ps.is_nan());
        assert!(ps.sign().is_negative());

        let numstr = format!("0.0000abc_e+{:X}", EXPONENT_MAX);
        let ps = parse(&numstr, Radix::Hex).unwrap();
        assert!(!ps.is_inf());
        assert!(!ps.is_nan());
        let (m, _s, e) = ps.raw_parts();
        assert_eq!(m, [0, 0, 0, 0, 0xa, 0xb, 0xc]);
        assert_eq!(e, EXPONENT_MAX);

        // small exp
        let numstr = format!(
            "abc.def09123e_e-{:x}",
            (EXPONENT_MIN as i64 - 4).unsigned_abs()
        );
        let ps = parse(&numstr, Radix::Hex).unwrap();
        assert!(!ps.is_inf());
        assert!(!ps.is_nan());
        let (m, _s, e) = ps.raw_parts();
        assert_eq!(m.iter().filter(|&&x| x != 0).count(), 0);
        assert!(e == 0);

        let numstr = format!(
            "0.0000abcdef09123e_e-{:X}",
            (EXPONENT_MIN as i64).unsigned_abs()
        );
        let ps = parse(&numstr, Radix::Hex).unwrap();
        assert!(!ps.is_inf());
        assert!(!ps.is_nan());
        let (m, _s, e) = ps.raw_parts();
        assert_eq!(
            m,
            [0, 0, 0, 0, 0xa, 0xb, 0xc, 0xd, 0xe, 0xf, 0x0, 0x9, 0x1, 0x2, 0x3, 0xe]
        );
        assert_eq!(e, EXPONENT_MIN);

        let ps = parse(
            "abc.def09123e_e-ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            Radix::Hex,
        )
        .unwrap();
        assert!(!ps.is_inf());
        assert!(!ps.is_nan());
        let (m, _s, e) = ps.raw_parts();
        assert_eq!(m.iter().filter(|&&x| x != 0).count(), 0);
        assert!(e == 0);
    }
}
