//! Conversion utilities.

use crate::defs::Sign;
use crate::defs::DoubleWord;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_MAX;
use crate::defs::Exponent;
use crate::defs::Radix;
use crate::defs::Error;
use crate::defs::Word;
use crate::defs::RoundingMode;
use crate::mantissa::Mantissa;
use crate::num::BigFloatNumber;
use crate::common::consts::TWO;
use crate::common::consts::EIGHT;
use crate::common::consts::TEN;
use crate::common::consts::SIXTEEN;
use crate::common::consts::TEN_POW_9;


impl BigFloatNumber {

    /// Converts an array of digits in radix `rdx` to BigFloatNumber with precision `p`.
    /// `digits` represents mantissa and is interpreted as a number smaller than 1 and greater or equal to 1/`rdx`. 
    /// The first element in `digits` is the most significant digit.
    /// `e` is the exponent part of the number, such that the number can be represented as `digits` * `rdx` ^ `e`.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    pub fn convert_from_radix(sign: Sign, digits: &[u8], e: Exponent, rdx: Radix, p: usize, rm: RoundingMode) -> Result<Self, Error> {
        match rdx {
            Radix::Bin => Self::conv_from_binary(sign, digits, e, p, rm),
            Radix::Oct => Self::conv_from_commensurable(sign, digits, e, 3, p, rm),
            Radix::Dec => Self::conv_from_num_dec(sign, digits, e, p, rm),
            Radix::Hex => Self::conv_from_commensurable(sign, digits, e, 4, p, rm),
        }
    }

    fn conv_from_binary(sign: Sign, digits: &[u8], e: Exponent, p: usize, rm: RoundingMode) -> Result<Self, Error> {

        debug_assert!(digits[0] != 0);

        let mut mantissa = Vec::new();
        let mut d = 0;
        let mut shift = 0;

        for v in digits.iter().rev() {

            d |= (*v as Word) << shift;
            shift += 1;

            if shift == WORD_BIT_SIZE {
                mantissa.push(d);
                shift = 0;
                d = 0;
            }
        }

        let mut ret = BigFloatNumber::from_raw_parts(&mantissa, digits.len(), sign, e)?;

        ret.set_precision(p, rm)?;

        Ok(ret)
    }

    fn conv_from_commensurable(sign: Sign, digits: &[u8], e: Exponent, shift: usize, p: usize, rm: RoundingMode) -> Result<Self, Error> {

        let mut mantissa = Vec::new();
        let mut done = shift;
        let mut d = 0;

        // exponent shift
        let mut e_shift = 0;
        for v in digits {
            let mut v = *v;
            if v == 0 {
                e_shift -= shift as Exponent;
            } else {
                let significant_bit = 1 << (shift - 1);
                while v & significant_bit == 0 {
                    e_shift -= 1;
                    v <<= 1;
                }
                break;
            }
        }

        // mantissa
        let mut iter = digits.iter().rev();
        for v in iter.by_ref() {
            if *v != 0 {
                d = *v as Word;
                break;
            }
        }

        if d > 0 {

            while d & 1 == 0 {
                d >>= 1;
                done -= 1;
            }

            for v in iter {

                d |= (*v as Word) << done;
                done += shift;

                if done >= WORD_BIT_SIZE {
                    mantissa.push(d);
                    done -= WORD_BIT_SIZE;
                    d = (*v as Word) >> (shift - done);
                }
            }

            if d > 0 {
                mantissa.push(d);
            }
        }

        let mut m = Mantissa::from_raw_parts(&mantissa, mantissa.len() * WORD_BIT_SIZE)?;
        if let Some(norm) = m.find_one_from(0) {
            m.shift_left(norm);
        }
        let mut ret = BigFloatNumber {
            m,
            s: sign,
            e: e*shift as Exponent + e_shift,
        };

        ret.set_precision(p, rm)?;

        Ok(ret)
    }

    fn conv_from_num_dec(sign: Sign, digits: &[u8], e: Exponent, p: usize, rm: RoundingMode) -> Result<Self, Error> {

        // mantissa part
        let pf = digits.len() * 3321928095 / 1000000000;
        let mut word: Word = 0;
        let mut f = Self::new(pf + 2)?;

        let mut i = 0;
        for d in digits {

            let d = *d as Word;

            word *= 10;
            word += d;

            i += 1;
            if i == 9 {
                i = 0;

                let d2 = Self::from_word(word, 1)?;
                f = f.mul(&TEN_POW_9, RoundingMode::None)?;
                f = f.add(&d2, RoundingMode::None)?;

                word = 0;
            }
        }

        if i > 0 {
            let mut ten_pow = 10;
            i -= 1;
            while i > 0 {
                ten_pow *= 10;
                i -= 1;
            }
            let ten_pow = Self::from_word(ten_pow, 1)?;
            let d2 = Self::from_word(word, 1)?;
            f = f.mul(&ten_pow, RoundingMode::None)?;
            f = f.add(&d2, RoundingMode::None)?;
        }

        // exponent part
        let n = e as isize - digits.len() as isize;

        let fpn = Self::from_word(10, pf.max(p) + 2)?
            .powi(n.unsigned_abs() as usize, RoundingMode::None)?;

        let mut ret = if n < 0 {
            f.div(&fpn, RoundingMode::None)
        } else {
            f.mul(&fpn, RoundingMode::None)
        }?;

        ret.set_sign(sign);
        ret.set_precision(p, rm)?;

        Ok(ret)
    }

    /// Converts `self` to radix `rdx` using rounding mode `rm`.
    /// The function returns sign, mantissa digits in radix `rdx`, and exponent such that the converted number 
    /// can be represented as `mantissa digits` * `rdx` ^ `exponent`.
    /// The first element in mantissa is the most significant digit.
    /// 
    /// ## Errors
    /// 
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    pub fn convert_to_radix(&self, rdx: Radix, rm: RoundingMode) -> Result<(Sign, Vec<u8>, Exponent), Error> {
        match rdx {
            Radix::Bin => self.conv_to_binary(),
            Radix::Oct => self.conv_to_commensurable(3),
            Radix::Dec => self.conv_to_dec(rm),
            Radix::Hex => self.conv_to_commensurable(4),
        }
    }

    fn conv_to_dec(&self, rm: RoundingMode) -> Result<(Sign, Vec<u8>, Exponent), Error> {

        // input: rdx = 10, self = m*2^e, 0.5 <= m < 1, 
        // let self = m*2^e * rdx^n / rdx^n, where n = floor(e * log_rdx(2))
        // let f = m / rdx^n,
        // then resulting number is F = f * rdx^n

        let n = self.get_exponent().unsigned_abs() as usize * 3010299957 / 10000000000;
        let l = self.get_mantissa_max_bit_len() as usize * 3010299957 / 10000000000 + 1;

        let (digits, e_shift) = if n == 0 {

            self.print_mantissa(l, Radix::Dec, rm)

        } else {

            let rdx = Self::number_for_radix(Radix::Dec)?;
            let mut rdx_p = rdx.clone()?;
            let max_p = self.get_mantissa_max_bit_len().min(self.get_exponent().unsigned_abs() as usize)
                 + core::mem::size_of::<Exponent>() + 2;
            rdx_p.set_precision(max_p, RoundingMode::None)?;

            let mut f = if n >= 646456993 { // avoid powi overflow

                let d = rdx_p.powi(n - 1, rm)?;

                if self.get_exponent() < 0 {
                    self.mul(&d, RoundingMode::None)?.mul(rdx, RoundingMode::None)
                } else {
                    self.div(&d, RoundingMode::None)?.div(rdx, RoundingMode::None)
                }

            } else {

                let d = rdx_p.powi(n, rm)?;

                if self.get_exponent() < 0 {
                    self.mul(&d, RoundingMode::None)
                } else {
                    self.div(&d, RoundingMode::None)
                }

            }?;

            f.set_precision(self.get_mantissa_max_bit_len(), rm)?;

            f.print_mantissa(l, Radix::Dec, rm)
        }?;

        let e = (n as Exponent) * self.get_exponent().signum() + e_shift;

        Ok((self.get_sign(), digits, e))
    }

    /// Conversion for radixes of power of 2.
    fn conv_to_commensurable(&self, shift: usize) -> Result<(Sign, Vec<u8>, Exponent), Error> {

        let mut e = self.get_exponent();
        let mut e_shift = e.unsigned_abs() as usize % shift;
        e /= shift as Exponent;
        if e_shift != 0 {
            if self.get_exponent() > 0 {
                e_shift = shift - e_shift;
                e += 1;
            }
        }

        let mut ret = Vec::new();

        let mask = (WORD_MAX >> (WORD_BIT_SIZE - shift)) as DoubleWord;
        let mut iter = self.get_mantissa_digits().iter().rev();
        let mut done = WORD_BIT_SIZE - shift + e_shift;
        let mut d = *iter.next().unwrap() as DoubleWord;

        loop {

            let digit = ((d >> done) & mask) as u8;

            ret.push(digit);

            if done < shift {

                d <<= WORD_BIT_SIZE;

                if let Some(v) = iter.next() {
                    d |= *v as DoubleWord;
                } else {
                    break;
                }

                done += WORD_BIT_SIZE;
            }

            done -= shift;
        }

        if done > 0 {

            if done < shift {
                done += WORD_BIT_SIZE - shift;
            }

            let digit = ((d >> done) & mask) as u8;
            ret.push(digit);
        }

        Ok((self.get_sign(), ret, e))
    }

    fn conv_to_binary(&self) -> Result<(Sign, Vec<u8>, Exponent), Error> {

        let mut ret = Vec::new();

        for v in self.get_mantissa_digits().iter().rev() {
            for i in (0..WORD_BIT_SIZE).rev() {
                ret.push(((v >> i) & 1) as u8);
            }
        }

        Ok((self.get_sign(), ret, self.get_exponent()))
    }

    fn print_mantissa(&self, l: usize, rdx: Radix, rm: RoundingMode) -> Result<(Vec<u8>, Exponent), Error> {

        let mut ret = Vec::new();
        let mut e_shift = 0;

        if self.is_zero() {

            ret.push(0);

        } else {

            let mut r = self.clone()?;
            r.set_sign(Sign::Pos);
            let rdx_num = Self::number_for_radix(rdx)?;
            let rdx_word = Self::word_for_radix(rdx);
            let mut word;

            let d = r.mul(rdx_num, rm).unwrap();
            r = d.fract()?;
            word = d.get_int_as_word();
            if word == 0 {
                e_shift = -1;
                let d = r.mul(rdx_num, rm).unwrap();
                r = d.fract()?;
                word = d.get_int_as_word();
            } else if word >= rdx_word {
                e_shift = 1;

                ret.push((word / rdx_word) as u8);
                ret.push((word % rdx_word) as u8);

                let d = r.mul(rdx_num, rm).unwrap();
                r = d.fract()?;
                word = d.get_int_as_word();
            }

            for _ in 0..l {

                ret.push(word as u8);

                let d = r.mul(rdx_num, rm).unwrap();
                r = d.fract()?;
                word = d.get_int_as_word();
            }

            if !r.round(0, RoundingMode::ToEven).unwrap().is_zero() {

                word += 1;

                if word == rdx_word {

                    ret.push(0);

                    let mut i = ret.len() - 2;
                    while i > 0 && ret[i] + 1 == rdx_word as u8 {
                        ret[i] = 0;
                        i -= 1;
                    }
                    ret[i] += 1;

                } else {

                    ret.push(word as u8);
                }

            } else {

                ret.push(word as u8);

            }
        }

        // strip zeroes
        let nzeroes = ret.iter().rev().take_while(|x| { **x == 0 }).count();
        ret.truncate(ret.len() - nzeroes);

        Ok((ret, e_shift))
    }

    fn word_for_radix(rdx: Radix) -> Word {
        match rdx {
            Radix::Bin => 2,
            Radix::Oct => 8,
            Radix::Dec => 10,
            Radix::Hex => 16,
        }
    }

    fn number_for_radix(rdx: Radix) -> Result<&'static Self, Error> {
        Ok(match rdx {
            Radix::Bin => &TWO,
            Radix::Oct => &EIGHT,
            Radix::Dec => &TEN,
            Radix::Hex => &SIXTEEN,
        })
    }
}


#[cfg(test)]
mod tests {

    use rand::random;
    use crate::defs::{Sign, EXPONENT_MIN, EXPONENT_MAX};
    use super::*;
    use crate::common::consts::ONE;

    #[test]
    fn test_conv() {

        let n = BigFloatNumber::from_f64(64, 0.031256789f64).unwrap();

        let (s, m, e) = n.convert_to_radix(Radix::Bin, RoundingMode::None).unwrap();

        assert!(m == [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 
                      1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert!(s == Sign::Pos);
        assert!(e == -4);

        let g = BigFloatNumber::convert_from_radix(s, &m, e, Radix::Bin, 160, RoundingMode::ToEven).unwrap();
        let f = g.to_f64();

        assert!(f == 0.031256789f64);

        #[cfg(target_arch = "x86")] {
            let n = BigFloatNumber::from_raw_parts(&[2576980377, 2576980377, 2576980377], 96, Sign::Pos, -1).unwrap();
            let (s, m, e) = n.convert_to_radix(Radix::Oct, RoundingMode::None).unwrap();
            let g = BigFloatNumber::convert_from_radix(s, &m, e, Radix::Oct, 160, RoundingMode::ToEven).unwrap();

            assert!(n.cmp(&g) == 0);
        
            let n = BigFloatNumber::from_raw_parts(&[2576980377, 2576980377, 2576980377], 96, Sign::Pos, -0).unwrap();
            let (s, m, e) = n.convert_to_radix(Radix::Dec, RoundingMode::None).unwrap();

            assert!(m == [6]);
            assert!(s == Sign::Pos);
            assert!(e == 0);
        
            let g = BigFloatNumber::convert_from_radix(s, &m, e, Radix::Dec, 96, RoundingMode::None).unwrap();
            assert!(g.cmp(&n) == 0);
        }

        #[cfg(target_arch = "x86_64")] {
            let n = BigFloatNumber::from_raw_parts(&[0x9999999999999999, 0x9999999999999999, 0x9999999999999999], 192, Sign::Pos, -1).unwrap();
            let (s, m, e) = n.convert_to_radix(Radix::Oct, RoundingMode::None).unwrap();
            let g = BigFloatNumber::convert_from_radix(s, &m, e, Radix::Oct, 192, RoundingMode::ToEven).unwrap();

            assert!(n.cmp(&g) == 0);
        
            let n = BigFloatNumber::from_raw_parts(&[0x9999999999999999, 0x9999999999999999, 0x9999999999999999], 192, Sign::Pos, -0).unwrap();
            let (s, m, e) = n.convert_to_radix(Radix::Dec, RoundingMode::ToEven).unwrap();

            //println!("{:?}", m);
            assert!(m == [5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 8, 8]);
            assert!(s == Sign::Pos);
            assert!(e == 0);

            let g = BigFloatNumber::convert_from_radix(s, &m, e, Radix::Dec, 192, RoundingMode::ToEven).unwrap();
            //println!("{:?}", g);
            //println!("{:?}", n);
            assert!(g.cmp(&n) == 0);
        }

        /* let n = BigFloatNumber::from_raw_parts(&[3585894214], 32, Sign::Pos, -24).unwrap();
        let (s, m , e) = n.convert_to_radix(Radix::Dec, RoundingMode::ToEven).unwrap();
        
        let g = BigFloatNumber::convert_from_radix(s, &m, e, Radix::Dec, 32, RoundingMode::ToEven).unwrap();
        let (s, m , e) = g.convert_to_radix(Radix::Dec, RoundingMode::ToEven).unwrap();
        //println!("{:?} {}", (s, &m, e), n.to_f64());
        return; */

        let prec = 320;
        let mut eps = ONE.clone().unwrap();

        for _ in 0..10000 {
            let n = BigFloatNumber::random_normal(prec, EXPONENT_MIN, EXPONENT_MAX).unwrap();
            let rdx = random_radix();

            let (s1, m1, e1) = n.convert_to_radix(rdx, RoundingMode::ToEven).unwrap();
            let g = BigFloatNumber::convert_from_radix(s1, &m1, e1, rdx, prec, RoundingMode::ToEven).unwrap();

            //println!("\n{:?}", rdx);
            //println!("{:?} {:?} {}", s1, m1, e1);
            //println!("{:?}\n{:?}", n, g);

            eps.set_exponent(n.get_exponent() - prec as Exponent + 4);
            if rdx == Radix::Dec {
                assert!(n.sub(&g, RoundingMode::None).unwrap().abs().unwrap().cmp(&eps) <= 0);
            } else {
                assert!(n.cmp(&g) == 0);
            }
        }
    }

    fn random_radix() -> Radix {
        match random::<usize>() % 4 {
            0 => Radix::Bin,
            1 => Radix::Oct,
            2 => Radix::Dec,
            3 => Radix::Hex,
            _ => unreachable!(),
        }
    }
}
