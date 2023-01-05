//! Conversion utilities.

use crate::common::consts::EIGHT;
use crate::common::consts::SIXTEEN;
use crate::common::consts::TEN;
use crate::common::consts::TEN_POW_9;
use crate::common::consts::TWO;
use crate::common::util::round_p;
use crate::defs::DoubleWord;
use crate::defs::Error;
use crate::defs::Exponent;
use crate::defs::Radix;
use crate::defs::RoundingMode;
use crate::defs::Sign;
use crate::defs::Word;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_MAX;
use crate::mantissa::Mantissa;
use crate::num::BigFloatNumber;
use crate::EXPONENT_MAX;
use crate::EXPONENT_MIN;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

impl BigFloatNumber {
    /// Converts an array of digits in radix `rdx` to BigFloatNumber with precision `p`.
    /// `digits` represents mantissa and is interpreted as a number smaller than 1 and greater or equal to 1/`rdx`.
    /// The first element in `digits` is the most significant digit.
    /// `e` is the exponent part of the number, such that the number can be represented as `digits` * `rdx` ^ `e`.
    /// Precision is rounded upwards to the word size.
    ///
    /// ## Examples
    ///
    /// Code below converts `-0.1234567₈ × 10₈^3₈` given in radix 8 to BigFloatNumber.
    ///
    /// ``` rust
    /// use astro_float::{BigFloatNumber, Sign, RoundingMode, Radix};
    ///
    /// let g = BigFloatNumber::convert_from_radix(
    ///     Sign::Neg,
    ///     &[1, 2, 3, 4, 5, 6, 7, 0],
    ///     3,
    ///     Radix::Oct,
    ///     64,
    ///     RoundingMode::None).unwrap();
    ///
    /// let n = BigFloatNumber::from_f64(64, -83.591552734375).unwrap();
    ///
    /// assert!(n.cmp(&g) == 0);
    /// ```
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - InvalidArgument: the precision is incorrect, or `digits` contains unacceptable digits for given radix.
    pub fn convert_from_radix(
        sign: Sign,
        digits: &[u8],
        e: Exponent,
        rdx: Radix,
        p: usize,
        rm: RoundingMode,
    ) -> Result<Self, Error> {
        let p = round_p(p);
        Self::p_assertion(p)?;

        if p == 0 {
            return Self::new(0);
        }

        match rdx {
            Radix::Bin => Self::conv_from_binary(sign, digits, e, p, rm),
            Radix::Oct => Self::conv_from_commensurable(sign, digits, e, 3, p, rm),
            Radix::Dec => Self::conv_from_num_dec(sign, digits, e, p, rm),
            Radix::Hex => Self::conv_from_commensurable(sign, digits, e, 4, p, rm),
        }
    }

    fn conv_from_binary(
        sign: Sign,
        digits: &[u8],
        e: Exponent,
        p: usize,
        rm: RoundingMode,
    ) -> Result<Self, Error> {
        if digits.is_empty() {
            return Self::new(p);
        }

        let mut mantissa = Vec::new();
        let mut d = 0;
        let mut shift = digits.len() % WORD_BIT_SIZE;
        if shift != 0 {
            shift = WORD_BIT_SIZE - shift;
        }

        for v in digits.iter().rev() {
            if *v > 1 {
                return Err(Error::InvalidArgument);
            }

            d |= (*v as Word) << shift;
            shift += 1;

            if shift == WORD_BIT_SIZE {
                mantissa.push(d);
                shift = 0;
                d = 0;
            }
        }

        if shift > 0 {
            mantissa.push(d);
        }

        let mut ret = BigFloatNumber::from_words(&mantissa, sign, e)?;

        ret.set_precision(p, rm)?;

        Ok(ret)
    }

    // radix is power of 2.
    fn conv_from_commensurable(
        sign: Sign,
        digits: &[u8],
        e: Exponent,
        shift: usize,
        p: usize,
        rm: RoundingMode,
    ) -> Result<Self, Error> {
        let mut m = Mantissa::new(p + WORD_BIT_SIZE)?;

        let significant_bit = 1 << (shift - 1);
        let base = 1 << shift;

        // exponent shift
        let mut e_shift = 0;
        let mut zeroes = 0;
        let mut first_shift = 0;
        for v in digits {
            let mut v = *v;

            if v == 0 {
                e_shift -= shift as isize;
                zeroes += 1;
            } else {
                if v >= base {
                    return Err(Error::InvalidArgument);
                }

                while v & significant_bit == 0 {
                    e_shift -= 1;
                    v <<= 1;
                    first_shift += 1;
                }
                break;
            }
        }

        if zeroes == digits.len() {
            // mantissa is zero
            m.set_length(p)?;

            Ok(BigFloatNumber { m, e: 0, s: sign })
        } else {
            // exponent
            let mut e = e as isize * shift as isize + e_shift;

            if e > EXPONENT_MAX as isize {
                return Err(Error::ExponentOverflow(sign));
            }

            // check for subnormality
            let mut start_bit = 0;
            if e < EXPONENT_MIN as isize {
                if (e + m.max_bit_len() as isize) <= EXPONENT_MIN as isize {
                    m.set_length(p)?;
                    return Ok(BigFloatNumber { m, e: 0, s: sign });
                } else {
                    start_bit = (EXPONENT_MIN as isize - e as isize) as usize;
                    e = EXPONENT_MIN as isize;
                }
            }

            // fill mantissa
            let mut filled = start_bit % WORD_BIT_SIZE + shift - first_shift;
            let mut dst = m
                .get_digits_mut()
                .iter_mut()
                .rev()
                .skip(start_bit / WORD_BIT_SIZE);
            let mut d = 0;
            'outer: for &v in digits.iter().skip(zeroes) {
                if v >= base {
                    return Err(Error::InvalidArgument);
                }

                if filled <= WORD_BIT_SIZE {
                    d |= (v as Word) << (WORD_BIT_SIZE - filled);
                } else {
                    d |= (v as Word) >> (filled - WORD_BIT_SIZE);

                    if let Some(w) = dst.next() {
                        *w = d;
                        filled -= WORD_BIT_SIZE;
                        d = if filled > 0 { (v as Word) << (WORD_BIT_SIZE - filled) } else { 0 };
                    } else {
                        break 'outer;
                    }
                }
                filled += shift;
            }

            if d > 0 {
                if let Some(w) = dst.next() {
                    *w = d;
                }
            }

            m.set_bit_len(m.max_bit_len() - start_bit);
            m.round_mantissa(WORD_BIT_SIZE, rm, sign.is_positive());
            m.set_length(p)?;

            Ok(BigFloatNumber {
                m,
                e: e as Exponent,
                s: sign,
            })
        }
    }

    fn conv_from_num_dec(
        sign: Sign,
        digits: &[u8],
        e: Exponent,
        p: usize,
        rm: RoundingMode,
    ) -> Result<Self, Error> {
        // mantissa part
        let pf = digits.len() * 3321928095 / 1000000000;
        let mut word: Word = 0;
        let mut f = Self::new(pf + 2)?;

        let leadzeroes = digits.iter().take_while(|&&x| x == 0).count();

        // TODO: divide and conquer can be used to build the mantissa.
        let mut i = 0;
        for &d in digits.iter().skip(leadzeroes) {
            if d > 9 {
                return Err(Error::InvalidArgument);
            }

            word *= 10;
            word += d as Word;

            i += 1;
            if i == 9 {
                i = 0;

                let d2 = Self::from_word(word, 1)?;
                f = f.mul(&TEN_POW_9, f.get_mantissa_max_bit_len(), RoundingMode::None)?;
                f = f.add(&d2, f.get_mantissa_max_bit_len(), RoundingMode::None)?;

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
            f = f.mul(&ten_pow, f.get_mantissa_max_bit_len(), RoundingMode::None)?;
            f = f.add(&d2, f.get_mantissa_max_bit_len(), RoundingMode::None)?;
        }

        // exponent part
        let n = e as isize - digits.len() as isize;

        let nmax = Exponent::MAX as usize * 301029995 / 1000000000;

        let ten = Self::from_word(10, 4)?;

        let mut nabs = n.unsigned_abs() as usize;
        if nabs > nmax {
            let fpnmax = ten.powi(nmax, pf.max(p), RoundingMode::None)?;

            while nabs > nmax {
                f = if n < 0 {
                    f.div(&fpnmax, f.get_mantissa_max_bit_len(), RoundingMode::None)
                } else {
                    f.mul(&fpnmax, f.get_mantissa_max_bit_len(), RoundingMode::None)
                }?;
                nabs -= nmax;
            }
        };

        if nabs > 0 {
            let fpn = ten.powi(nabs, pf.max(p) + WORD_BIT_SIZE, RoundingMode::None)?;

            f = if n < 0 {
                f.div(&fpn, f.get_mantissa_max_bit_len(), RoundingMode::None)
            } else {
                f.mul(&fpn, f.get_mantissa_max_bit_len(), RoundingMode::None)
            }?;
        }

        f.set_sign(sign);
        f.set_precision(p, rm)?;

        Ok(f)
    }

    /// Converts `self` to radix `rdx` using rounding mode `rm`.
    /// The function returns sign, mantissa digits in radix `rdx`, and exponent such that the converted number
    /// can be represented as `mantissa digits` * `rdx` ^ `exponent`.
    /// The first element in the mantissa is the most significant digit.
    ///
    /// ## Examples
    ///
    /// ``` rust
    /// use astro_float::{BigFloatNumber, Sign, RoundingMode, Radix};
    ///
    /// let n = BigFloatNumber::from_f64(64, 0.00012345678f64).unwrap();
    ///
    /// let (s, m, e) = n.convert_to_radix(Radix::Dec, RoundingMode::None).unwrap();
    ///
    /// assert_eq!(s, Sign::Pos);
    /// assert_eq!(m, [1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 4, 2]);
    /// assert_eq!(e, -3);
    /// ```
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    pub fn convert_to_radix(
        &self,
        rdx: Radix,
        rm: RoundingMode,
    ) -> Result<(Sign, Vec<u8>, Exponent), Error> {
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
            self.conv_mantissa(l, Radix::Dec, rm)
        } else {
            let rdx = Self::number_for_radix(Radix::Dec)?;
            let mut rdx_p = rdx.clone()?;
            let max_p = self
                .get_mantissa_max_bit_len()
                .min(self.get_exponent().unsigned_abs() as usize)
                + core::mem::size_of::<Exponent>()
                + 2;
            rdx_p.set_precision(max_p, RoundingMode::None)?;

            let mut f = if n >= 646456993 {
                // avoid powi overflow

                let d = rdx_p.powi(n - 1, max_p, rm)?;

                if self.get_exponent() < 0 {
                    self.mul(&d, self.get_mantissa_max_bit_len(), RoundingMode::None)?
                        .mul(rdx, self.get_mantissa_max_bit_len(), RoundingMode::None)
                } else {
                    self.div(&d, self.get_mantissa_max_bit_len(), RoundingMode::None)?
                        .div(rdx, self.get_mantissa_max_bit_len(), RoundingMode::None)
                }
            } else {
                let d = rdx_p.powi(n, max_p, rm)?;

                if self.get_exponent() < 0 {
                    self.mul(&d, self.get_mantissa_max_bit_len(), RoundingMode::None)
                } else {
                    self.div(&d, self.get_mantissa_max_bit_len(), RoundingMode::None)
                }
            }?;

            f.set_precision(self.get_mantissa_max_bit_len(), rm)?;

            f.conv_mantissa(l, Radix::Dec, rm)
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
        let mut d = *iter.next().unwrap() as DoubleWord; // iter is never empty.

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

    fn conv_mantissa(
        &self,
        l: usize,
        rdx: Radix,
        rm: RoundingMode,
    ) -> Result<(Vec<u8>, Exponent), Error> {
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

            let d = r.mul(rdx_num, r.get_mantissa_max_bit_len(), rm)?;
            r = d.fract()?;
            word = d.get_int_as_word();
            if word == 0 {
                e_shift = -1;
                let d = r.mul(rdx_num, r.get_mantissa_max_bit_len(), rm)?;
                r = d.fract()?;
                word = d.get_int_as_word();
            } else if word >= rdx_word {
                e_shift = 1;

                ret.push((word / rdx_word) as u8);
                ret.push((word % rdx_word) as u8);

                let d = r.mul(rdx_num, r.get_mantissa_max_bit_len(), rm)?;
                r = d.fract()?;
                word = d.get_int_as_word();
            }

            for _ in 0..l {
                ret.push(word as u8);

                let d = r.mul(rdx_num, r.get_mantissa_max_bit_len(), rm)?;
                r = d.fract()?;
                word = d.get_int_as_word();
            }

            if !r.round(0, RoundingMode::ToEven)?.is_zero() {
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
        let nzeroes = ret.iter().rev().take_while(|x| **x == 0).count();
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

    use super::*;
    use crate::common::consts::ONE;
    use crate::common::util::random_subnormal;
    use crate::defs::{Sign, EXPONENT_MAX, EXPONENT_MIN};
    use rand::random;

    #[test]
    fn test_conv() {
        // basic tests
        let n = BigFloatNumber::from_f64(64, 0.031256789f64).unwrap();

        let (s, m, e) = n.convert_to_radix(Radix::Bin, RoundingMode::None).unwrap();

        assert!(
            m == [
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0,
                1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0
            ]
        );
        assert!(s == Sign::Pos);
        assert!(e == -4);

        let g = BigFloatNumber::convert_from_radix(s, &m, e, Radix::Bin, 160, RoundingMode::ToEven)
            .unwrap();
        let f = g.as_f64();

        assert!(f == 0.031256789f64);

        let n = BigFloatNumber::from_f64(64, 0.00012345678f64).unwrap();

        let (s, m, e) = n.convert_to_radix(Radix::Dec, RoundingMode::None).unwrap();

        assert_eq!(s, Sign::Pos);
        assert_eq!(
            m,
            [1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 4, 2]
        );
        assert_eq!(e, -3);

        let g = BigFloatNumber::convert_from_radix(
            Sign::Neg,
            &[1, 2, 3, 4, 5, 6, 7, 0],
            3,
            Radix::Oct,
            64,
            RoundingMode::None,
        )
        .unwrap();
        let n = BigFloatNumber::from_f64(64, -83.591552734375).unwrap();
        assert!(n.cmp(&g) == 0);

        #[cfg(target_arch = "x86")]
        {
            let n = BigFloatNumber::from_raw_parts(
                &[2576980377, 2576980377, 2576980377],
                96,
                Sign::Pos,
                -1,
            )
            .unwrap();
            let (s, m, e) = n.convert_to_radix(Radix::Oct, RoundingMode::None).unwrap();
            let g =
                BigFloatNumber::convert_from_radix(s, &m, e, Radix::Oct, 160, RoundingMode::ToEven)
                    .unwrap();

            assert!(n.cmp(&g) == 0);

            let n = BigFloatNumber::from_raw_parts(
                &[2576980377, 2576980377, 2576980377],
                96,
                Sign::Pos,
                -0,
            )
            .unwrap();
            let (s, m, e) = n.convert_to_radix(Radix::Dec, RoundingMode::None).unwrap();

            assert!(m == [6]);
            assert!(s == Sign::Pos);
            assert!(e == 0);

            let g =
                BigFloatNumber::convert_from_radix(s, &m, e, Radix::Dec, 96, RoundingMode::None)
                    .unwrap();
            assert!(g.cmp(&n) == 0);
        }

        #[cfg(target_arch = "x86_64")]
        {
            let n = BigFloatNumber::from_raw_parts(
                &[0x9999999999999999, 0x9999999999999999, 0x9999999999999999],
                192,
                Sign::Pos,
                -1,
            )
            .unwrap();
            let (s, m, e) = n.convert_to_radix(Radix::Oct, RoundingMode::None).unwrap();
            let g =
                BigFloatNumber::convert_from_radix(s, &m, e, Radix::Oct, 192, RoundingMode::ToEven)
                    .unwrap();

            assert!(n.cmp(&g) == 0);

            let n = BigFloatNumber::from_raw_parts(
                &[0x9999999999999999, 0x9999999999999999, 0x9999999999999999],
                192,
                Sign::Pos,
                -0,
            )
            .unwrap();
            let (s, m, e) = n
                .convert_to_radix(Radix::Dec, RoundingMode::ToEven)
                .unwrap();

            //println!("{:?}", m);
            assert!(
                m == [
                    5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                    9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                    9, 9, 9, 9, 9, 8, 8
                ]
            );
            assert!(s == Sign::Pos);
            assert!(e == 0);

            let g =
                BigFloatNumber::convert_from_radix(s, &m, e, Radix::Dec, 192, RoundingMode::ToEven)
                    .unwrap();
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

        // random normal values
        let mut eps = ONE.clone().unwrap();

        for _ in 0..1000 {
            let p1 = (random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
            let p = p1.min(p2);

            let mut n =
                BigFloatNumber::random_normal(p1, EXPONENT_MIN + p1 as Exponent, EXPONENT_MAX)
                    .unwrap();
            let rdx = random_radix();

            let (s1, m1, e1) = n.convert_to_radix(rdx, RoundingMode::ToEven).unwrap();
            let mut g =
                BigFloatNumber::convert_from_radix(s1, &m1, e1, rdx, p2, RoundingMode::ToEven)
                    .unwrap();

            //println!("\n{:?}", rdx);
            //println!("{:?} {:?} {}", s1, m1, e1);
            //println!("{:?}\n{:?}", n, g);

            if rdx == Radix::Dec {
                eps.set_exponent(n.get_exponent() - p as Exponent + 3);
                assert!(
                    n.sub(&g, p, RoundingMode::None)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps)
                        <= 0
                );
            } else {
                if p2 < p1 {
                    n.set_precision(p, RoundingMode::ToEven).unwrap();
                } else if p2 > p1 {
                    g.set_precision(p, RoundingMode::ToEven).unwrap();
                }

                assert!(n.cmp(&g) == 0);
            }
        }

        // subnormal values
        for _ in 0..1000 {
            let p1 = (random::<usize>() % 32 + 3) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % 32 + 3) * WORD_BIT_SIZE;
            let p = p1.min(p2);

            let mut n = random_subnormal(p1);
            let rdx = random_radix();

            let (s1, m1, e1) = n.convert_to_radix(rdx, RoundingMode::ToEven).unwrap();

            let mut g =
                BigFloatNumber::convert_from_radix(s1, &m1, e1, rdx, p2, RoundingMode::ToEven)
                    .unwrap();

            //println!("\n{:?}", rdx);
            //println!("{:?} {:?} {}", s1, m1, e1);
            //println!("{:?}\n{:?}", n, g);

            if rdx == Radix::Dec {
                let mut eps = BigFloatNumber::min_positive(p).unwrap();
                eps.set_exponent(eps.get_exponent() + 1);

                assert!(
                    n.sub(&g, p, RoundingMode::None)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps)
                        <= 0
                );
            } else {
                if p2 < p1 {
                    n.set_precision(p, RoundingMode::ToEven).unwrap();
                } else if p2 > p1 {
                    g.set_precision(p, RoundingMode::ToEven).unwrap();
                }

                assert!(n.cmp(&g) == 0);
            }
        }

        // MIN, MAX, min_subnormal
        let p1 = (random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % 32 + 1) * WORD_BIT_SIZE;
        let p = p1.min(p2);

        for rdx in [Radix::Bin, Radix::Oct, Radix::Dec, Radix::Hex] {
            // min, max
            // for p2 < p1 rounding will cause overflow, for p2 >= p1 no rounding is needed.
            let rm = RoundingMode::None;
            for mut n in
                [BigFloatNumber::max_value(p1).unwrap(), BigFloatNumber::min_value(p1).unwrap()]
            {
                //println!("\n{:?} {} {}", rdx, p1, p2);
                //println!("{:?}", n);

                let (s1, m1, e1) = n.convert_to_radix(rdx, rm).unwrap();

                //println!("{:?} {:?} {}", s1, m1, e1);

                let mut g = BigFloatNumber::convert_from_radix(s1, &m1, e1, rdx, p2, rm).unwrap();

                //println!("{:?}", g);

                if rdx == Radix::Dec {
                    eps.set_exponent(n.get_exponent() - p as Exponent + 3);
                    assert!(n.sub(&g, p, rm).unwrap().abs().unwrap().cmp(&eps) <= 0);
                } else {
                    if p2 < p1 {
                        n.set_precision(p, rm).unwrap();
                    } else if p2 > p1 {
                        g.set_precision(p, rm).unwrap();
                    }

                    assert!(n.cmp(&g) == 0);
                }
            }

            // min subnormal
            let rm = RoundingMode::ToEven;
            let mut n = BigFloatNumber::min_positive(p1).unwrap();
            //println!("\n{:?} {} {}", rdx, p1, p2);
            //println!("{:?}", n);
            let (s1, m1, e1) = n.convert_to_radix(rdx, rm).unwrap();

            //println!("{:?} {:?} {}", s1, m1, e1);

            let mut g = BigFloatNumber::convert_from_radix(s1, &m1, e1, rdx, p2, rm).unwrap();
            //println!("{:?}", g);

            if rdx == Radix::Dec {
                let mut eps = BigFloatNumber::min_positive(p).unwrap();
                eps.set_exponent(eps.get_exponent() + 1);
                assert!(n.sub(&g, p, rm).unwrap().abs().unwrap().cmp(&eps) <= 0);
            } else {
                if p2 < p1 {
                    n.set_precision(p, rm).unwrap();
                } else if p2 > p1 {
                    g.set_precision(p, rm).unwrap();
                }
                assert!(n.cmp(&g) == 0);
            }
        }

        // misc/invalid input
        let s1 = Sign::Pos;
        for rdx in [Radix::Bin, Radix::Oct, Radix::Dec, Radix::Hex] {
            for e1 in [123, -123, 0] {
                let m1 = [];
                assert!(BigFloatNumber::convert_from_radix(
                    s1,
                    &m1,
                    e1,
                    rdx,
                    p1,
                    RoundingMode::ToEven
                )
                .unwrap()
                .is_zero());
                let m1 = [1, rdx as u8, 0];
                assert!(
                    BigFloatNumber::convert_from_radix(s1, &m1, e1, rdx, p1, RoundingMode::ToEven)
                        .unwrap_err()
                        == Error::InvalidArgument
                );
                let m1 = [1, rdx as u8 - 1, 0];
                assert!(BigFloatNumber::convert_from_radix(
                    s1,
                    &m1,
                    e1,
                    rdx,
                    0,
                    RoundingMode::ToEven
                )
                .unwrap()
                .is_zero());
                let m1 = [0; 256];
                assert!(BigFloatNumber::convert_from_radix(
                    s1,
                    &m1,
                    e1,
                    rdx,
                    p1,
                    RoundingMode::ToEven
                )
                .unwrap()
                .is_zero());
                let m1 = [0];
                assert!(BigFloatNumber::convert_from_radix(
                    s1,
                    &m1,
                    e1,
                    rdx,
                    p1,
                    RoundingMode::ToEven
                )
                .unwrap()
                .is_zero());
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
