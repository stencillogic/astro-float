//! Conversion utilities.

use crate::common::consts::TEN;
use crate::common::util::log2_ceil;
use crate::common::util::round_p;
use crate::defs::DoubleWord;
use crate::defs::Error;
use crate::defs::Exponent;
use crate::defs::Radix;
use crate::defs::RoundingMode;
use crate::defs::Sign;
use crate::defs::Word;
use crate::defs::DEFAULT_P;
use crate::defs::WORD_BIT_SIZE;
use crate::defs::WORD_MAX;
use crate::mantissa::Mantissa;
use crate::num::BigFloatNumber;
use crate::Consts;
use crate::EXPONENT_MAX;
use crate::EXPONENT_MIN;

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

const TEN_PWR_MAX_TO_DEC: usize = EXPONENT_MAX as usize / 4;
const TEN_PWR_MAX_FROM_DEC: usize = (EXPONENT_MAX as u64 * 301029995 / 1000000000) as usize;

impl BigFloatNumber {
    /// Converts an array of digits in radix `rdx` to BigFloatNumber with precision `p`.
    /// `digits` represents mantissa and is interpreted as a number smaller than 1 and greater or equal to 1/`rdx`.
    /// The first element in `digits` is the most significant digit.
    /// `e` is the exponent part of the number, such that the number can be represented as `digits` * `rdx` ^ `e`.
    /// Precision is rounded upwards to the word size.
    /// if `p` equals usize::MAX then the precision of the resulting number is determined automatically from the input.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    ///  - InvalidArgument: the precision is incorrect, or `digits` contains unacceptable digits for given radix,
    /// or when `e` is less than EXPONENT_MIN or greater than EXPONENT_MAX.
    pub fn convert_from_radix(
        sign: Sign,
        digits: &[u8],
        e: Exponent,
        rdx: Radix,
        mut p: usize,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<Self, Error> {
        if p < usize::MAX {
            p = round_p(p);
            Self::p_assertion(p)?;

            if p == 0 {
                return Self::new(0);
            }
        }

        #[cfg(target_arch = "x86")]
        if e < EXPONENT_MIN || e > EXPONENT_MAX {
            return Err(Error::InvalidArgument);
        }

        match rdx {
            Radix::Bin => Self::conv_from_binary(sign, digits, e, p, rm),
            Radix::Oct => Self::conv_from_commensurable(sign, digits, e, 3, p, rm),
            Radix::Dec => Self::conv_from_dec(sign, digits, e, p, rm, cc),
            Radix::Hex => Self::conv_from_commensurable(sign, digits, e, 4, p, rm),
        }
    }

    fn conv_from_binary(
        sign: Sign,
        digits: &[u8],
        mut e: Exponent,
        p: usize,
        rm: RoundingMode,
    ) -> Result<Self, Error> {
        if digits.is_empty() {
            return Self::new(if p < usize::MAX { p } else { DEFAULT_P });
        }

        Self::p_assertion(round_p(digits.len()))?;

        let mut mantissa = Mantissa::new(digits.len())?;
        let mut d = 0;
        let mut shift = digits.len() % WORD_BIT_SIZE;
        if shift != 0 {
            shift = WORD_BIT_SIZE - shift;
        }

        let mut dst = mantissa.digits_mut().iter_mut();

        for v in digits.iter().rev() {
            if *v > 1 {
                return Err(Error::InvalidArgument);
            }

            d |= (*v as Word) << shift;
            shift += 1;

            if shift == WORD_BIT_SIZE {
                *dst.next().unwrap() = d; // mantissa has precision of digits.len()
                shift = 0;
                d = 0;
            }
        }

        if shift > 0 {
            *dst.next().unwrap() = d; // mantissa has precision of digits.len()
        }

        mantissa.update_bit_len();

        if p < usize::MAX {
            let mut ret = BigFloatNumber::from_raw_unchecked(mantissa, sign, e, false);

            ret.set_precision(p, rm)?;

            Ok(ret)
        } else {
            let shift = mantissa.max_bit_len() - mantissa.bit_len();

            if shift > 0 {
                if e > EXPONENT_MIN {
                    let e_shift = (e - EXPONENT_MIN) as usize;

                    if e_shift >= shift {
                        mantissa.normilize2();
                        e -= shift as Exponent;
                    } else {
                        mantissa.shift_left(e_shift);
                        mantissa.set_bit_len(mantissa.bit_len() + e_shift);
                        e = EXPONENT_MIN;
                    }
                }
            }

            Ok(BigFloatNumber::from_raw_unchecked(mantissa, sign, e, false))
        }
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
            let m = Mantissa::new(if p < usize::MAX { p } else { DEFAULT_P })?;

            Ok(BigFloatNumber::from_raw_unchecked(m, sign, 0, false))
        } else {
            let msz = round_p((digits.len() - zeroes) * shift + WORD_BIT_SIZE);

            Self::p_assertion(msz)?;

            let mut m = Mantissa::new(msz)?;

            // exponent
            let e = e as isize * shift as isize + e_shift;

            if e > EXPONENT_MAX as isize {
                return Err(Error::ExponentOverflow(sign));
            }

            // fill mantissa
            let mut filled = shift - first_shift;
            let mut dst = m.digits_mut().iter_mut().rev();
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

            m.set_bit_len(m.max_bit_len());

            let mut ret = if e < EXPONENT_MIN as isize {
                if p < usize::MAX {
                    let mut num = BigFloatNumber::from_raw_unchecked(m, sign, EXPONENT_MIN, false);

                    if p + WORD_BIT_SIZE > num.mantissa_max_bit_len() {
                        num.set_precision(p + WORD_BIT_SIZE, RoundingMode::None)?;
                    }

                    num.subnormalize(e, RoundingMode::None);

                    if num.inexact() {
                        num.mantissa_mut().digits_mut()[0] |= 1; // sticky for correct rounding when calling set_precision()
                    }

                    num
                } else {
                    let e_shift = (EXPONENT_MIN as isize - e) as usize;
                    let newbitlen = m.bit_len().saturating_add(e_shift);

                    Self::p_assertion(round_p(newbitlen))?;

                    m.extend_subnormal(e_shift)?;

                    let leftshift = m.max_bit_len() - newbitlen;
                    m.shift_left(leftshift);

                    BigFloatNumber::from_raw_unchecked(m, sign, EXPONENT_MIN, false)
                }
            } else {
                BigFloatNumber::from_raw_unchecked(m, sign, e as Exponent, false)
            };

            if p < usize::MAX {
                ret.set_precision(p, rm)?;
            }

            Ok(ret)
        }
    }

    fn conv_from_dec(
        sign: Sign,
        digits: &[u8],
        e: Exponent,
        p: usize,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<Self, Error> {
        // mantissa part
        let leadzeroes = digits.iter().take_while(|&&x| x == 0).count();

        if digits.len() - leadzeroes == 0 {
            return Self::new(if p < usize::MAX { p } else { DEFAULT_P });
        }

        let k = log2_ceil(digits.len() - leadzeroes);
        let tenpowers = cc.tenpowers(k)?;
        let mut m = Mantissa::conv_from_dec(&digits[leadzeroes..], tenpowers)?;

        if m.bit_len() > EXPONENT_MAX as usize {
            return Err(Error::ExponentOverflow(sign));
        }

        let me = m.bit_len() as Exponent;
        let _ = m.normilize2();

        let x = BigFloatNumber::from_raw_unchecked(m, sign, me, false);

        // exponent part
        let n = e as isize - digits.len() as isize;

        let p = if p < usize::MAX {
            p
        } else {
            // determine from the input
            let p = round_p((digits.len() as u64 * 3321928095 / 1000000000) as usize + 1);
            Self::p_assertion(p)?;
            p
        };

        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = p + p_inc;

        // error estimation
        let mut err = 0;
        let npowmax = n.unsigned_abs() / TEN_PWR_MAX_FROM_DEC;
        let tenpowrem = n.unsigned_abs() % TEN_PWR_MAX_FROM_DEC;
        if npowmax != 0 {
            err += 3 * npowmax;
        }
        if tenpowrem != 0 {
            err += 3;
        }

        loop {
            let p_f = p_wrk + err;

            let mut f = x.clone()?;

            if npowmax != 0 {
                let fpnmax = TEN.powi(TEN_PWR_MAX_FROM_DEC, p_f, RoundingMode::None)?;

                for _ in 0..npowmax {
                    if n < 0 {
                        f = f.div(&fpnmax, p_f, RoundingMode::None)?
                    } else {
                        f = f.mul(&fpnmax, p_f, RoundingMode::None)?
                    }
                }
            };

            if tenpowrem != 0 {
                let fpn = TEN.powi(tenpowrem, p_f, RoundingMode::None)?;
                if n < 0 {
                    f = f.div(&fpn, p_f, RoundingMode::None)?
                } else {
                    f = f.mul(&fpn, p_f, RoundingMode::None)?
                }
            }

            f.set_sign(sign);

            if f.try_set_precision(p, rm, p_wrk)? {
                return Ok(f);
            }

            p_wrk += p_inc;
            p_inc = round_p(p_wrk / 5);
        }
    }

    /// Converts `self` to radix `rdx` using rounding mode `rm`.
    /// The function returns sign, mantissa digits in radix `rdx`, and exponent such that the converted number
    /// can be represented as `mantissa digits` * `rdx` ^ `exponent`.
    /// The first element in the mantissa is the most significant digit.
    ///
    /// ## Errors
    ///
    ///  - MemoryAllocation: failed to allocate memory for mantissa.
    ///  - ExponentOverflow: the resulting exponent becomes greater than the maximum allowed value for the exponent.
    pub fn convert_to_radix(
        &self,
        rdx: Radix,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<(Sign, Vec<u8>, Exponent), Error> {
        match rdx {
            Radix::Bin => self.conv_to_binary(),
            Radix::Oct => self.conv_to_commensurable(3),
            Radix::Dec => self.conv_to_dec(rm, cc),
            Radix::Hex => self.conv_to_commensurable(4),
        }
    }

    fn conv_to_dec(
        &self,
        rm: RoundingMode,
        cc: &mut Consts,
    ) -> Result<(Sign, Vec<u8>, Exponent), Error> {
        if self.precision() == 0 {
            return Ok((self.sign(), Vec::new(), 0));
        }

        let p = self.mantissa_max_bit_len();
        let subn_e = p - self.precision();
        let n = (p as u64 * 301029996 / 1000000000) as usize + 1;

        let mut err = WORD_BIT_SIZE; // speculative
        let mut p_wrk = round_p((n as u64 * 3321928095 / 1000000000) as usize + 1 + err);
        let mut p_inc = WORD_BIT_SIZE;

        loop {
            let mut x = self.clone()?;
            x.set_inexact(false);

            let n_wrk = ((p_wrk as i64 - self.exponent() as i64 + subn_e as i64) * 301029996
                / 1000000000) as isize
                + 1;

            let mut err_acc = 0;

            let mut pwr = n_wrk.unsigned_abs();
            if pwr > TEN_PWR_MAX_TO_DEC {
                let tp = TEN.powi(TEN_PWR_MAX_TO_DEC, p_wrk, RoundingMode::None)?;
                err_acc += 1;

                while pwr > TEN_PWR_MAX_TO_DEC {
                    if n_wrk < 0 {
                        x = x.div(&tp, p_wrk, RoundingMode::None)?;
                    } else {
                        x = x.mul(&tp, p_wrk, RoundingMode::None)?;
                    }
                    err_acc += 2;
                    pwr -= TEN_PWR_MAX_TO_DEC;
                }
            }

            if pwr != 0 {
                let tp = TEN.powi(pwr, p_wrk, RoundingMode::None)?;
                if n_wrk < 0 {
                    x = x.div(&tp, p_wrk, RoundingMode::None)?;
                } else {
                    x = x.mul(&tp, p_wrk, RoundingMode::None)?;
                }
                err_acc += 3;
            }

            if err_acc > err {
                err_acc += err_acc / TEN_PWR_MAX_TO_DEC + 3;
                p_wrk += round_p(err_acc - err);
                err = err_acc;
                continue;
            }

            let (mut m, _, e, inexact) = x.to_raw_parts();

            let shift = e as usize - p_wrk;
            if shift > 0 {
                m.shift_left_resize(shift)?;
            }

            let l = (m.bit_len() as u64 * 301029996 / 1000000000) as usize + 1;

            let k = log2_ceil(l);

            let tenpowers = cc.tenpowers(k)?;
            let mut digits = m.conv_to_dec(1 << k, tenpowers, k - 1, true)?;

            let mut e_out = digits.len() as isize - n_wrk;

            let mut e_subn = 0;
            if e_out < EXPONENT_MIN as isize {
                e_subn = (EXPONENT_MIN as isize - e_out) as usize;
                e_out = EXPONENT_MIN as isize;
            }

            let mut e_out = e_out as Exponent;

            // try round
            let valid =
                digits.len() - ((shift + err_acc) as i64 * 301029996 / 1000000000) as usize - 1; // cut off digits with error

            debug_assert!(digits.len() > n);
            debug_assert!(valid > n);

            if Self::try_round_dec(
                &mut digits[..valid],
                n,
                rm,
                self.sign(),
                &mut e_out,
                inexact,
            )? {
                if e_subn > 0 {
                    if e_out > EXPONENT_MIN {
                        e_subn -= 1;
                        e_out = EXPONENT_MIN;
                    }

                    let rsz = if digits.len() > n { n } else { digits.len() };

                    digits.resize(rsz + e_subn, 0);
                    digits[rsz..].fill(0);
                    digits.rotate_right(e_subn);
                } else {
                    if digits.len() > n {
                        digits.resize(n, 0);
                    }
                }

                // remove trailing zeroes
                let nzr = digits.iter().rev().take_while(|&&x| x == 0).count();

                digits.resize(digits.len() - nzr, 0);

                return Ok((self.sign(), digits, e_out));
            }

            p_wrk += p_inc;
            p_inc = round_p(p_wrk / 5);
        }
    }

    // Try to round a decimal mantissa.
    fn try_round_dec(
        digits: &mut [u8],
        n: usize,
        rm: RoundingMode,
        s: Sign,
        e: &mut Exponent,
        inexact: bool,
    ) -> Result<bool, Error> {
        let mut check_roundable = inexact;

        if n > 0 {
            let ovf = Self::round_dec(digits, n, rm, s.is_positive(), &mut check_roundable);

            if check_roundable {
                return Ok(false);
            }

            if ovf {
                if *e == EXPONENT_MAX {
                    return Err(Error::ExponentOverflow(s));
                }

                *e += 1;
            }
        }

        Ok(true)
    }

    // Round decimal mantissa.
    // The function is similar to Mantissa::round_mantissa.
    fn round_dec(
        digits: &mut [u8],
        n: usize,
        rm: RoundingMode,
        is_positive: bool,
        check_roundable: &mut bool,
    ) -> bool {
        if rm == RoundingMode::None {
            *check_roundable = false;
            return false;
        }

        #[inline]
        fn get_rem(arr: &[u8]) -> (bool, bool) {
            let mut rem9 = true;
            let mut rem0 = true;

            for &d in arr.iter() {
                if d != 9 {
                    rem9 = false;
                }
                if d != 0 {
                    rem0 = false;
                }
            }
            (rem0, rem9)
        }

        if n > 0 && n < digits.len() {
            let mut c = false;

            if rm == RoundingMode::ToEven || rm == RoundingMode::ToOdd {
                let is_even = digits[n - 1] % 2 == 0;
                let dn = digits[n];

                let (rem0, rem9) = get_rem(&digits[n + 1..]);

                if *check_roundable && (rem0 || rem9) {
                    return false;
                }

                // need adding 1?
                match rm {
                    RoundingMode::ToEven => {
                        if dn == 5 {
                            if !is_even || !rem0 {
                                c = true;
                            }
                        } else if dn > 5 {
                            c = true;
                        }
                    }
                    RoundingMode::ToOdd => {
                        if dn == 5 {
                            if is_even || !rem0 {
                                c = true;
                            }
                        } else if dn > 5 {
                            c = true;
                        }
                    }
                    _ => unreachable!(),
                };
            } else {
                let (rem0, rem9) = get_rem(&digits[n..]);

                if *check_roundable && (rem0 || rem9) {
                    return false;
                }

                // rounding
                match rm {
                    RoundingMode::ToZero => {}
                    RoundingMode::FromZero => {
                        if !rem0 {
                            // add 1
                            c = true;
                        }
                    }
                    RoundingMode::Up => {
                        if !rem0 && is_positive {
                            // add 1
                            c = true;
                        }
                    }
                    RoundingMode::Down => {
                        if !rem0 && !is_positive {
                            // add 1
                            c = true;
                        }
                    }
                    _ => unreachable!(),
                };
            }

            *check_roundable = false; // can round

            digits[n..].fill(0);

            if c {
                for v in digits[..n].iter_mut().rev() {
                    if *v < 9 {
                        *v += 1;
                        return false;
                    } else {
                        *v = 0;
                    }
                }

                digits[0] = 1;

                return true;
            }
        }
        false
    }

    /// Conversion for radixes of power of 2.
    fn conv_to_commensurable(&self, shift: usize) -> Result<(Sign, Vec<u8>, Exponent), Error> {
        let mut e = self.exponent();
        let mut e_shift = e.unsigned_abs() as usize % shift;
        e /= shift as Exponent;
        if e_shift != 0 && self.exponent() > 0 {
            e_shift = shift - e_shift;
            e += 1;
        }

        let mut ret = Vec::new();
        ret.try_reserve_exact(self.mantissa_max_bit_len() / shift)?;

        let mask = (WORD_MAX >> (WORD_BIT_SIZE - shift)) as DoubleWord;
        let mut iter = self.mantissa().digits().iter().rev();

        let mut done = WORD_BIT_SIZE - shift + e_shift;
        let mut d = *iter.next().unwrap() as DoubleWord; // iter is never empty.
        let mut cnt = 0;

        loop {
            let digit = ((d >> done) & mask) as u8;

            if digit == 0 {
                cnt += 1;
            } else {
                cnt = 0;
            }

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
            if digit > 0 {
                cnt = 0;
                ret.push(digit);
            }
        }

        ret.resize(ret.len() - cnt, 0);

        Ok((self.sign(), ret, e))
    }

    fn conv_to_binary(&self) -> Result<(Sign, Vec<u8>, Exponent), Error> {
        let mut ret = Vec::new();
        ret.try_reserve_exact(self.mantissa_max_bit_len())?;
        let mut cnt = 0;

        for v in self.mantissa().digits().iter().rev() {
            for i in (0..WORD_BIT_SIZE).rev() {
                let val = ((v >> i) & 1) as u8;
                if val == 1 {
                    cnt = 0;
                } else {
                    cnt += 1;
                }
                ret.push(val);
            }
        }

        // cut off trailing zeroes
        ret.resize(ret.len() - cnt, 0);

        Ok((self.sign(), ret, self.exponent()))
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::common::consts::ONE;
    use crate::common::util::random_subnormal;
    use crate::defs::{Sign, EXPONENT_MAX, EXPONENT_MIN};
    use rand::random;

    #[cfg(not(feature = "std"))]
    use alloc::vec;

    #[test]
    fn test_conv_num() {
        let mut cc = Consts::new().unwrap();

        // basic tests
        let n = BigFloatNumber::from_f64(64, 0.031256789f64).unwrap();

        let (s, m, e) = n
            .convert_to_radix(Radix::Bin, RoundingMode::None, &mut cc)
            .unwrap();

        assert_eq!(
            m,
            [
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0,
                1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1
            ]
        );
        assert_eq!(s, Sign::Pos);
        assert_eq!(e, -4);

        let g = BigFloatNumber::convert_from_radix(
            s,
            &m,
            e,
            Radix::Bin,
            160,
            RoundingMode::ToEven,
            &mut cc,
        )
        .unwrap();
        let f = g.to_f64();

        assert_eq!(f, 0.031256789f64);

        let n = BigFloatNumber::from_f64(64, 0.00012345678f64).unwrap();

        let (s, m, e) = n
            .convert_to_radix(Radix::Dec, RoundingMode::None, &mut cc)
            .unwrap();

        assert_eq!(s, Sign::Pos);
        assert_eq!(
            m,
            [1, 2, 3, 4, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 4]
        );
        assert_eq!(e, -3);

        let g = BigFloatNumber::convert_from_radix(
            Sign::Neg,
            &[1, 2, 3, 4, 5, 6, 7, 0],
            3,
            Radix::Oct,
            64,
            RoundingMode::None,
            &mut cc,
        )
        .unwrap();
        let n = BigFloatNumber::from_f64(64, -83.591552734375).unwrap();
        assert_eq!(n.cmp(&g), 0);

        #[cfg(target_arch = "x86")]
        {
            let n = BigFloatNumber::from_raw_parts(
                &[2576980377, 2576980377, 2576980377],
                96,
                Sign::Pos,
                -1,
                false,
            )
            .unwrap();
            let (s, m, e) = n
                .convert_to_radix(Radix::Oct, RoundingMode::None, &mut cc)
                .unwrap();
            let g = BigFloatNumber::convert_from_radix(
                s,
                &m,
                e,
                Radix::Oct,
                160,
                RoundingMode::ToEven,
                &mut cc,
            )
            .unwrap();

            assert!(n.cmp(&g) == 0);

            let n = BigFloatNumber::from_raw_parts(
                &[2576980377, 2576980377, 2576980377],
                96,
                Sign::Pos,
                -0,
                false,
            )
            .unwrap();
            let (s, m, e) = n
                .convert_to_radix(Radix::Dec, RoundingMode::None, &mut cc)
                .unwrap();

            assert_eq!(
                m,
                [
                    5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                    9, 9, 9
                ]
            );
            assert!(s == Sign::Pos);
            assert!(e == 0);

            let g = BigFloatNumber::convert_from_radix(
                s,
                &m,
                e,
                Radix::Dec,
                96,
                RoundingMode::ToEven,
                &mut cc,
            )
            .unwrap();
            assert!(g.cmp(&n) == 0);
        }

        #[cfg(not(target_arch = "x86"))]
        {
            let n = BigFloatNumber::from_raw_parts(
                &[0x9999999999999999, 0x9999999999999999, 0x9999999999999999],
                192,
                Sign::Pos,
                -1,
                false,
            )
            .unwrap();
            let (s, m, e) = n
                .convert_to_radix(Radix::Oct, RoundingMode::None, &mut cc)
                .unwrap();
            let g = BigFloatNumber::convert_from_radix(
                s,
                &m,
                e,
                Radix::Oct,
                192,
                RoundingMode::ToEven,
                &mut cc,
            )
            .unwrap();

            assert!(n.cmp(&g) == 0);

            let n = BigFloatNumber::from_raw_parts(
                &[0x9999999999999999, 0x9999999999999999, 0x9999999999999999],
                192,
                Sign::Pos,
                -0,
                false,
            )
            .unwrap();
            let (s, m, e) = n
                .convert_to_radix(Radix::Dec, RoundingMode::ToEven, &mut cc)
                .unwrap();

            assert_eq!(
                m,
                [
                    5, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                    9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
                    9, 9, 9, 9, 9, 9
                ]
            );
            assert_eq!(s, Sign::Pos);
            assert_eq!(e, 0);

            let g = BigFloatNumber::convert_from_radix(
                s,
                &m,
                e,
                Radix::Dec,
                192,
                RoundingMode::ToEven,
                &mut cc,
            )
            .unwrap();
            //println!("{:?}", g);
            //println!("{:?}", n);
            assert!(g.cmp(&n) == 0);
        }

        /* let n = BigFloatNumber::from_words(&[10946118985158034780, 0, 0], Sign::Pos, -2147483648).unwrap();
        let (s, m , e) = (Sign::Pos, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 7, 5, 1, 6, 10, 5, 0, 10, 12, 6, 9, 15, 11, 9, 15, 13, 13, 10, 7, 7, 10, 10, 3, 10, 5, 13, 12, 1, 7, 11, 2, 0, 3, 0, 13, 8, 6, 4, 4, 2, 7, 4, 14, 4, 15, 2, 12, 1, 8, 15, 13, 2, 6, 13, 1, 3, 10, 12, 2, 1, 10, 1, 1, 3, 9, 2, 10, 12, 9, 9, 8, 8, 10, 9, 11, 4, 13, 10, 3, 7, 5, 10, 4, 5, 7, 3, 15, 5, 8, 7, 12, 12, 8, 14, 6, 2, 6, 7, 9, 9, 5, 0, 13, 12, 12, 10, 15, 9, 0, 0, 3, 14, 15, 1, 0, 2, 1, 10, 15, 12, 11, 1, 0, 11, 9, 0, 12, 15, 3, 7, 2, 15, 13, 7, 6, 2, 10, 8, 11, 5, 6, 8, 8, 10, 9, 12, 9, 1, 4, 8, 12, 3, 5, 4, 3, 12, 7, 5, 3, 13, 11, 11, 14, 8, 8, 14, 14, 4, 11, 5, 6, 0, 2, 1, 4, 2, 0, 10, 0, 6, 9, 0, 7, 12, 14, 3, 10, 11, 1, 8, 15, 11, 9, 3, 6, 1, 3, 15, 11, 13, 10, 6, 5, 1, 7, 11, 12, 13, 3, 5, 0, 14, 9, 9, 1, 5, 6, 1, 15, 13, 6, 9, 10, 0, 8, 1, 7, 6, 2, 10, 7, 6, 1, 7, 12, 5, 8, 4, 4, 6, 1, 3, 12, 2, 5, 0, 10, 7, 12, 5, 6, 10, 3, 5, 14, 5, 1, 9, 7, 5, 11, 13, 0, 15, 12, 2, 11, 8, 14, 4, 11, 1, 4, 4, 14, 5, 7, 12, 11, 8, 10, 8, 13, 8, 13, 3, 12, 1, 1, 7, 4, 9, 3, 2, 15, 12, 14, 2, 8, 8, 15, 2, 4, 9, 3, 9, 11, 0, 9, 7, 7, 6, 7, 14, 14, 4, 1, 2, 4, 5, 10, 13, 13, 12, 7, 5, 13, 5, 1, 1, 0, 1, 15, 2, 7, 1, 8, 7, 4, 4, 11, 4, 4, 0, 2, 12, 3, 15, 6, 15, 0, 11, 2, 6, 2, 15, 14, 5, 4, 14, 14, 1, 7, 10, 9, 3, 4, 7, 2, 2, 9, 8, 1, 13, 3, 4, 6, 3, 3, 10, 5, 5, 13, 8, 15, 8, 10, 5, 2, 15, 13, 13, 3, 11, 8, 1, 10, 8, 0, 1, 0, 14, 1, 11, 10, 10, 10, 0, 13, 9, 8, 6, 13, 9, 0, 0, 15, 5, 4, 12, 5, 15, 11, 9, 5, 5, 10, 0, 2, 3, 12, 11, 4, 14, 13, 9, 13, 0, 6, 0, 9, 12, 3, 5, 13, 5, 3, 8, 8, 6, 5, 2, 5, 9, 13, 2, 13, 12, 4, 1, 13, 13, 9], -536870912);

        let g = BigFloatNumber::convert_from_radix(s, &m, e, Radix::Hex, 1920, RoundingMode::ToEven).unwrap();
        println!("{:?}", g);
        return; */

        // random normal values
        let mut eps = ONE.clone().unwrap();
        let p_rng = 32;

        for _ in 0..1000 {
            let p1 = (random::<usize>() % p_rng + 1) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % p_rng + 1) * WORD_BIT_SIZE;
            let p = p1.min(p2);

            let mut n =
                BigFloatNumber::random_normal(p1, EXPONENT_MIN + p1 as Exponent, EXPONENT_MAX)
                    .unwrap();
            let rdx = random_radix();

            let (s1, m1, e1) = n
                .convert_to_radix(rdx, RoundingMode::ToEven, &mut cc)
                .unwrap();
            let mut g = BigFloatNumber::convert_from_radix(
                s1,
                &m1,
                e1,
                rdx,
                p2,
                RoundingMode::ToEven,
                &mut cc,
            )
            .unwrap();

            //println!("\n{:?}", rdx);
            //println!("{:?} {:?} {}", s1, m1, e1);
            //println!("{:?}\n{:?}", n, g);

            if rdx == Radix::Dec {
                eps.set_exponent(n.exponent() - p as Exponent + 3);
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
            let p1 = (random::<usize>() % p_rng + 3) * WORD_BIT_SIZE;
            let p2 = (random::<usize>() % p_rng + 3) * WORD_BIT_SIZE;
            let p = p1.min(p2);

            let mut n = random_subnormal(p1);
            let rdx = random_radix();

            let (s1, m1, e1) = n
                .convert_to_radix(rdx, RoundingMode::ToEven, &mut cc)
                .unwrap();

            //println!("\n{:?}", rdx);
            //println!("{:?} {:?} {}", s1, m1, e1);

            let mut g = BigFloatNumber::convert_from_radix(
                s1,
                &m1,
                e1,
                rdx,
                p2,
                RoundingMode::ToEven,
                &mut cc,
            )
            .unwrap();

            //println!("\n{:?}", rdx);
            //println!("{:?} {:?} {}", s1, m1, e1);
            //println!("{:?}\n{:?}", n, g);

            if rdx == Radix::Dec {
                let mut eps = BigFloatNumber::min_positive(p).unwrap();
                eps.set_exponent(eps.exponent() + 1);

                assert!(
                    n.sub(&g, p, RoundingMode::None)
                        .unwrap()
                        .abs()
                        .unwrap()
                        .cmp(&eps)
                        <= 0,
                    "{:?} {:?}",
                    n,
                    g
                );
            } else {
                if p2 < p1 {
                    n.set_precision(p, RoundingMode::ToEven).unwrap();
                } else if p2 > p1 {
                    g.set_precision(p, RoundingMode::ToEven).unwrap();
                }

                assert!(n.cmp(&g) == 0, "{:?} {:?} {:?}", rdx, n, g);
            }
        }

        // MIN, MAX, min_subnormal
        let p1 = (random::<usize>() % p_rng + 1) * WORD_BIT_SIZE;
        let p2 = (random::<usize>() % p_rng + 1) * WORD_BIT_SIZE;
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

                let (s1, m1, e1) = n.convert_to_radix(rdx, rm, &mut cc).unwrap();

                //println!("{:?} {:?} {}", s1, m1, e1);

                let mut g =
                    BigFloatNumber::convert_from_radix(s1, &m1, e1, rdx, p2, rm, &mut cc).unwrap();

                //println!("{:?}", g);

                if rdx == Radix::Dec {
                    eps.set_exponent(n.exponent() - p as Exponent + 4);
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
            let (s1, m1, e1) = n.convert_to_radix(rdx, rm, &mut cc).unwrap();

            //println!("{:?} {:?} {}", s1, m1, e1);

            let mut g =
                BigFloatNumber::convert_from_radix(s1, &m1, e1, rdx, p2, rm, &mut cc).unwrap();
            //println!("{:?}", g);

            if rdx == Radix::Dec {
                let mut eps = BigFloatNumber::min_positive(p).unwrap();
                eps.set_exponent(eps.exponent() + 1);
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
                    RoundingMode::ToEven,
                    &mut cc
                )
                .unwrap()
                .is_zero());
                let m1 = [1, rdx as u8, 0];
                assert!(
                    BigFloatNumber::convert_from_radix(
                        s1,
                        &m1,
                        e1,
                        rdx,
                        p1,
                        RoundingMode::ToEven,
                        &mut cc
                    )
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
                    RoundingMode::ToEven,
                    &mut cc,
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
                    RoundingMode::ToEven,
                    &mut cc,
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
                    RoundingMode::ToEven,
                    &mut cc,
                )
                .unwrap()
                .is_zero());
            }
        }

        // unkonwn p: binary, octal, hexadecimal
        for (s1, exp, rdx) in [
            // Bin
            (
                vec![
                    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
                ],
                123,
                Radix::Bin,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0,
                    0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1,
                ],
                EXPONENT_MIN + 3,
                Radix::Bin,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0,
                    0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1,
                ],
                EXPONENT_MIN,
                Radix::Bin,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0,
                    0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1,
                ],
                EXPONENT_MIN + 256,
                Radix::Bin,
            ),
            // Oct
            (
                vec![
                    7, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                123,
                Radix::Oct,
            ),
            (
                vec![
                    7, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                EXPONENT_MIN / 3 - 123,
                Radix::Oct,
            ),
            (
                vec![
                    3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                EXPONENT_MIN / 3 + 123,
                Radix::Oct,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1,
                    1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0,
                    0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                EXPONENT_MIN / 3 - 123,
                Radix::Oct,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1,
                    1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0,
                    0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                EXPONENT_MIN / 3 + 123,
                Radix::Oct,
            ),
            // Hex
            (
                vec![
                    0xF, 0, 2, 0, 0, 0, 0, 0, 0xD, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 0, 0xA, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                123,
                Radix::Hex,
            ),
            (
                vec![
                    0xF, 0, 2, 0, 0, 0, 0, 0, 0xD, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 0, 0xA, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                EXPONENT_MIN / 4 - 123,
                Radix::Hex,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    7, 0, 2, 0, 0, 0, 0, 0, 0xD, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1,
                    0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1,
                    0, 0, 0, 0, 0, 0xA, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                EXPONENT_MIN / 4 - 123,
                Radix::Hex,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    7, 0, 2, 0, 0, 0, 0, 0, 0xD, 0, 0, 0, 4, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1,
                    0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1,
                    0, 0, 0, 0, 0, 0xA, 0, 0, 0, 0, 0, 3, 0, 6,
                ],
                EXPONENT_MIN / 4 + 123,
                Radix::Hex,
            ),
            // Dec
            (
                vec![
                    9, 5, 7, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 9, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 9, 1, 1, 7, 0, 0, 0, 0, 1, 1, 1, 5, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 6,
                ],
                123,
                Radix::Dec,
            ),
            (
                vec![
                    9, 5, 7, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 9, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 9, 1, 1, 7, 0, 0, 0, 0, 1, 1, 1, 5, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 5,
                ],
                EXPONENT_MIN / 10 - 123,
                Radix::Dec,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    9, 5, 7, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 9, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 9, 1, 1, 7, 0, 0, 0, 0, 1, 1, 1, 5, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 7,
                ],
                EXPONENT_MIN / 10 - 123,
                Radix::Dec,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    9, 5, 7, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 9, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 9, 1, 1, 7, 0, 0, 0, 0, 1, 1, 1, 5, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 5,
                ],
                EXPONENT_MIN / 10 + 10,
                Radix::Dec,
            ),
            (
                vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    9, 5, 7, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 9, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1,
                    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 9, 1, 1, 7, 0, 0, 0, 0, 1, 1, 1, 5, 0, 0, 1, 1,
                    1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 2, 0, 5,
                ],
                123,
                Radix::Dec,
            ),
        ] {
            let mut g = BigFloatNumber::convert_from_radix(
                Sign::Pos,
                &s1,
                exp,
                rdx,
                usize::MAX,
                RoundingMode::None,
                &mut cc,
            )
            .unwrap();

            let (s, d, e) = g
                .convert_to_radix(rdx, RoundingMode::None, &mut cc)
                .unwrap();

            // verify no information loss in mantissa becase of length
            let lead_zeroes_s1 = s1.iter().take_while(|&&x| x == 0).count();
            let lead_zeroes_d = d.iter().take_while(|&&x| x == 0).count();
            assert!(*d.iter().last().unwrap() != 0);
            assert!(*s1.iter().last().unwrap() != 0);
            assert!(d.len() - lead_zeroes_d >= s1.len() - lead_zeroes_s1);

            let mut n = BigFloatNumber::convert_from_radix(
                s,
                &d,
                e,
                rdx,
                usize::MAX,
                RoundingMode::None,
                &mut cc,
            )
            .unwrap();

            if rdx == Radix::Dec {
                if g.mantissa_max_bit_len() < n.mantissa_max_bit_len() {
                    n.set_precision(g.mantissa_max_bit_len(), RoundingMode::ToEven)
                        .unwrap();
                } else {
                    g.set_precision(n.mantissa_max_bit_len(), RoundingMode::ToEven)
                        .unwrap();
                }

                assert!(n.cmp(&g) == 0);
            } else {
                assert!(n.cmp(&g) == 0);
            }
        }

        // unknown p: decimal
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

    #[test]
    fn test_round_dec() {
        let mut testset = [
            (
                RoundingMode::ToEven,
                vec![
                    (
                        ([1, 2, 3, 5, 0, 0], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 5, 0, 0], false, true),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 5, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 5, 0, 1], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),  // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 4, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 6, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 4, 9, 9], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 4, 9, 9], false, true),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 5, 0, 0], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 5, 0, 0], false, true),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 5, 0, 1], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 5, 0, 0, 0], false, false),  // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 4, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 6, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 5, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 4, 9, 9], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                ],
            ),
            (
                RoundingMode::ToOdd,
                vec![
                    (
                        ([1, 2, 3, 5, 0, 0], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 5, 0, 0], false, true),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 5, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 5, 0, 1], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),  // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 4, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 6, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 4, 9, 9], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 5, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 5, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 5, 0, 1], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 5, 0, 0, 0], false, false),  // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 4, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 6, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 5, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 4, 4, 9, 9], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 4, 9, 9], false, true),   // output, overflow, check_roundable
                    ),
                ],
            ),
            (
                RoundingMode::FromZero,
                vec![
                    (
                        ([1, 2, 3, 0, 0, 0], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, true),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 0, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 0, 0, 1], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),  // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 9, 9, 9], false, true),   // output, overflow, check_roundable
                    ),
                ],
            ),
            (
                RoundingMode::ToZero,
                vec![
                    (
                        ([1, 2, 3, 0, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 9, 9, 9], false, true),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 1, 1, 1], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),  // output, overflow, check_roundable
                    ),
                ],
            ),
            (
                RoundingMode::None,
                vec![
                    (
                        ([1, 2, 3, 1, 2, 3], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 1, 2, 3], false, false),  // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 1, 2, 3], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 1, 2, 3], false, false),   // output, overflow, check_roundable
                    ),
                ],
            ),
            (
                RoundingMode::Up,
                vec![
                    (
                        ([1, 2, 3, 0, 0, 0], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, true),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 0, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 0, 0, 1], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),  // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 0, 0, 0], 3, false, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),    // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, false, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 9, 9, 9], false, true),    // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, false, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),    // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 1, 1, 1], 3, false, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                ],
            ),
            (
                RoundingMode::Down,
                vec![
                    (
                        ([1, 2, 3, 0, 0, 0], 3, false, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, true),    // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 0, 0, 0], 3, false, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),    // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 0, 0, 1], 3, false, true), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, false, false), // input, n, is_positive, check_roundable
                        ([1, 2, 4, 0, 0, 0], false, false),    // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 0, 0, 0], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 9, 9, 9], false, true),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 9, 9, 9], 3, true, false), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),   // output, overflow, check_roundable
                    ),
                    (
                        ([1, 2, 3, 1, 1, 1], 3, true, true), // input, n, is_positive, check_roundable
                        ([1, 2, 3, 0, 0, 0], false, false),  // output, overflow, check_roundable
                    ),
                ],
            ),
        ];

        for (rm, sets) in testset.iter_mut() {
            for (
                (input, n, is_positive, check_roundable),
                (output, overflow, check_roundable_ret),
            ) in sets.iter_mut()
            {
                match rm {
                    RoundingMode::ToEven
                    | RoundingMode::ToOdd
                    | RoundingMode::FromZero
                    | RoundingMode::ToZero
                    | RoundingMode::None => {
                        // indifferent of sign
                        for is_positive in [true, false] {
                            let ovf = BigFloatNumber::round_dec(
                                input,
                                *n,
                                *rm,
                                is_positive,
                                check_roundable,
                            );
                            assert_eq!(*check_roundable, *check_roundable_ret);
                            assert_eq!(*overflow, ovf);
                            assert_eq!(*input, *output);
                        }
                    }
                    RoundingMode::Down | RoundingMode::Up => {
                        let ovf = BigFloatNumber::round_dec(
                            input,
                            *n,
                            *rm,
                            *is_positive,
                            check_roundable,
                        );
                        assert_eq!(*check_roundable, *check_roundable_ret);
                        assert_eq!(*overflow, ovf);
                        assert_eq!(*input, *output);
                    }
                }
            }
        }

        // overflow
        let mut input = [9, 9, 9, 9, 9, 9];
        let mut check_roundable = false;
        let ovf =
            BigFloatNumber::round_dec(&mut input, 3, RoundingMode::Up, true, &mut check_roundable);
        assert!(ovf);
        assert_eq!(input, [1, 0, 0, 0, 0, 0]);

        // n = input.len()
        let mut input = [9, 9, 9, 9, 9, 9];
        let mut check_roundable = false;
        let ovf =
            BigFloatNumber::round_dec(&mut input, 6, RoundingMode::Up, true, &mut check_roundable);
        assert!(!ovf);
        assert_eq!(input, [9, 9, 9, 9, 9, 9]);

        // n > input.len()
        let mut input = [9, 9, 9, 9, 9, 9];
        let mut check_roundable = false;
        let ovf =
            BigFloatNumber::round_dec(&mut input, 7, RoundingMode::Up, true, &mut check_roundable);
        assert!(!ovf);
        assert_eq!(input, [9, 9, 9, 9, 9, 9]);

        // n = 0
        let mut input = [9, 9, 9, 9, 9, 9];
        let mut check_roundable = false;
        let ovf =
            BigFloatNumber::round_dec(&mut input, 0, RoundingMode::Up, true, &mut check_roundable);
        assert!(!ovf);
        assert_eq!(input, [9, 9, 9, 9, 9, 9]);

        // try round
        assert!(BigFloatNumber::try_round_dec(
            &mut [9, 9, 9, 9, 9, 9],
            3,
            RoundingMode::Up,
            Sign::Pos,
            &mut 0,
            false
        )
        .unwrap());
        assert!(!BigFloatNumber::try_round_dec(
            &mut [9, 9, 9, 9, 9, 9],
            3,
            RoundingMode::Up,
            Sign::Pos,
            &mut 0,
            true
        )
        .unwrap());

        let mut e = 0;
        assert!(BigFloatNumber::try_round_dec(
            &mut [9, 9, 9, 9, 9, 0],
            3,
            RoundingMode::Up,
            Sign::Pos,
            &mut e,
            true
        )
        .unwrap());
        assert_eq!(e, 1);

        e = EXPONENT_MAX;
        assert_eq!(
            BigFloatNumber::try_round_dec(
                &mut [9, 9, 9, 9, 9, 0],
                3,
                RoundingMode::FromZero,
                Sign::Neg,
                &mut e,
                true
            ),
            Err(Error::ExponentOverflow(Sign::Neg))
        );
    }
}
