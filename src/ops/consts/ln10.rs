//! ln(10)

use crate::common::consts::ONE;
use crate::defs::Error;
use crate::num::BigFloatNumber;
use crate::RoundingMode;

fn pqr(a: usize, b: usize) -> Result<(BigFloatNumber, BigFloatNumber, BigFloatNumber), Error> {
    if a == b - 1 {
        let p = BigFloatNumber::from_word(81, 1)?;
        let q = BigFloatNumber::from_usize((2 * b + 1) * 121)?;
        let r = BigFloatNumber::from_usize((2 * b + 1) * 81)?;

        Ok((p, q, r))
    } else {
        let m = (a + b) / 2;

        let (pa, qa, ra) = pqr(a, m)?;
        let (pb, qb, rb) = pqr(m, b)?;

        let pq = pa.mul_full_prec(&qb)?;
        let pr = pb.mul_full_prec(&ra)?;

        let p = pq.add_full_prec(&pr)?;
        let q = qa.mul_full_prec(&qb)?;
        let r = ra.mul_full_prec(&rb)?;

        Ok((p, q, r))
    }
}

fn pqr_inc(
    pa: &BigFloatNumber,
    qa: &BigFloatNumber,
    ra: &BigFloatNumber,
    m: usize,
) -> Result<(BigFloatNumber, BigFloatNumber, BigFloatNumber, usize), Error> {
    let b = m * 2;

    let (pb, qb, rb) = pqr(m, b)?;

    let pq = pa.mul_full_prec(&qb)?;
    let pr = pb.mul_full_prec(ra)?;

    let p_ret = pq.add_full_prec(&pr)?;
    let q_ret = qa.mul_full_prec(&qb)?;
    let r_ret = ra.mul_full_prec(&rb)?;

    Ok((p_ret, q_ret, r_ret, b))
}

/// Holds value of currently computed ln(10).
#[derive(Debug)]
pub struct Ln10Cache {
    b: usize,
    pk: BigFloatNumber,
    qk: BigFloatNumber,
    rk: BigFloatNumber,
    val: BigFloatNumber,
}

impl Ln10Cache {
    pub fn new() -> Result<Self, Error> {
        let (p01, q01, r01) = pqr(0, 1)?;

        let val = Self::calc_ln10(&p01, &q01)?;

        Ok(Ln10Cache {
            b: 1,
            pk: p01,
            qk: q01,
            rk: r01,
            val,
        })
    }

    fn calc_ln10(p: &BigFloatNumber, q: &BigFloatNumber) -> Result<BigFloatNumber, Error> {
        // 18 * (1 + p / q) / 11
        let prec = p
            .get_mantissa_max_bit_len()
            .max(q.get_mantissa_max_bit_len());
        let mut val = p.div(q, prec, crate::RoundingMode::None)?;
        val = val.add(&ONE, prec, crate::RoundingMode::None)?;
        let f0 = BigFloatNumber::from_word(18, 1)?;
        let f1 = BigFloatNumber::from_word(11, 1)?;
        val = val.mul(&f0, prec, crate::RoundingMode::None)?;
        val.div(&f1, prec, crate::RoundingMode::None)
    }

    /// Return value of ln(10) with precision k (calculate if needed).
    pub fn for_prec(&mut self, k: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        let kext = k * 1728 / 1000 + 4;

        if self.b <= kext {
            let mut pk;
            let mut qk;
            let mut rk;
            let mut bb;

            (pk, qk, rk, bb) = pqr_inc(&self.pk, &self.qk, &self.rk, self.b)?;

            while bb <= kext {
                (pk, qk, rk, bb) = pqr_inc(&pk, &qk, &rk, bb)?;
            }

            let mut ret = Self::calc_ln10(&pk, &qk)?;

            self.val = ret.clone()?;

            ret.set_precision(k, rm)?;

            self.pk = pk;
            self.qk = qk;
            self.rk = rk;
            self.b = bb;

            Ok(ret)
        } else {
            let mut ret = self.val.clone()?;

            ret.set_precision(k, rm)?;

            Ok(ret)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::{RoundingMode, Sign};

    #[test]
    #[cfg(target_arch = "x86")]
    fn test_ln10_const() {
        let mut ln10 = Ln10Cache::new().unwrap();
        let c = ln10.for_prec(320, RoundingMode::ToEven).unwrap();
        //println!("{:?}", c.fp3(crate::Radix::Dec, RoundingMode::None));
        let r = BigFloatNumber::from_raw_parts(
            &[
                2980581469, 2519663319, 32517490, 2210799234, 3663591694, 3801083129, 2194868776,
                3931559467, 2863180822, 2472381917,
            ],
            320,
            Sign::Pos,
            2,
        )
        .unwrap();
        assert!(c.cmp(&r) == 0);
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn test_ln10_const() {
        let mut ln10 = Ln10Cache::new().unwrap();
        let c = ln10.for_prec(320, RoundingMode::ToEven).unwrap();
        //println!("{:?}", c);
        let r = BigFloatNumber::from_raw_parts(
            &[
                10821871555016396893,
                9495310408084368754,
                16325527732095940878,
                16885919335239060008,
                10618799479599967254,
            ],
            320,
            Sign::Pos,
            2,
        )
        .unwrap();
        assert!(c.cmp(&r) == 0);
    }
}
