//! Euler's number

use crate::common::consts::ONE;
use crate::common::util::log2_floor;
use crate::defs::Error;
use crate::num::BigFloatNumber;
use crate::RoundingMode;

fn pq(a: usize, b: usize) -> Result<(BigFloatNumber, BigFloatNumber), Error> {
    if a == b - 1 {
        let q = BigFloatNumber::from_usize(b)?;
        let p = BigFloatNumber::from_word(1, 1)?;

        Ok((p, q))
    } else {
        let m = (a + b) / 2;

        let (pa, qa) = pq(a, m)?;
        let (pb, qb) = pq(m, b)?;

        let q = qa.mul_full_prec(&qb)?;
        let n0 = pa.mul_full_prec(&qb)?;
        let p = n0.add_full_prec(&pb)?;

        Ok((p, q))
    }
}

fn pqr_inc(
    pa: &BigFloatNumber,
    qa: &BigFloatNumber,
    m: usize,
) -> Result<(BigFloatNumber, BigFloatNumber, usize), Error> {
    let b = m * 2;

    let (pb, qb) = pq(m, b)?;

    let q = qa.mul_full_prec(&qb)?;
    let n0 = pa.mul_full_prec(&qb)?;
    let p = n0.add_full_prec(&pb)?;

    Ok((p, q, b))
}

/// Holds value of currently computed e.
pub struct ECache {
    b: usize,
    pk: BigFloatNumber,
    qk: BigFloatNumber,
    val: BigFloatNumber,
}

impl ECache {
    fn calc_e(p: &BigFloatNumber, q: &BigFloatNumber) -> Result<BigFloatNumber, Error> {
        // 1 + pk / qk
        let prec = p
            .get_mantissa_max_bit_len()
            .max(q.get_mantissa_max_bit_len());
        let f0 = p.div(q, prec, RoundingMode::None)?;
        f0.add(&ONE, prec, RoundingMode::None)
    }

    pub fn new() -> Result<Self, Error> {
        // initial precision is large enough, as b_factor() requires it.
        let (p01, q01) = pq(0, 64)?;

        let val = Self::calc_e(&p01, &q01)?;

        Ok(ECache {
            b: 64,
            pk: p01,
            qk: q01,
            val,
        })
    }

    fn b_factor(x: usize) -> usize {
        // If we compute n elements of the series 1 + 1/1! + 1/2! + ... 
        // then 1/(n!) is greater than the remaining part: sum(1/(k!)), k = n+1 .. +inf 
        // (we can see it if we divide sum(1/(k!)) by 1/(n!)).
        // So, for n parts the error is less than 1/(n!).
        // Let p be the precision we need.
        // From Stirling's approximation: 1/(n!) < (e/n)^n.
        // From (e/n)^n < 1/(2^p) follows simplified, but more strict, inequality n*(log2(n) - 2) > p.
        // Assume n = p / log2(p) - log2(log2(p)), and substitute in the inequality above, 
        // then for large enough p the inequality is true.
        let ln = log2_floor(x);
        let lln = log2_floor(ln);

        // to give higher estimate log2_floor is used, 
        // and 3 is an empirical adjustment.
        x / (ln - lln - 3)
    }

    /// Return value of e with precision k.
    pub fn for_prec(&mut self, k: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        let kext = Self::b_factor(k);

        if self.b <= kext {
            let mut pk;
            let mut qk;
            let mut bb;

            (pk, qk, bb) = pqr_inc(&self.pk, &self.qk, self.b)?;

            while bb <= kext {
                (pk, qk, bb) = pqr_inc(&pk, &qk, bb)?;
            }

            let mut ret = Self::calc_e(&pk, &qk)?;

            self.val = ret.clone()?;

            ret.set_precision(k, rm)?;

            self.pk = pk;
            self.qk = qk;
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
    fn test_e_const() {
        let mut e = ECache::new().unwrap();
        let c = e.for_prec(320, RoundingMode::ToEven).unwrap();
        //println!("{:?}", c);
        let r = BigFloatNumber::from_raw_parts(
            &[
                614153977, 3432226254, 342111227, 2850108993, 3459069589, 3636053379, 658324721,
                2950452768, 2730183322, 2918732888,
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
    fn test_e_const() {
        let mut e = ECache::new().unwrap();
        let c = e.for_prec(320, RoundingMode::ToEven).unwrap();
        //println!("{:?}", c);
        let r = BigFloatNumber::from_raw_parts(
            &[
                14741299514016743161,
                12241124915312604155,
                15616730352774362773,
                12672098147611000049,
                12535862302449814170,
            ],
            320,
            Sign::Pos,
            2,
        )
        .unwrap();
        assert!(c.cmp(&r) == 0);
    }
}
