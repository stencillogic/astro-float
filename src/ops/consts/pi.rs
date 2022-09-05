//! π number

use crate::RoundingMode;
use crate::defs::Error;
use crate::num::BigFloatNumber;


fn pqr(a: usize, b: usize) -> Result<(BigFloatNumber, BigFloatNumber, BigFloatNumber), Error> {

    if a == b - 1 {

        let n0 = BigFloatNumber::from_usize(6*b - 5)?;
        let n1 = BigFloatNumber::from_usize(2*b - 1)?;
        let n2 = BigFloatNumber::from_usize(6*b - 1)?;

        let n3 = n0.mul_full_prec(&n1)?;
        let r = n3.mul_full_prec(&n2)?;

        let n0 = BigFloatNumber::from_usize(10939058860032000)?;
        let n1 = BigFloatNumber::from_usize(b)?;
        let n2 = n1.mul_full_prec(&n1)?;
        let n3 = n2.mul_full_prec(&n1)?;
        let q = n0.mul_full_prec(&n3)?;

        let n0 = BigFloatNumber::from_usize(13591409 + 545140134*b)?;
        let mut p = r.mul_full_prec(&n0)?;

        if b & 1 != 0 {
            p.inv_sign();
        }

        Ok((p, q, r))

    } else {

        let m = (a + b) / 2;

        let (pa, qa, ra) = pqr(a, m)?;
        let (pb, qb, rb) = pqr(m, b)?;

        let r = ra.mul_full_prec(&rb)?;
        let q = qa.mul_full_prec(&qb)?;
        let n0 = pa.mul_full_prec(&qb)?;
        let n1 = pb.mul_full_prec(&ra)?;
        let p = n0.add_full_prec(&n1)?;

        Ok((p, q, r))
    }
}

fn pqr_inc(pa: &BigFloatNumber, qa: &BigFloatNumber, ra: &BigFloatNumber, m: usize) -> Result<(BigFloatNumber, BigFloatNumber, BigFloatNumber, usize), Error> {

    let b = m*2;

    let (pb, qb, rb) = pqr(m, b)?;

    let r = ra.mul_full_prec(&rb)?;
    let q = qa.mul_full_prec(&qb)?;
    let n0 = pa.mul_full_prec(&qb)?;
    let n1 = pb.mul_full_prec(ra)?;
    let p = n0.add_full_prec(&n1)?;

    Ok((p, q, r, b))
}

/// Holds value of currently computed ln(2).
pub struct Pi_cache {
    b: usize,
    pk: BigFloatNumber,
    qk: BigFloatNumber,
    rk: BigFloatNumber,
    val: BigFloatNumber,
}

impl Pi_cache {

    fn calc_pi(p: &BigFloatNumber, q: &BigFloatNumber, k: usize) -> Result<BigFloatNumber, Error>  {

        // p*4270934400 / ((p + q*13591409) * sqrt(10005))
        let n0 = BigFloatNumber::from_word(4270934400, 1)?;
        let n1 = BigFloatNumber::from_word(13591409, 1)?;

        let q0 = q.mul_full_prec(&n0)?;
        let q1 = q.mul_full_prec(&n1)?;
        let p0 = p.add_full_prec(&q1)?;

        let f3 = BigFloatNumber::from_word(10005, k)?;
        let f4 = f3.sqrt(RoundingMode::None)?;
        let f5 = p0.mul(&f4, RoundingMode::None)?;

        q0.div(&f5, RoundingMode::None)
    }

    pub fn new() -> Result<Self, Error> {

        let (p01, q01, r01) = pqr(0, 1)?;        

        let val = Self::calc_pi(&p01, &q01, 1)?;

        Ok(Pi_cache {
            b: 1,
            pk: p01,
            qk: q01,
            rk: r01,
            val,
        })
    }

    /// Return value of ln(2) with precision k.
    pub fn for_prec(&mut self, k: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {

        let kext = k + 51;

        if self.b <= kext {

            let mut pk;
            let mut qk;
            let mut rk;
            let mut bb;

            (pk, qk, rk, bb) = pqr_inc(&self.pk, &self.qk, &self.rk, self.b)?;

            while bb <= kext {

                (pk, qk, rk, bb) = pqr_inc(&pk, &qk, &rk, bb)?;
            }

            let mut ret = Self::calc_pi(&pk, &qk, k)?;

            self.val = ret.clone()?;

            ret.set_precision(k, rm)?;

            self.pk = pk;
            self.pk = qk;
            self.pk = rk;
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

    use crate::{RoundingMode, Sign};
    use super::*;

    #[test]
    fn test_pi_const() {
        let mut pi = Pi_cache::new().unwrap();
        let c = pi.for_prec(320, RoundingMode::ToEven).unwrap();
        //println!("{:?}", c.fp3(Radix::Dec, RoundingMode::None));
        let r = BigFloatNumber::from_raw_parts(&[2385773791, 1363806329, 991140642, 34324134, 2322058356, 688016904, 2161908945, 3301335691, 560513588, 3373259426], 320, Sign::Pos, 2).unwrap();
        assert!(c.cmp(&r) == 0);
    }
}