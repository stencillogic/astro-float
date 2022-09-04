//! π number

use crate::RoundingMode;
use crate::common::int::Int;
use crate::defs::Error;
use crate::num::BigFloatNumber;


fn pqr(a: usize, b: usize) -> Result<(Int, Int, Int), Error> {

    if a == b - 1 {

        let n0 = Int::from_usize(6*b - 5)?;
        let n1 = Int::from_usize(2*b - 1)?;
        let n2 = Int::from_usize(6*b - 1)?;

        let n3 = n0.mul(&n1)?;
        let r = n3.mul(&n2)?;

        let n0 = Int::from_usize(10939058860032000)?;
        let n1 = Int::from_usize(b)?;
        let n2 = n1.mul(&n1)?;
        let n3 = n2.mul(&n1)?;
        let q = n0.mul(&n3)?;

        let n0 = Int::from_usize(13591409 + 545140134*b)?;
        let mut p = r.mul(&n0)?;

        if b & 1 != 0 {
            p.set_sign(-1);
        }

        Ok((p, q, r))

    } else {

        let m = (a + b) / 2;

        let (pa, qa, ra) = pqr(a, m)?;
        let (pb, qb, rb) = pqr(m, b)?;

        let r = ra.mul(&rb)?;
        let q = qa.mul(&qb)?;
        let n0 = pa.mul(&qb)?;
        let n1 = pb.mul(&ra)?;
        let p = n0.add(&n1)?;

        Ok((p, q, r))
    }
}

fn pqr_inc(pa: &Int, qa: &Int, ra: &Int, m: usize) -> Result<(Int, Int, Int, usize), Error> {

    let b = m*2;

    let (pb, qb, rb) = pqr(m, b)?;

    let r = ra.mul(&rb)?;
    let q = qa.mul(&qb)?;
    let n0 = pa.mul(&qb)?;
    let n1 = pb.mul(ra)?;
    let p = n0.add(&n1)?;

    Ok((p, q, r, b))
}

/// Holds value of currently computed ln(2).
pub struct Pi_cache {
    b: usize,
    pk: Int,
    qk: Int,
    rk: Int,
    val: BigFloatNumber,
}

impl Pi_cache {

    fn calc_pi(p: &Int, q: &Int, k: usize) -> Result<BigFloatNumber, Error>  {

        let n0 = Int::from_word(4270934400)?;
        let n1 = Int::from_word(13591409)?;

        let q0 = q.mul(&n0)?;
        let q1 = q.mul(&n1)?;
        let p0 = p.add(&q1)?;

        let f0 = q0.as_float()?;
        let f1 = p0.as_float()?;

        let f3 = BigFloatNumber::from_word(10005, k)?;
        let f4 = f3.sqrt(RoundingMode::None)?;
        let f5 = f1.mul(&f4, RoundingMode::None)?;

        println!("{:?}\n{:?}\n{:?}", f0, f1, f4);

        f0.div(&f5, RoundingMode::None)
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

        let kext = k + 20;

        if self.pk.bit_len() < kext && self.qk.bit_len() < kext {

            let mut pk;
            let mut qk;
            let mut rk;
            let mut bb;

            (pk, qk, rk, bb) = pqr_inc(&self.pk, &self.qk, &self.rk, self.b)?;

            while pk.bit_len() < kext || qk.bit_len() < kext {

                (pk, qk, rk, bb) = pqr_inc(&pk, &qk, &rk, bb)?;
            }

            let mut ret = Self::calc_pi(&pk, &pk, k)?;

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
    use crate::{RoundingMode, defs::Radix};

    use super::*;


    #[test]
    fn test_pi_const() {
        let mut pi = Pi_cache::new().unwrap();
        let c = pi.for_prec(64, RoundingMode::ToEven).unwrap();
        println!("{:?}", c.fp3(Radix::Dec, RoundingMode::None))
    }
}