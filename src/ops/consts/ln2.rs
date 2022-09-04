//! ln(2)

use crate::RoundingMode;
use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::common::int::Int;
use crate::defs::Error;
use crate::num::BigFloatNumber;


fn p(a: usize, b: usize) -> Result<Int, Error> {

    if a == b - 1 {

        Int::from_word(1)

    } else {

        let m = (a + b) / 2;

        let pa = p(a, m)?;
        let qb = q(m, b)?;
        let pb = p(m, b)?;
        let ra = r(a,m)?;

        let pq = pa.mul(&qb)?;
        let pr = pb.mul(&ra)?;

        pq.add(&pr)
    }
}

fn q(a: usize, b: usize) -> Result<Int, Error> {

    if a == b - 1 {

        Int::from_usize((2*b + 1)*9)

    } else {

        let m = (a + b) / 2;

        let qa = q(a, m)?;
        let qb = q(m, b)?;

        qa.mul(&qb)
    }
}

fn r(a: usize, b: usize) -> Result<Int, Error> {

    if a == b-1 {

        Int::from_usize(2*b + 1)

    } else {

        let m = (a + b) / 2;

        let ra = r(a, m)?;
        let rb = r(m, b)?;

        ra.mul(&rb)
    }
}

fn pqr_inc(pa: &Int, qa: &Int, ra: &Int, m: usize) -> Result<(Int, Int, Int, usize), Error> {

    let b = m*2;

    let qb = q(m, b)?;
    let pb = p(m, b)?;
    let rb = r(m, b)?;

    let pq = pa.mul(&qb)?;
    let pr = pb.mul(ra)?;

    let p_ret = pq.add(&pr)?;
    let q_ret = qa.mul(&qb)?;
    let r_ret = ra.mul(&rb)?;

    Ok((p_ret, q_ret, r_ret, b))
}

/// Holds value of currently computed ln(2).
pub struct Ln2_cache {
    b: usize,
    pk: Int,
    qk: Int,
    rk: Int,
    val: BigFloatNumber,
}

impl Ln2_cache {

    pub fn new() -> Result<Self, Error> {

        let p01 = p(0, 1)?;
        let q01 = q(0, 1)?;
        let r01 = r(0, 1)?;

        let f0 = p01.as_float()?;
        let f1 = q01.as_float()?;

        // 2 * (1 + p / q) / 3
        let mut val = f0.div(&f1, crate::RoundingMode::None)?;
        val = val.add(&ONE, crate::RoundingMode::None)?;
        val = val.div(&THREE, crate::RoundingMode::None)?;
        val.set_exponent(val.get_exponent() + 1);

        Ok(Ln2_cache {
            b: 1,
            pk: p01,
            qk: q01,
            rk: r01,
            val,
        })
    }

    /// Return value of ln(2) with precision k.
    pub fn for_prec(&mut self, k: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {

        let kext = k + 5;

        if self.pk.bit_len() < kext && self.qk.bit_len() < kext {

            let mut pk;
            let mut qk;
            let mut rk;
            let mut bb;

            (pk, qk, rk, bb) = pqr_inc(&self.pk, &self.qk, &self.rk, self.b)?;

            while pk.bit_len() < kext || qk.bit_len() < kext {

                (pk, qk, rk, bb) = pqr_inc(&pk, &qk, &rk, bb)?;
            }

            let f0 = pk.as_float()?;
            let f1 = qk.as_float()?;

            // 2 * (1 + p / q) / 3
            let mut ret = f0.div(&f1, crate::RoundingMode::None)?;
            ret = ret.add(&ONE, crate::RoundingMode::None)?;
            ret = ret.div(&THREE, crate::RoundingMode::None)?;
            ret.set_exponent(ret.get_exponent() + 1);

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

    use super::Ln2_cache;

    #[test]
    fn test_ln2_const() {
        let mut ln2 = Ln2_cache::new().unwrap();
        let c = ln2.for_prec(128, RoundingMode::ToEven).unwrap();
        println!("{:?}", c.fp3(Radix::Dec, RoundingMode::None))
    }
}