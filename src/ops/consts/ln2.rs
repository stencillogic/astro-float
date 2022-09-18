//! ln(2)

use crate::RoundingMode;
use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::defs::Error;
use crate::num::BigFloatNumber;


fn pqr(a: usize, b: usize) -> Result<(BigFloatNumber, BigFloatNumber, BigFloatNumber), Error> {

    if a == b - 1 {

        let p = BigFloatNumber::from_word(1, 1)?;
        let q = BigFloatNumber::from_usize((2*b + 1)*9)?;
        let r = BigFloatNumber::from_usize(2*b + 1)?;

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

fn pqr_inc(pa: &BigFloatNumber, qa: &BigFloatNumber, ra: &BigFloatNumber, m: usize) -> Result<(BigFloatNumber, BigFloatNumber, BigFloatNumber, usize), Error> {

    let b = m*2;

    let (pb, qb, rb) = pqr(m, b)?;

    let pq = pa.mul_full_prec(&qb)?;
    let pr = pb.mul_full_prec(ra)?;

    let p_ret = pq.add_full_prec(&pr)?;
    let q_ret = qa.mul_full_prec(&qb)?;
    let r_ret = ra.mul_full_prec(&rb)?;

    Ok((p_ret, q_ret, r_ret, b))
}

/// Holds value of currently computed ln(2).
pub struct Ln2Cache {
    b: usize,
    pk: BigFloatNumber,
    qk: BigFloatNumber,
    rk: BigFloatNumber,
    val: BigFloatNumber,
}

impl Ln2Cache {

    pub fn new() -> Result<Self, Error> {

        let (p01, q01, r01) = pqr(0, 1)?;

        // 2 * (1 + p / q) / 3
        let mut val = p01.div(&q01, crate::RoundingMode::None)?;
        val = val.add(&ONE, crate::RoundingMode::None)?;
        val = val.div(&THREE, crate::RoundingMode::None)?;
        val.set_exponent(val.get_exponent() + 1);

        Ok(Ln2Cache {
            b: 1,
            pk: p01,
            qk: q01,
            rk: r01,
            val,
        })
    }

    /// Try to get cached value without additional calculations.
    pub fn try_for_prec(&self, k: usize, rm: RoundingMode) -> Result<Option<BigFloatNumber>, Error> {

        let kext = k / 2 + 4;

        if self.b > kext {

            let mut ret = self.val.clone()?;

            ret.set_precision(k, rm)?;

            Ok(Some(ret))

        } else {
            
            Ok(None)
        }
    }

    /// Return value of ln(2) with precision k (calculate if needed).
    pub fn for_prec(&mut self, k: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {

        let kext = k / 2 + 4;

        if self.b <= kext {

            let mut pk;
            let mut qk;
            let mut rk;
            let mut bb;

            (pk, qk, rk, bb) = pqr_inc(&self.pk, &self.qk, &self.rk, self.b)?;

            while bb <= kext {

                (pk, qk, rk, bb) = pqr_inc(&pk, &qk, &rk, bb)?;
            }

            // 2 * (1 + p / q) / 3
            let mut ret = pk.div(&qk, crate::RoundingMode::None)?;
            ret = ret.add(&ONE, crate::RoundingMode::None)?;
            ret = ret.div(&THREE, crate::RoundingMode::None)?;
            ret.set_exponent(ret.get_exponent() + 1);

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

    use crate::{RoundingMode, Sign};

    use super::*;

    #[test]
    fn test_ln2_const() {
        let mut ln2 = Ln2Cache::new().unwrap();
        let c = ln2.for_prec(3200, RoundingMode::ToEven).unwrap();
        let r = BigFloatNumber::from_raw_parts(&[3303612541, 717600284, 3199892741, 1462999970, 137959948, 6349977, 1794441986, 1645437721, 1024185081, 96544981, 3471345337, 920660768, 4091103730, 196810490, 3381928201, 1109492717, 2355549125, 1586635448, 1797039055, 1638923588, 2503522690, 646601759, 4224649045, 2372882807, 579489529, 2708640721, 1931271310, 1151346004, 816810139, 2530535123, 2409011252, 1433450182, 451048430, 1972937109, 3009774909, 1293299123, 1348780427, 1599124760, 455979803, 126841693, 1818258609, 2922462427, 2984344477, 2505920889, 389352748, 206047828, 1560181411, 122533377, 1578405506, 1788641162, 895787831, 627481395, 3520465245, 1276780043, 2475905356, 3435941477, 3027881267, 3376670514, 3683225829, 390465397, 335590294, 2100175838, 4229888533, 3998653805, 2414170530, 1628254456, 4217109392, 133483025, 255841734, 3660421061, 790684578, 1700766087, 942682696, 4125075133, 2640660682, 1926137777, 1985476427, 628072684, 2973130811, 3119160259, 830224510, 449567249, 575334597, 1050069526, 292141093, 660028201, 3241681220, 3979259445, 1257904912, 1435849467, 1844161688, 3887625760, 2343238187, 2316113755, 1922610733, 1089684262, 66254511, 3387143064, 3520035243, 2977044471], 3200, Sign::Pos, 0).unwrap();
        assert!(c.cmp(&r) == 0);
    }
}