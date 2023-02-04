//! ln(2)

use crate::common::consts::ONE;
use crate::common::consts::THREE;
use crate::common::util::round_p;
use crate::defs::Error;
use crate::num::BigFloatNumber;
use crate::RoundingMode;
use crate::WORD_BIT_SIZE;

fn pqr(a: usize, b: usize) -> Result<(BigFloatNumber, BigFloatNumber, BigFloatNumber), Error> {
    if a == b - 1 {
        let p = BigFloatNumber::from_word(1, 1)?;
        let q = BigFloatNumber::from_usize((2 * b + 1) * 9)?;
        let r = BigFloatNumber::from_usize(2 * b + 1)?;

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

/// Holds value of currently computed ln(2).
#[derive(Debug)]
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
        let prec = p01.mantissa_max_bit_len().max(q01.mantissa_max_bit_len());
        let mut val = p01.div(&q01, prec, crate::RoundingMode::None)?;
        val = val.add(&ONE, prec, crate::RoundingMode::None)?;
        val = val.div(&THREE, prec, crate::RoundingMode::None)?;
        val.set_exponent(val.exponent() + 1);

        Ok(Ln2Cache {
            b: 1,
            pk: p01,
            qk: q01,
            rk: r01,
            val,
        })
    }

    /// Return value of ln(2) with precision k (calculate if needed).
    pub(crate) fn for_prec(&mut self, k: usize, rm: RoundingMode) -> Result<BigFloatNumber, Error> {
        let mut p_inc = WORD_BIT_SIZE;
        let mut p_wrk = round_p(k) + p_inc;

        loop {
            let kext = k / 2 + 4;

            if self.b > kext {
                let mut ret = self.val.clone()?;

                if ret.try_set_precision(k, rm, p_wrk)? {
                    return Ok(ret);
                }

                p_wrk += p_inc;
                p_inc = round_p(p_wrk / 5);
            }

            let mut pk;
            let mut qk;
            let mut rk;
            let mut bb;

            (pk, qk, rk, bb) = pqr_inc(&self.pk, &self.qk, &self.rk, self.b)?;

            while bb <= kext {
                (pk, qk, rk, bb) = pqr_inc(&pk, &qk, &rk, bb)?;
            }

            // 2 * (1 + p / q) / 3
            let prec = pk.mantissa_max_bit_len().max(qk.mantissa_max_bit_len());
            let mut ret = pk.div(&qk, prec, crate::RoundingMode::None)?;
            ret = ret.add(&ONE, prec, crate::RoundingMode::None)?;
            ret = ret.div(&THREE, prec, crate::RoundingMode::None)?;
            ret.set_exponent(ret.exponent() + 1);

            self.val = ret;

            self.pk = pk;
            self.qk = qk;
            self.rk = rk;
            self.b = bb;
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::{RoundingMode, Sign};

    use super::*;

    #[test]
    #[cfg(target_arch = "x86")]
    fn test_ln2_const() {
        let mut ln2 = Ln2Cache::new().unwrap();
        let c = ln2.for_prec(3200, RoundingMode::ToEven).unwrap();
        //println!("{:?}", c);
        let r = BigFloatNumber::from_raw_parts(
            &[
                3303612541, 717600284, 3199892741, 1462999970, 137959948, 6349977, 1794441986,
                1645437721, 1024185081, 96544981, 3471345337, 920660768, 4091103730, 196810490,
                3381928201, 1109492717, 2355549125, 1586635448, 1797039055, 1638923588, 2503522690,
                646601759, 4224649045, 2372882807, 579489529, 2708640721, 1931271310, 1151346004,
                816810139, 2530535123, 2409011252, 1433450182, 451048430, 1972937109, 3009774909,
                1293299123, 1348780427, 1599124760, 455979803, 126841693, 1818258609, 2922462427,
                2984344477, 2505920889, 389352748, 206047828, 1560181411, 122533377, 1578405506,
                1788641162, 895787831, 627481395, 3520465245, 1276780043, 2475905356, 3435941477,
                3027881267, 3376670514, 3683225829, 390465397, 335590294, 2100175838, 4229888533,
                3998653805, 2414170530, 1628254456, 4217109392, 133483025, 255841734, 3660421061,
                790684578, 1700766087, 942682696, 4125075133, 2640660682, 1926137777, 1985476427,
                628072684, 2973130811, 3119160259, 830224510, 449567249, 575334597, 1050069526,
                292141093, 660028201, 3241681220, 3979259445, 1257904912, 1435849467, 1844161688,
                3887625760, 2343238187, 2316113755, 1922610733, 1089684262, 66254511, 3387143064,
                3520035243, 2977044471,
            ],
            3200,
            Sign::Pos,
            0,
        )
        .unwrap();
        assert!(c.cmp(&r) == 0);
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    fn test_ln2_const() {
        let mut ln2 = Ln2Cache::new().unwrap();
        let c = ln2.for_prec(3200, RoundingMode::ToEven).unwrap();
        //println!("{:?}", c);
        let r = BigFloatNumber::from_raw_parts(
            &[
                3082069754683924605,
                6283537028398873861,
                27272943683312140,
                7067101201094214402,
                414657537012126457,
                3954207892741588665,
                845294622150838770,
                4765234938047111433,
                6814547362189857733,
                7039123212900017103,
                2777133410944596354,
                10191454057530328917,
                11633523313888349945,
                4944993435491556494,
                10868565595481147547,
                6156621654544259124,
                8473700360670835694,
                5554677440240256317,
                6868188547772629387,
                544780923660251931,
                12551880549572046001,
                10762848267602590621,
                884968683061185836,
                526276848443620003,
                7682155296647843458,
                2695012071269245751,
                5483728532390938973,
                14757256277160841548,
                14502689430025391411,
                1677036114017882341,
                9020186540394984342,
                17174087324730849813,
                6993299640500441506,
                573305231163259792,
                15721388746840462790,
                7304734722601575330,
                17717062790720533064,
                8272698762445801674,
                2697551639276418891,
                13396691306361020475,
                1930876632637913214,
                4510014273271556293,
                2834799538024855589,
                17090789181815791940,
                6166926504001936144,
                16697225500131306648,
                9947632833883994667,
                4680158270178506285,
                14547668686819489455,
                12786308645202655659,
            ],
            3200,
            Sign::Pos,
            0,
        )
        .unwrap();
        assert!(c.cmp(&r) == 0);
    }
}
